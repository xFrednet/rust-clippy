#![warn(unused)]

use crate::borrow_pats::MyStateInfo;

use super::super::prelude::*;
use super::OwnedPat;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct StateInfo<'tcx> {
    pub state: State,
    /// This is a set of values that *might* contain the owned value.
    /// MIR has this *beautiful* habit of moving stuff into anonymous
    /// locals first before using it further.
    pub anons: FxHashSet<Local>,
    /// This set contains borrows, these are often used for temporary
    /// borrows
    ///
    /// **Note 1**: Named borrows can be created in two ways (Because of course
    /// they can...)
    /// ```
    /// // From: `mut_named_ref_non_kill`
    /// //    let mut x = 1;
    /// //    let mut p: &u32 = &x;
    /// _4 = &_1
    /// _3 = &(*_4)
    ///
    /// // From: `call_extend_named`
    /// //    let data = String::new();
    /// //    let loan = &data;
    /// _2 = &_3
    /// ```
    ///
    /// **Note 2**: Correction there are three ways to created named borrows...
    /// Not sure why but let's take `mut_named_ref_non_kill` as and example for `y`
    ///
    /// ```
    /// // y     => _2
    /// // named => _3
    /// _8 = &_2
    /// _7 = &(*_8)
    /// _3 = move _7
    /// ```
    ///
    /// **Note 3**: If I can confirm that these borrows are always used for
    /// temporary borrows, it might be possible to prevent tracking them
    /// to safe some performance. (Confirmed, that they are not just
    /// used for temp borrows :D)
    borrows: FxHashMap<Local, (Place<'tcx>, Mutability, BroKind)>,
    /// This tracks mut borrows, which might be used for two phased borrows.
    /// Based on the docs, it sounds like there can always only be one. Let's
    /// use an option and cry when it fails.
    ///
    /// See: https://rustc-dev-guide.rust-lang.org/borrow_check/two_phase_borrows.html
    phase_borrow: Vec<(Local, Place<'tcx>)>,
}

#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd, Default)]
pub enum State {
    #[default]
    None,
    Empty,
    Filled,
    Moved,
    Dropped,
    MaybeFilled,
}

#[expect(unused)]
enum Event<'tcx> {
    Init,
    Loan,
    Mutated,
    // Moved or Dropped
    Moved(Place<'tcx>),
    Drop,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub enum BroKind {
    Anon,
    Named,
    Dep,
}

impl<'tcx> StateInfo<'tcx> {
    /// Retruns true if this state contains valid data, which can be dropped or moved.
    pub fn validity(&self) -> Validity {
        match self.state {
            State::None => unreachable!(),
            State::Filled => Validity::Valid,
            State::MaybeFilled => Validity::Maybe,
            State::Empty | State::Moved | State::Dropped => Validity::Not,
        }
    }

    /// Notifies the state that a local has been killed
    pub fn kill_local(&mut self, local: Local) {
        self.anons.remove(&local);
        self.borrows.remove(&local);
        self.phase_borrow.retain(|(phase_local, _place)| *phase_local != local);
    }

    /// This tries to remove the given place from the known anons that hold this value.
    /// It will retrun `true`, if the removal was successfull.
    /// Places with projections will be ignored.
    pub fn remove_anon(&mut self, anon: &Place<'_>) -> bool {
        let found = self.remove_anon_place(anon);
        assert!(!found || anon.just_local(), "{self:#?} - {anon:#?}");
        found
    }

    pub fn remove_anon_place(&mut self, anon: &Place<'_>) -> bool {
        self.anons.remove(&anon.local)
    }

    /// This clears this state. The `state` field has to be set afterwards
    pub fn clear(&mut self) {
        self.anons.clear();
        self.borrows.clear();
        self.phase_borrow.clear();

        self.state = State::None;
    }

    pub fn add_borrow(
        &mut self,
        borrow: Place<'tcx>,
        broker: Place<'tcx>,
        kind: BorrowKind,
        bro_kind: Option<BroKind>,
        info: &AnalysisInfo<'tcx>,
        pats: &mut BTreeSet<OwnedPat>,
    ) {
        self.update_bros(broker, kind.mutability(), info);

        if matches!(kind, BorrowKind::Shared)
            && self
                .phase_borrow
                .iter()
                .any(|(_loc, phase_place)| info.places_conflict(*phase_place, broker))
        {
            pats.insert(OwnedPat::TwoPhasedBorrow);
            info.stats.borrow_mut().owned.two_phased_borrows += 1;
        }
        
        let is_named = matches!(info.locals[&borrow.local].kind, LocalKind::UserVar(..));
        if is_named {
            if matches!(kind, BorrowKind::Shared) {
                info.stats.borrow_mut().owned.named_borrow_count += 1;
                pats.insert(OwnedPat::NamedBorrow);
            } else {
                info.stats.borrow_mut().owned.named_borrow_mut_count += 1;
                pats.insert(OwnedPat::NamedBorrowMut);
            }
        }

        let bro_kind = if let Some(bro_kind) = bro_kind {
            bro_kind
        } else if is_named {
            BroKind::Named
        } else {
            BroKind::Anon
        };

        // So: It turns out that MIR is an inconsisten hot mess. Two-Phase-Borrows are apparently
        // allowed to violate rust borrow semantics...
        //
        // Simple example: `x.push(x.len())`
        if !is_named {
            assert!(borrow.just_local());
            if kind.allows_two_phase_borrow() {
                self.phase_borrow.push((borrow.local, broker));
            } else {
                self.borrows.insert(borrow.local, (broker, kind.mutability(), bro_kind));
            }
        } else {
            // Mut loans can also be used for two-phased-borrows, but only with themselfs.
            // Taking the mut loan and the owned value failes.
            //
            // ```
            // fn test(mut vec: Vec<usize>) {
            //     let loan = &mut vec;
            //     loan.push(vec.len());
            // }
            // ```
            //
            // The two-phased-borrow will be detected by the owned reference. So we can
            // ignore it here :D
            self.borrows.insert(borrow.local, (broker, kind.mutability(), bro_kind));
            // todo!("Named Local: {borrow:#?} = {broker:#?}\n{self:#?}");
        }
    }

    /// This function informs the state, that a local loan was just copied.
    pub fn add_ref_copy(
        &mut self,
        dst: Place<'tcx>,
        src: Place<'tcx>,
        _copy_kind: Option<BorrowKind>,
        info: &AnalysisInfo<'tcx>,
        pats: &mut BTreeSet<OwnedPat>,
    ) {
        // This function has to share quite some magic with `add_borrow` but
        // again is different enough that they can't be merged directly AFAIK

        let Some((broker, muta, bro_kind)) = self.borrows.get(&src.local).copied() else {
            return;
        };

        // It looks like loans preserve the mutability of th copy. This is perfectly
        // inconsitent. Maybe the previous `&mut (*_2)` came from a different
        // MIR version. At this point there is no value in even checking.
        //
        // Looking at `temp_borrow_mixed_2` it seems like the copy mutability depends
        // on the use case. I'm not even disappointed anymore
        let new_muta = muta;
        match bro_kind {
            BroKind::Dep | BroKind::Named => {
                // FIXME: Maybe this doesn't even needs to be tracked?
                self.borrows.insert(dst.local, (broker, new_muta, BroKind::Dep));
            },
            // Only anons should be able to add new information
            BroKind::Anon => {
                let is_named = matches!(info.locals[&dst.local].kind, LocalKind::UserVar(..));
                if is_named {
                    if matches!(new_muta, Mutability::Mut) {
                        info.stats.borrow_mut().owned.named_borrow_mut_count += 1;
                        pats.insert(OwnedPat::NamedBorrowMut);
                    } else {
                        info.stats.borrow_mut().owned.named_borrow_count += 1;
                        pats.insert(OwnedPat::NamedBorrow);
                    }
                }

                let new_bro_kind = if is_named { BroKind::Named } else { BroKind::Anon };

                // `copy_kind` can only be mutable if `src` is also mutable
                self.borrows.insert(dst.local, (broker, new_muta, new_bro_kind));
            },
        }
    }

    fn update_bros(&mut self, broker: Place<'tcx>, muta: Mutability, info: &AnalysisInfo<'tcx>) {
        // TODO: Check if this function is even needed with the kill command!!!!

        if broker.just_local() && matches!(muta, Mutability::Mut) {
            // If the entire thing is borrowed mut, every reference get's cleared
            self.borrows.clear();
        } else {
            // I switch on muta before the `retain`, to make the `retain`` specialized and therefore faster.
            match muta {
                // Not mutable aka aliasable
                Mutability::Not => self.borrows.retain(|_key, (broed_place, muta, _bro)| {
                    !(matches!(muta, Mutability::Mut) && info.places_conflict(*broed_place, broker))
                }),
                Mutability::Mut => self
                    .borrows
                    .retain(|_key, (broed_place, _muta, _kind)| !info.places_conflict(*broed_place, broker)),
            }
        }
    }

    pub fn has_bro(&mut self, anon: &Place<'_>) -> Option<(Place<'tcx>, Mutability, BroKind)> {
        if let Some((_loc, place)) = self.phase_borrow.iter().find(|(local, _place)| *local == anon.local) {
            // TwoPhaseBorrows are always mutable
            Some((*place, Mutability::Mut, BroKind::Anon))
        } else {
            self.borrows.get(&anon.local).copied()
        }
    }

    pub fn add_assign(&mut self, _bb: BasicBlock) {
        self.state = State::Filled;
    }
}

impl<'a, 'tcx> MyStateInfo<super::OwnedAnalysis<'a, 'tcx>> for StateInfo<'tcx> {
    fn join(&mut self, state_owner: &mut super::OwnedAnalysis<'a, 'tcx>, bb: BasicBlock) -> bool {
        let other = &state_owner.states[bb];
        let mut changed = false;

        assert_ne!(other.state, State::None);
        if self.state == State::None {
            *self = other.clone();
            return true;
        }

        let new_state = match (self.validity(), other.validity()) {
            (Validity::Valid, Validity::Valid) => State::Filled,
            (Validity::Not, Validity::Not) => State::Empty,
            (_, _) => State::MaybeFilled,
        };
        changed |= self.state != new_state;
        self.state = new_state;

        // FIXME: Here we can have collisions where two anons reference different places... oh no...
        let anons_previous_len = self.anons.len();
        let anon_bros_previous_len = self.borrows.len();
        self.anons.extend(other.anons.iter());
        self.borrows.extend(other.borrows.iter());
        changed |= (self.anons.len() != anons_previous_len) || (self.borrows.len() != anon_bros_previous_len);

        {
            let phase_borrow_len = self.phase_borrow.len();
            self.phase_borrow.extend(other.phase_borrow.iter());
            changed |= self.phase_borrow.len() != phase_borrow_len;
        }

        // if let Some(bb_a) = self.assignments.last().copied()
        //     && let Some(bb_b) = other.assignments.last().copied()
        //     && bb_a != bb_b
        // {
        //     match (self.assignments.contains(&bb_b), other.assignments.contains(&bb_a)) {
        //         (true, true) => todo!("Loop="),
        //         (true, false) | (false, true) => todo!(),
        //         (false, false) => todo!(),
        //     }

        //     changed = true;
        // }

        changed
    }
}
