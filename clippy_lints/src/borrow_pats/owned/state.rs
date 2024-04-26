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
    /// This set contains anonymous borrows, these are AFAIK always used
    /// for temporary borrows.
    ///
    /// Note: If I can confirm that these borrows are always used for
    /// temporary borrows, it might be possible to prevent tracking them
    /// to safe some performance.
    borrows: FxHashMap<Local, (Place<'tcx>, Mutability, BroKind)>,
    /// This tracks mut borrows, which might be used for two phased borrows.
    /// Based on the docs, it sounds like there can always only be one. Let's
    /// use an option and cry when it fails.
    ///
    /// See: https://rustc-dev-guide.rust-lang.org/borrow_check/two_phase_borrows.html
    phase_borrow: Option<(Local, Place<'tcx>)>,
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
        self.phase_borrow.take_if(|(phase_local, _place)| *phase_local == local);
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
        self.phase_borrow = None;

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
            && let Some((_loc, phase_place)) = self.phase_borrow
            && info.places_conflict(phase_place, broker)
        {
            pats.insert(OwnedPat::TwoPhasedBorrow);
            info.stats.borrow_mut().two_phase_borrows += 1;
        }

        let is_named = matches!(info.locals[&borrow.local].kind, LocalKind::UserVar(..));
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
                let old = self.phase_borrow.replace((borrow.local, broker));
                assert_eq!(old, None);
            } else {
                self.borrows.insert(borrow.local, (broker, kind.mutability(), bro_kind));
            }
        } else {
            todo!("Named Local: {borrow:#?} = {broker:#?}\n{self:#?}");
        }
    }

    pub fn has_anon_ref(&self, src: Local) -> bool {
        self.borrows.contains_key(&src)
    }

    /// This function informs the state, that a local loan was just copied.
    pub fn add_ref_copy(&mut self, dst: Local, src: Local) {
        if let Some(data) = self.borrows.get(&src).copied() {
            self.borrows.insert(dst, data);
        }
    }

    fn update_bros(&mut self, broker: Place<'tcx>, muta: Mutability, info: &AnalysisInfo<'tcx>) {
        // TODO: Check if this function is even needed with the kill command.

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
        assert!(anon.just_local());

        if let Some((_loc, place)) = self.phase_borrow.as_ref().filter(|(local, _place)| *local == anon.local) {
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

        assert!(!(self.phase_borrow.is_some() && other.phase_borrow.is_some()));
        if let Some(data) = other.phase_borrow {
            self.phase_borrow = Some(data);
            changed = true;
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
