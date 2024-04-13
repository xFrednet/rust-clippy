fn simple_const() -> u32 {
    15
}

fn simple_cond() -> u32 {
    if true { 1 } else { 2 }
}

#[forbid(clippy::borrow_pats)]
fn static_slice() -> &'static [u32] {
    &[]
}

fn main() {}
