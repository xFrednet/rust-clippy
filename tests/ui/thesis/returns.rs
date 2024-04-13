fn simple_const() -> u32 {
    15
}

#[forbid(clippy::borrow_pats)]
fn fn_call() -> u32 {
    simple_const()
}

fn simple_cond() -> u32 {
    if true { 1 } else { 2 }
}

fn static_slice() -> &'static [u32] {
    &[]
}

fn main() {}
