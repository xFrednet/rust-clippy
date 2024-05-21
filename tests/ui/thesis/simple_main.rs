//@rustc-env: CLIPPY_PRINT_MIR=1
// #[forbid(clippy::borrow_pats)]
use std::collections::HashSet;

struct Bar(u32);

struct Foo {
    field_1: Bar,
    field_2: Bar,
}

#[forbid(clippy::borrow_pats)]
fn example(mut var_1: HashSet<usize>) {
    // Example 1
    var_1.insert(var_1.len());
    
}

fn function(_: &mut Bar, _: &mut Bar) {}


fn main() {}
