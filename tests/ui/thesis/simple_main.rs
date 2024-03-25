#![allow(unused)]

struct B<'a>(&'a String);

impl Drop for B<'_> {
    fn drop(&mut self) {}
}

fn maybe_simple() {
    let data = String::new();
    let c = B(&data);
    let b = &c;

    magic_1(b);
    1;
    magic_2(b, b);

    //drop(b);
    //drop(data);
}

fn magic_1(b: &B) {}
fn magic_2(b: &B, c: &B) {}

fn simple_ownership(owned: String) {
    owned.len();
}

fn main() {}
