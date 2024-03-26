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

fn print_mir(owned: String, cond: bool) -> u32 {
    if cond {
        return 16;
    }

    let _b = String::new();
    18
}

fn simple_ownership(owned: String) {
    owned.len();
}

fn if_fun(a: String, b: String, cond: bool) {
    if cond {
        magic_1(&a);
    } else {
        magic_1(&b);
    }

    magic_1(if cond {&a} else {&b});
}



fn main() {}
