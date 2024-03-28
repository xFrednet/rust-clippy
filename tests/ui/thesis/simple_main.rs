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

fn print_mir() {
    let a = if true {
        let mut x = Vec::new();
        x.push(1);
        x
    } else {
        let mut y = Vec::new();
        y.push(89);
        y
    };
}

fn simple_ownership(mut owned: Vec<i32>) {
    if owned.is_empty() {
        let _a = 17;
    }

    if owned.is_empty() {
        let _b = 89;
    }
}

// fn if_fun(a: String, b: String, cond: bool) {
//     if cond {
//         magic_1(&a);
//     } else {
//         magic_1(&b);
//     }
//
//     magic_1(if cond {&a} else {&b});
// }

fn main() {}
