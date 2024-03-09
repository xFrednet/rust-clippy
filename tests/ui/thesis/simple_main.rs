
#![allow(unused)]

struct B<'a>(&'a String);


fn maybe_simple() {
    let data = String::new();
    let b = B(&data);
    
    magic(&b);
    
    drop(data);
    //magic(&b);
}

fn magic(b: &B) {
    
}

fn simple_ownership(owned: String) {
    let x = &owned;
    x.len();
}

fn main() {
    
}
