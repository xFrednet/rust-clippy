#[forbid(clippy::borrow_pats)]
fn if_1() {
    if true {
        let _x = 1;
    }
}

fn if_2() {
    if true {
        let _x = 1;
    } else if false {
        let _y = 1;
    }
}

fn main() {}
