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

fn loop_1() {
    while !cond_1() {
        while cond_2() {}
    }
}

fn loop_2() {
    let mut idx = 0;
    while idx < 10 {
        idx += 1;
    }
}

#[forbid(clippy::borrow_pats)]
fn loop_3() {
    let mut idx = 0;
    loop {
        idx += 1;
        if idx < 10 {
            break;
        }
        let _x = 1;
    }
    let _y = 0;
}

fn cond_1() -> bool {
    true
}
fn cond_2() -> bool {
    false
}

fn main() {}
