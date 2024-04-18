//@rustc-env: CLIPPY_PETS_PRINT=1

struct Animal {
    science_name: String,
    simple_name: String,
}

#[warn(clippy::borrow_pats)]
fn temp_borrow_1(a: String) -> bool {
    a.is_empty()
}

#[warn(clippy::borrow_pats)]
fn temp_borrow_2(a: String) {
    take_1_loan(&a);
}

#[warn(clippy::borrow_pats)]
fn temp_borrow_mut_1(mut a: String) {
    a.clear();
}

// #[warn(clippy::borrow_pats)]
fn temp_borrow_mut_2(mut a: String) {
    take_1_mut_loan(&mut a);
}

fn temp_borrow_mut_3(mut a: Animal) {
    take_2_mut_loan(&mut a.science_name, &mut a.simple_name);
}

// #[warn(clippy::borrow_pats)]
fn temp_borrow_mixed(mut a: String) {
    take_1_mut_loan(&mut a);
    take_1_loan(&a);
}

fn temp_borrow_mixed_2(mut a: Animal) {
    take_2_mixed_loan(&a.science_name, &mut a.simple_name);
}


fn take_1_loan(_: &String) {}
fn take_1_mut_loan(_: &String) {}
fn take_2_mut_loan(_: &mut String, _: &mut String) {}
fn take_2_mixed_loan(_: &String, _: &mut String) {}

fn main() {}
