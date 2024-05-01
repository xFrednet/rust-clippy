//@rustc-env: CLIPPY_PETS_TEST_RELATIONS=1
//@rustc-env: CLIPPY_PETS_PRINT=1

#[warn(clippy::borrow_pats)]
fn use_local_func() {
    let func = take_string_ref;

    func(&String::new());
}

#[warn(clippy::borrow_pats)]
fn use_arg_func(func: fn(&String) -> &str) {
    func(&String::new());
}

#[warn(clippy::borrow_pats)]
fn borrow_as_generic(s: String) {
    let _tee = pass_t(&s);
    // let _len = tee.len();
}

fn take_string(_s: String) {}
fn take_string_ref(_s: &String) {}
fn pass_t<T>(tee: T) -> T {
    tee
}

fn main() {}
