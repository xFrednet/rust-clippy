//@rustc-env: CLIPPY_PETS_PRINT=1

fn extend_string(data: &String) -> &String {
    data
}

#[forbid(clippy::borrow_pats)]
fn call_extend_simple() {
    let data = String::new();

    extend_string(&data).is_empty();
}

fn main() {}
