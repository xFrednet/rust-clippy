//@rustc-env: CLIPPY_PETS_PRINT=1

struct Animal {
    legs: u32,
    heads: u32,
}

// Check arguments are correctly detected
#[warn(clippy::borrow_pats)]
fn take_one(_animal: Animal) {}

#[warn(clippy::borrow_pats)]
fn take_two(_animal_1: Animal, _animal_2: Animal) {}

fn take_pair((_animal_1, _animal_2): (Animal, Animal)) {}

#[warn(clippy::borrow_pats)]
fn pat_return_owned_arg(animal: Animal) -> Animal {
    animal
}

#[warn(clippy::borrow_pats)]
fn pat_maybe_return_owned_arg_1(a: String) -> String {
    if !a.is_empty() {
        return a;
    }

    "hey".to_string()
}

#[warn(clippy::borrow_pats)]
fn pat_maybe_return_owned_arg_1_test(a: u32) -> u32 {
    if !a.is_power_of_two() {
        return a;
    }

    19
}

#[forbid(clippy::borrow_pats)]
/// FIXME: The argument return is not yet detected both in `a`
fn pat_maybe_return_owned_arg_2(a: String) -> String {
    let ret;
    if !a.is_empty() {
        ret = a;
    } else {
        ret = "hey".to_string();
        println!("{a:#?}");
    }
    ret
}

fn pat_maybe_return_owned_arg_3(a: String) -> String {
    let ret = if !a.is_empty() { a } else { "hey".to_string() };
    ret
}

fn pat_copy_to_self(mut animal: Animal) {
    animal.heads = animal.legs;
}

#[warn(clippy::borrow_pats)]
fn pub_dynamic_drop_1(animal: String, cond: bool) {
    if cond {
        // Move out of function
        std::mem::drop(animal);
    }

    magic()
}

fn magic() {}

fn main() {}