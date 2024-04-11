struct Animal {
    legs: u32,
    heads: u32,
}

// Check arguments are correctly detected
fn take_one(_animal: Animal) {}

fn take_two(_animal_1: Animal, _animal_2: Animal) {}

fn take_pair((_animal_1, _animal_2): (Animal, Animal)) {}

#[forbid(clippy::borrow_pats)]
fn pat_return_owned_arg(animal: Animal) -> Animal {
    animal
}

fn pat_copy_to_self(mut animal: Animal) {
    animal.heads = animal.legs;
}

fn main() {}
