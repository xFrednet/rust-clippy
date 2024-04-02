struct A {
    field: String,
}

impl A {
    fn borrow_self(&self) -> &A {
        self
    }

    #[warn(clippy::borrow_pats)]
    fn borrow_field_direct(&self) -> &String {
        &self.field
    }

    fn borrow_field_deref(&self) -> &str {
        &self.field
    }

    fn borrow_field_or_default(&self) -> &str {
        if self.field.is_empty() {
            "Here be defaults"
        } else {
            &self.field
        }
    }
}

fn main() {}
