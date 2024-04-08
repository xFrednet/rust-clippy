struct A {
    field: String,
}

struct Magic<'a> {
    a: &'a String,
}

impl A {
    #[warn(clippy::borrow_pats)]
    fn borrow_self(&self) -> &A {
        self
    }

    #[warn(clippy::borrow_pats)]
    fn borrow_field_direct(&self) -> &String {
        &self.field
    }

    #[warn(clippy::borrow_pats)]
    fn borrow_field_deref(&self) -> &str {
        &self.field
    }

    #[forbid(clippy::borrow_pats)]
    fn borrow_field_or_default(&self) -> &str {
        if self.field.is_empty() {
            "Here be defaults"
        } else {
            &self.field
        }
    }

    fn borrow_field_into_mut_arg<'a>(&'a self, magic: &mut Magic<'a>) {
        magic.a = &self.field;
    }
}

fn main() {}
