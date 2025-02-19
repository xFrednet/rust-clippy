//@aux-build:non-exhaustive-enum.rs
#![allow(
    clippy::manual_unwrap_or_default,
    clippy::manual_unwrap_or,
    clippy::redundant_pattern_matching,
    clippy::no_effect
)]
#![warn(clippy::unneeded_struct_pattern)]

extern crate non_exhaustive_enum;
use non_exhaustive_enum::*;

fn noop() {}

fn main() {
    match Some(114514) {
        Some(v) => v,
        None {} => 0,
        //~^ unneeded_struct_pattern
    };

    match Some(1919810) {
        Some(v) => v,
        None { .. } => 0,
        //~^ unneeded_struct_pattern
    };

    match Some(123456) {
        Some(v) => v,
        None => 0,
    };

    match Some(Some(123456)) {
        Some(Some(v)) => v,
        Some(None {}) => 0,
        //~^ unneeded_struct_pattern
        None {} => 0,
        //~^ unneeded_struct_pattern
    };

    if let None {} = Some(0) {}
    //~^ unneeded_struct_pattern
    if let None { .. } = Some(0) {}
    //~^ unneeded_struct_pattern
    if let Some(None {}) = Some(Some(0)) {}
    //~^ unneeded_struct_pattern
    let None {} = Some(0) else { panic!() };
    //~^ unneeded_struct_pattern
    let None { .. } = Some(0) else { panic!() };
    //~^ unneeded_struct_pattern
    let Some(None {}) = Some(Some(0)) else { panic!() };
    //~^ unneeded_struct_pattern

    enum Custom {
        HasFields {
            field: i32,
        },
        HasBracketsNoFields {},
        NoBrackets,
        #[non_exhaustive]
        NoBracketsNonExhaustive,
        Init,
    };

    match Custom::Init {
        Custom::HasFields { field: value } => value,
        Custom::HasBracketsNoFields {} => 0,
        _ => 0,
    };

    match Custom::Init {
        Custom::HasFields { field: value } => value,
        Custom::HasBracketsNoFields { .. } => 0,
        _ => 0,
    };

    match Custom::Init {
        _ => 0,
    };
    //~^^^ match_single_binding

    match Custom::Init {
        //~^ match_single_binding
        _ => 0,
    };

    if let Custom::HasFields { field: value } = Custom::Init {
        noop();
    }
    if let Custom::HasBracketsNoFields {} = Custom::Init {
        noop();
    }
    if let Custom::HasBracketsNoFields { .. } = Custom::Init {
        noop();
    }
    if let Custom::NoBrackets {} = Custom::Init {
        //~^ unneeded_struct_pattern
        noop();
    }
    if let Custom::NoBrackets { .. } = Custom::Init {
        //~^ unneeded_struct_pattern
        noop();
    }
    if let Custom::NoBrackets {} | Custom::NoBracketsNonExhaustive {} = Custom::Init {
        //~^ unneeded_struct_pattern
        //~| unneeded_struct_pattern
        noop();
    }
    if let Custom::NoBracketsNonExhaustive {} = Custom::Init {
        //~^ unneeded_struct_pattern
        noop();
    }
    if let Custom::NoBracketsNonExhaustive { .. } = Custom::Init {
        //~^ unneeded_struct_pattern
        noop();
    }

    let Custom::HasFields { field: value } = Custom::Init else {
        panic!()
    };

    let Custom::HasBracketsNoFields {} = Custom::Init else {
        panic!()
    };

    let Custom::HasBracketsNoFields { .. } = Custom::Init else {
        panic!()
    };

    let Custom::NoBrackets { .. } = Custom::Init else {
        //~^ unneeded_struct_pattern
        panic!()
    };
    let Custom::NoBracketsNonExhaustive {} = Custom::Init else {
        //~^ unneeded_struct_pattern
        panic!()
    };
    let Custom::NoBracketsNonExhaustive { .. } = Custom::Init else {
        //~^ unneeded_struct_pattern
        panic!()
    };

    enum Refutable {
        Variant,
    }
}

fn external_crate() {
    use ExtNonExhaustiveVariant::*;

    match ExhaustiveUnit {
        // Expected
        ExhaustiveUnit => 0,
        _ => 0,
    };

    match ExhaustiveUnit {
        //~^ match_single_binding
        // Exhaustive variant
        _ => 0,
    };

    match ExhaustiveUnit {
        //~^ match_single_binding
        // Exhaustive variant
        _ => 0,
    };

    match ExhaustiveUnit {
        ExhaustiveUnit => 0,
        // vvvvv Non-exhaustive variants, should all be ignored
        Unit { .. } => 0,
        Tuple { 0: field, .. } => field,
        StructNoField { .. } => 0,
        Struct { field, .. } => field,
        _ => 0,
    };
}
