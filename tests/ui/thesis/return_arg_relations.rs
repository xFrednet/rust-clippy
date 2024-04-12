//! A file to test dependencies between function parameters

fn no_rep(_: u32, _: String) -> u16 {
    12
}

fn direct_dep(a: &String, _: u32) -> &String {
    a
}

fn lifetime_dep<'a>(_: &String, a: &'a String) -> &'a String {
    a
}

fn lifetime_dep_more<'a>(_: &'a String, a: &'a String) -> &'a String {
    a
}

fn lifetime_dep_const<'a>(_: &'a str, a: &'a str) -> &'a str {
    a
}

fn lifetime_dep_prim<'a>(_: &'a u32, a: &'a u32) -> &'a u32 {
    a
}

fn lifetime_outlives<'a, 'b: 'a, 'c: 'a>(b: &'b String, _c: &'c String) -> &'a String {
    b
}

#[forbid(clippy::borrow_pats)]
fn test(s1: String, s2: String, s3: String, pair: (String, String)) {
    let _test = no_rep(1, s3);
    let _test = direct_dep(&s1, 2);
    let _test = lifetime_dep(&s1, &s2);
    let _test = lifetime_dep_more(&s1, &s2);
    let _test = lifetime_dep_prim(&1, &2);
    let _test = lifetime_dep_const("In", "Put");
    let _test = lifetime_outlives(&s1, &s2);
    let _test = lifetime_outlives(&pair.0, &pair.1);
}

fn main() {}
