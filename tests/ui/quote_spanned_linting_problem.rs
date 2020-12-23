#[macro_use]
extern crate clippy_mini_macro_test as mini_mac;

fn main() {
    // This triggers the `clippy::suspicious-else-formatting` lint
    mini_mac::spans_are_fun!(true);
    // Story: Most of our lints check if an expression is the result of a macro expedition to avoid
    // reports in code that the user hasn't written. So far so good.
    // The problem arises from the `quote::quote_spanned!` macro that enables users to set the span
    // property of tokens. This macro right here set's the generated statement spans to the span of
    // the true statement. This is nice for some error reporting but problematic in our case because
    // it makes it impossible to determine if the linted code originates from a macro (like in this
    // case) or by the user
}