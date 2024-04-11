type DataFlag = u32;

#[derive(Copy, Clone)]
struct DataInfo {
    /// A constant value
    const_val: u16,
    /// A value that is the result of an evaluation, like 1 + 1 or a function
    /// call
    eval_val: u16,
    /// A global value
    global: u16,
    /// An argument
    argument: u16,
}