fn main() {
    let data = 1;

    #[allow(mutable_transmutes)]
    unsafe {
        let a = std::mem::transmute::<&u32, &mut u32>(&data);

        *a = 3;
    }
}
