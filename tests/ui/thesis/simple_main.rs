#![allow(unused)]


fn main() {

    // let owned_1 = String::new();
// 
    // {
    //     let owned_2 = String::new();
    //     let owned_3 = String::new();
// 
    //     drop(owned_2);
    // }

    let owned_4b = {
        let owned_4a = String::new();

        owned_4a
    };
}
