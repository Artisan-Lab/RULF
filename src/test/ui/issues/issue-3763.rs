// compile-flags: -Zsave-analysis
// Also regression test for #69416

mod my_mod {
    pub struct MyStruct {
        priv_field: isize
    }
    pub fn MyStruct () -> MyStruct {
        MyStruct {priv_field: 4}
    }
    impl MyStruct {
        fn happyfun(&self) {}
    }
}

fn main() {
    let my_struct = my_mod::MyStruct();
    let _woohoo = (&my_struct).priv_field;
    //~^ ERROR field `priv_field` of struct `MyStruct` is private

    let _woohoo = (Box::new(my_struct)).priv_field;
    //~^ ERROR field `priv_field` of struct `MyStruct` is private

    (&my_struct).happyfun();               //~ ERROR associated function `happyfun` is private

    (Box::new(my_struct)).happyfun();          //~ ERROR associated function `happyfun` is private
    let nope = my_struct.priv_field;
    //~^ ERROR field `priv_field` of struct `MyStruct` is private
}
