pub static mut FUNCTIONS: usize = 0;
pub static mut GENERIC_FUNCTIONS: usize = 0;
pub static mut TRAIT_IMPLS: usize = 0;
pub static mut BLANKET_IMPLS: usize = 0;
pub static mut DEGENERIC: usize = 0;
pub static mut MONO_FUNS: usize = 0;
pub static mut ITERS:usize =0;

pub fn inc(key: &str) {
    unsafe {
        match key {
            "FUNCTIONS" => {
                FUNCTIONS += 1;
            }
            "GENERIC_FUNCTIONS" => {
                GENERIC_FUNCTIONS += 1;
            }
            "TRAIT_IMPLS" => {
                TRAIT_IMPLS += 1;
            }
            "BLANKET_IMPLS" => {
                BLANKET_IMPLS += 1;
            }
            "DEGENERIC" => {
                DEGENERIC += 1;
            }
            "MONO_FUNS" => {
                MONO_FUNS += 1;
            }
            "ITERS" => {
                ITERS+=1;
            }
            _ => {
                panic!("invalid statistic field");
            }
        }
    }
}
pub fn print_summary() {
    unsafe {
        println!("====== statistic ======");
        println!("functions: {}", FUNCTIONS);
        println!("trait impl: {}", TRAIT_IMPLS);
        println!("blanket impl: {}", BLANKET_IMPLS);
        println!("generic functions: {}", GENERIC_FUNCTIONS);
        println!("degeneric: {}", DEGENERIC);
        println!("MONO_FUNS: {}", MONO_FUNS);
        println!("MONO_PER_FUNCS: {}", MONO_FUNS as f32/DEGENERIC as f32);
        println!("ITERS: {}", ITERS);
        println!("=======================");
    }
}
