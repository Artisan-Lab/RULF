use rustc_data_structures::fx::FxHashMap;
use lazy_static::lazy_static;
use once_cell::sync::Lazy;
use std::sync::Mutex;

pub static mut STATISTIC_MAP:Lazy<Mutex<FxHashMap<String,usize>>>=Lazy::new(||{
    let mut map=FxHashMap::<String,usize>::default();
    map.insert("FUNCTIONS".to_string(),0);
    map.insert("GENERIC_FUNCTIONS".to_string(),0);
    map.insert("TRAIT_IMPLS".to_string(),0);
    map.insert("BLANKET_IMPLS".to_string(),0);
    map.insert("DEGENERIC".to_string(),0);
    map.insert("MONO_FUNS".to_string(),0);
    map.insert("ITERS".to_string(),0);
    map.insert("CANDIDATES".to_string(),0);
    map.insert("UNSOLVABLE".to_string(),0);
    map.into()
});


pub fn inc(key: &str) {
    unsafe{
        if let Some(value)=STATISTIC_MAP.lock().unwrap().get_mut(key){
            *value+=1;
        } else {
            panic!("invalid statistic field");
        }
    }
}
pub fn print_summary() {
    unsafe{
        println!("====== statistic ======");
        for (key,value) in STATISTIC_MAP.lock().unwrap().iter(){
            println!("{}: {}",key,value);
        }
        println!("======  advance  ======");
        let mono_funs=*STATISTIC_MAP.lock().unwrap().get("MONO_FUNS").unwrap();
        let degeneric=*STATISTIC_MAP.lock().unwrap().get("DEGENERIC").unwrap();
        println!("MONO_PER_FUNCS: {}", mono_funs as f32/ degeneric as f32);
        println!("=======================");
        
    }

        /* unsafe {
        println!("====== statistic ======");
        println!("functions: {}", FUNCTIONS);
        println!("trait impl: {}", TRAIT_IMPLS);
        println!("blanket impl: {}", BLANKET_IMPLS);
        println!("generic functions: {}", GENERIC_FUNCTIONS);
        println!("degeneric: {}", DEGENERIC);
        println!("MONO_FUNS: {}", MONO_FUNS);
        println!("MONO_PER_FUNCS: {}", MONO_FUNS as f32/DEGENERIC as f32);
        println!("ITERS: {}", ITERS);
        println!("CANDIDATES: {}",CANDIDATES);
        println!("=======================");
    } */
}
