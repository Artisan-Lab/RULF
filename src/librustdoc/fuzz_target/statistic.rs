use lazy_static::lazy_static;
use once_cell::sync::Lazy;
use rustc_data_structures::fx::FxHashMap;
use std::sync::Mutex;

pub static mut STATISTIC_MAP: Lazy<Mutex<FxHashMap<String, usize>>> = Lazy::new(|| {
    let mut map = FxHashMap::<String, usize>::default();
    map.insert("API".to_string(), 0);
    map.insert("GENERIC_API".to_string(), 0);
    map.insert("TRAIT_IMPLS".to_string(), 0);
    map.insert("BLANKET_IMPLS".to_string(), 0);
    map.insert("COVERED GENERIC".to_string(), 0);
    map.insert("COVERED API".to_string(),0);
    map.insert("MONO_FUNS".to_string(), 0);
    map.insert("ITERS".to_string(), 0);
    map.insert("CANDIDATES".to_string(), 0);
    map.insert("UNSOLVABLE".to_string(), 0);
    map.insert("RESERVE".to_string(), 0);
    map.insert("PRUNE_ITERS".to_string(), 0);
    map.insert("UNSAFE".to_string(), 0);
    map.insert("RPG_GENERIC".to_string(), 0);
    map.insert("RPG_API".to_string(), 0);
    map.insert("RPG_COVERED_GENERIC".to_string(), 0);
    map.insert("RPG_COVERED_API".to_string(), 0);
    map.into()
});

pub fn add(key: &str, val: usize) {
    unsafe {
        if let Some(value) = STATISTIC_MAP.lock().unwrap().get_mut(key) {
            *value += val;
        } else {
            panic!("invalid statistic field");
        }
    }
}

pub fn inc(key: &str) {
    unsafe {
        if let Some(value) = STATISTIC_MAP.lock().unwrap().get_mut(key) {
            *value += 1;
        } else {
            panic!("invalid statistic field");
        }
    }
}
pub fn print_summary() {
    unsafe {
        println!("====== statistic ======");
        for (key, value) in STATISTIC_MAP.lock().unwrap().iter() {
            println!("{}: {}", key, value);
        }
        println!("======  advance  ======");
        let mono_funs = *STATISTIC_MAP.lock().unwrap().get("MONO_FUNS").unwrap();
        let num_covered_generic = *STATISTIC_MAP.lock().unwrap().get("COVERED GENERIC").unwrap();
        let num_api = *STATISTIC_MAP.lock().unwrap().get("API").unwrap();
        let num_generic = *STATISTIC_MAP.lock().unwrap().get("GENERIC_API").unwrap();
        let num_covered_api = *STATISTIC_MAP.lock().unwrap().get("COVERED API").unwrap();
        println!("MONO_PER_FUNCS: {}", mono_funs as f32 / num_covered_generic as f32);
        println!("GENERIC COVERAGE: {}", num_covered_generic as f32 / num_generic as f32);
        println!("API COVERAGE: {}", num_covered_api as f32 / num_api as f32);

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
