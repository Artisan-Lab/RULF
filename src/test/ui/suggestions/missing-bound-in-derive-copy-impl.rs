use std::fmt::Debug;

#[derive(Debug, Copy, Clone)]
pub struct Vector2<T: Debug + Copy + Clone>{
    pub x: T,
    pub y: T
}

#[derive(Debug, Copy, Clone)] //~ ERROR the trait `Copy` may not be implemented for this type
pub struct AABB<K>{
    pub loc: Vector2<K>,
    pub size: Vector2<K>
}

fn main() {}
