#![warn(clippy::arithmetic_side_effects)]

use core::ops::Add;

#[derive(Clone, Copy)]
struct Point {
    x: i32,
    y: i32,
}

impl Add for Point {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        todo!()
    }
}

fn main() {
    let _ = Point { x: 1, y: 0 } + Point { x: 2, y: 3 };

    let point: Point = Point { x: 1, y: 0 };
    let _ = point + point;
}
