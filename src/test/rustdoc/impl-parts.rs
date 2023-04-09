#![feature(negative_impls)]
#![feature(auto_traits)]

pub auto trait AnAutoTrait {}

pub struct Foo<T> { field: T }

// @has impl_parts/struct.Foo.html '//*[@class="impl has-srclink"]//h3[@class="code-header"]' \
//     "impl<T: Clone> !AnAutoTrait for Foo<T>where T: Sync,"
// @has impl_parts/trait.AnAutoTrait.html '//*[@id="implementors-list"]//h3[@class="code-header"]' \
//     "impl<T: Clone> !AnAutoTrait for Foo<T>where T: Sync,"
impl<T: Clone> !AnAutoTrait for Foo<T> where T: Sync {}
