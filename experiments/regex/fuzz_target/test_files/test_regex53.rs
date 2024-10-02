#[macro_use]
extern crate afl;
extern crate regex;
fn _to_slice<T>(data:&[u8], start_index: usize, end_index: usize)->&[T] {
    let data_slice = &data[start_index..end_index];
    let (_, shorts, _) = unsafe {data_slice.align_to::<T>()};
    shorts
}

use regex::bytes::Replacer;

fn test_function53(mut _param0 :regex::bytes::NoExpand) {
    let _local0_param0_helper1 = &mut (_param0);
    let mut _local0 = <regex::bytes::NoExpand<'_> as regex::bytes::Replacer>::by_ref(_local0_param0_helper1);
    let _local1_param0_helper1 = &mut (_local0);
    let mut _local1: regex::bytes::ReplacerRef<'_, regex::bytes::ReplacerRef<'_, regex::bytes::NoExpand<'_>>> = <regex::bytes::ReplacerRef<'_, regex::bytes::NoExpand<'_>> as regex::bytes::Replacer>::by_ref(_local1_param0_helper1);
    let _local2_param0_helper1 = &mut (_local1);
    let _: regex::bytes::ReplacerRef<'_, regex::bytes::ReplacerRef<'_, regex::bytes::ReplacerRef<'_, regex::bytes::NoExpand<'_>>>> = <regex::bytes::ReplacerRef<'_, regex::bytes::ReplacerRef<'_, regex::bytes::NoExpand<'_>>> as regex::bytes::Replacer>::by_ref(_local2_param0_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() < 1 {return;}
        let dynamic_length = (data.len() - 1) / 1;
        let _param0 = regex::bytes::NoExpand(_to_slice::<u8>(data, 1 + 0 * dynamic_length, data.len()));
        test_function53(_param0);
    });
}
