#![feature(int_log)]
#![feature(allocator_api)]

#[macro_use]
extern crate afl;
fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}

fn _to_u16(data:&[u8], index:usize)->u16 {
    let data0 = _to_u8(data, index) as u16;
    let data1 = _to_u8(data, index+1) as u16;
    data0 << 8 | data1
}

fn _to_u64(data:&[u8], index:usize)->u64 {
    let data0 = _to_u32(data, index) as u64;
    let data1 = _to_u32(data, index+4) as u64;
    data0 << 32 | data1
}

fn _to_u32(data:&[u8], index:usize)->u32 {
    let data0 = _to_u16(data, index) as u32;
    let data1 = _to_u16(data, index+2) as u32;
    data0 << 16 | data1
}

fn test_function66(_param0 :uuid::timestamp::context::NoContext ,_param1 :uuid::timestamp::context::NoContext ,_param2 :u64 ,_param3 :u32) {
    let _local0: uuid::timestamp::Timestamp = uuid::timestamp::Timestamp::now(_param0);
    let _local1: uuid::timestamp::Timestamp = uuid::timestamp::Timestamp::from_unix(_param1, _param2, _param3);
    let _local2_param0_helper1 = &(_local0);
    let _local2_param1_helper1 = &(_local1);
    let _ = <uuid::timestamp::Timestamp as std::cmp::PartialEq::<uuid::timestamp::Timestamp>>::eq(_local2_param0_helper1, _local2_param1_helper1);
}

fn main() {
    fuzz!(|data: &[u8]| {
        //actual body emit
        if data.len() != 12 {return;}
        let _param0 = uuid::timestamp::context::NoContext{};
        let _param1 = uuid::timestamp::context::NoContext{};
        let _param2 = _to_u64(data, 0);
        let _param3 = _to_u32(data, 8);
        test_function66(_param0 ,_param1 ,_param2 ,_param3);
    });
}
