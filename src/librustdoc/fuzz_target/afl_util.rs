use crate::clean::PrimitiveType;
use crate::fuzz_target::fuzzable_type::FuzzableType;
use rustc_data_structures::fx::FxHashSet;
#[derive(Debug, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) enum _AflHelpers {
    _NoHelper,
    _U8,
    _I8,
    _U16,
    _I16,
    _U32,
    _I32,
    _F32,
    _U64,
    _I64,
    _F64,
    _U128,
    _I128,
    _Usize,
    _Isize,
    _Char,
    _Bool,
    _Str,
    _Slice(Box<_AflHelpers>),
    _Tuple(Vec<Box<_AflHelpers>>),
}

impl _AflHelpers {
    pub(crate) fn _new_from_fuzzable(fuzzable: &FuzzableType) -> Self {
        match fuzzable {
            FuzzableType::NoFuzzable => _AflHelpers::_NoHelper,
            FuzzableType::RefStr => _AflHelpers::_Str,
            FuzzableType::Primitive(primitive_type) => match primitive_type {
                PrimitiveType::U8 => _AflHelpers::_U8,
                PrimitiveType::I8 => _AflHelpers::_I8,
                PrimitiveType::U16 => _AflHelpers::_U16,
                PrimitiveType::I16 => _AflHelpers::_I16,
                PrimitiveType::U32 => _AflHelpers::_U32,
                PrimitiveType::I32 => _AflHelpers::_I32,
                PrimitiveType::U64 => _AflHelpers::_U64,
                PrimitiveType::I64 => _AflHelpers::_I64,
                PrimitiveType::U128 => _AflHelpers::_U128,
                PrimitiveType::I128 => _AflHelpers::_I128,
                PrimitiveType::Usize => _AflHelpers::_Usize,
                PrimitiveType::Isize => _AflHelpers::_Isize,
                PrimitiveType::Char => _AflHelpers::_Char,
                PrimitiveType::Bool => _AflHelpers::_Bool,
                PrimitiveType::F32 => _AflHelpers::_F32,
                PrimitiveType::F64 => _AflHelpers::_F64,
                _ => _AflHelpers::_NoHelper,
            },
            FuzzableType::RefSlice(inner_fuzzable) => {
                let inner_afl_helper = _AflHelpers::_new_from_fuzzable(inner_fuzzable);
                _AflHelpers::_Slice(Box::new(inner_afl_helper))
            }
            FuzzableType::Tuple(inner_fuzzables) => {
                let inner_afl_helpers: Vec<Box<_AflHelpers>> = inner_fuzzables
                    .into_iter()
                    .map(|inner_fuzzable| Box::new(_AflHelpers::_new_from_fuzzable(inner_fuzzable)))
                    .collect();
                _AflHelpers::_Tuple(inner_afl_helpers)
            }
        }
    }

    //找到所有依赖的afl helper,包括自身
    //TODO：注意到这个函数在处理slice的时候会有些问题，不同的slice会有多个afl helpers，
    //但实际上我们只需要定义一个函数，但这个函数很难继续调整，所以我们在别的地方需要注意这里面的逻辑
    //Tuple在这一步已经全部排除掉了，所以接下来不会再有tuple的问题
    pub(crate) fn _get_all_dependent_afl_helpers(&self) -> Vec<_AflHelpers> {
        let mut helpers = Vec::new();
        if let _AflHelpers::_Tuple(inner_helpers) = self {
            for afl_helper in inner_helpers {
                let mut inner_dependent = afl_helper._get_all_dependent_afl_helpers();
                helpers.append(&mut inner_dependent);
            }
        } else {
            helpers.push(self.clone());
            match self {
                _AflHelpers::_U8
                | _AflHelpers::_I8
                | _AflHelpers::_NoHelper
                | _AflHelpers::_Slice(..)
                | _AflHelpers::_Str
                | _AflHelpers::_F32
                | _AflHelpers::_F64 => {}
                _AflHelpers::_Bool => {
                    let mut u8_dependency = _AflHelpers::_U8._get_all_dependent_afl_helpers();
                    helpers.append(&mut u8_dependency);
                }
                _AflHelpers::_U16 => {
                    let mut u8_dependency = _AflHelpers::_U8._get_all_dependent_afl_helpers();
                    helpers.append(&mut u8_dependency);
                }
                _AflHelpers::_I16 => {
                    let mut i8_dependency = _AflHelpers::_I8._get_all_dependent_afl_helpers();
                    helpers.append(&mut i8_dependency);
                }
                _AflHelpers::_U32 => {
                    let mut u16_dependency = _AflHelpers::_U16._get_all_dependent_afl_helpers();
                    helpers.append(&mut u16_dependency);
                }
                _AflHelpers::_I32 => {
                    let mut i16_dependency = _AflHelpers::_I16._get_all_dependent_afl_helpers();
                    helpers.append(&mut i16_dependency);
                }
                _AflHelpers::_U64 => {
                    let mut u32_dependency = _AflHelpers::_U32._get_all_dependent_afl_helpers();
                    helpers.append(&mut u32_dependency);
                }
                _AflHelpers::_I64 => {
                    let mut i32_dependency = _AflHelpers::_I32._get_all_dependent_afl_helpers();
                    helpers.append(&mut i32_dependency);
                }
                _AflHelpers::_U128 => {
                    let mut u64_dependency = _AflHelpers::_U64._get_all_dependent_afl_helpers();
                    helpers.append(&mut u64_dependency);
                }
                _AflHelpers::_I128 => {
                    let mut i64_dependency = _AflHelpers::_I64._get_all_dependent_afl_helpers();
                    helpers.append(&mut i64_dependency);
                }
                _AflHelpers::_Usize => {
                    let mut u64_dependency = _AflHelpers::_U64._get_all_dependent_afl_helpers();
                    helpers.append(&mut u64_dependency);
                }
                _AflHelpers::_Isize => {
                    let mut i64_dependency = _AflHelpers::_I64._get_all_dependent_afl_helpers();
                    helpers.append(&mut i64_dependency);
                }
                _AflHelpers::_Char => {
                    let mut u32_dependency = _AflHelpers::_U32._get_all_dependent_afl_helpers();
                    helpers.append(&mut u32_dependency);
                }
                _AflHelpers::_Tuple(..) => {}
            }
        }
        helpers
    }

    pub(crate) fn _to_full_function(&self) -> &'static str {
        match self {
            _AflHelpers::_NoHelper => "afl no helper",
            _AflHelpers::_U8 => _data_to_u8(),
            _AflHelpers::_I8 => _data_to_i8(),
            _AflHelpers::_U16 => _data_to_u16(),
            _AflHelpers::_I16 => _data_to_i16(),
            _AflHelpers::_U32 => _data_to_u32(),
            _AflHelpers::_I32 => _data_to_i32(),
            _AflHelpers::_F32 => _data_to_f32(),
            _AflHelpers::_U64 => _data_to_u64(),
            _AflHelpers::_I64 => _data_to_i64(),
            _AflHelpers::_F64 => _data_to_f64(),
            _AflHelpers::_U128 => _data_to_u128(),
            _AflHelpers::_I128 => _data_to_i128(),
            _AflHelpers::_Usize => _data_to_usize(),
            _AflHelpers::_Isize => _data_to_isize(),
            _AflHelpers::_Char => _data_to_char(),
            _AflHelpers::_Bool => _data_to_bool(),
            _AflHelpers::_Str => _data_to_str(),
            _AflHelpers::_Slice(..) => _data_to_slice(),
            _AflHelpers::_Tuple(..) => "",
        }
    }

    pub(crate) fn _type_name(&self) -> String {
        match self {
            _AflHelpers::_NoHelper => "afl no helper".to_string(),
            _AflHelpers::_U8 => "u8".to_string(),
            _AflHelpers::_I8 => "i8".to_string(),
            _AflHelpers::_U16 => "u16".to_string(),
            _AflHelpers::_I16 => "i16".to_string(),
            _AflHelpers::_U32 => "u32".to_string(),
            _AflHelpers::_I32 => "i32".to_string(),
            _AflHelpers::_F32 => "f32".to_string(),
            _AflHelpers::_U64 => "u64".to_string(),
            _AflHelpers::_I64 => "i64".to_string(),
            _AflHelpers::_F64 => "f64".to_string(),
            _AflHelpers::_U128 => "u128".to_string(),
            _AflHelpers::_I128 => "i128".to_string(),
            _AflHelpers::_Usize => "usize".to_string(),
            _AflHelpers::_Isize => "isize".to_string(),
            _AflHelpers::_Bool => "bool".to_string(),
            _AflHelpers::_Char => "char".to_string(),
            _AflHelpers::_Str => "str".to_string(),
            _AflHelpers::_Slice(..) => "slice".to_string(),
            _AflHelpers::_Tuple(inner_afl_helpers) => {
                let mut type_name = "(".to_string();
                let inner_afl_helpers_length = inner_afl_helpers.len();
                for i in 0..inner_afl_helpers_length {
                    let inner_afl_helper = &inner_afl_helpers[i];
                    let inner_type_name = inner_afl_helper._type_name();
                    if i != 0 {
                        type_name.push_str(" ,");
                    }
                    type_name.push_str(inner_type_name.as_str());
                }
                type_name.push_str(")");
                return type_name;
            }
        }
    }

    pub(crate) fn _to_function_name(&self) -> String {
        match self {
            _AflHelpers::_Slice(inner_afl_helpers) => {
                //不考虑内部还是slice或者str的情况,这种函数在构建graph的时候就已经作为多维动态长度被删掉了
                //tuple里面也不会出现slice或者
                let inner_type_name = inner_afl_helpers._type_name();
                format!(
                    "_to_{type_name}::<{inner_type_name}>",
                    type_name = self._type_name(),
                    inner_type_name = inner_type_name
                )
            }
            _AflHelpers::_Tuple(..) => String::new(),
            _ => {
                format!("_to_{type_name}", type_name = self._type_name())
            }
        }
    }

    pub(crate) fn _print_all() {
        println!("afl helper functions: ");
        println!("{}", _data_to_u8());
        println!("{}", _data_to_i8());
        println!("{}", _data_to_u16());
        println!("{}", _data_to_i16());
        println!("{}", _data_to_u32());
        println!("{}", _data_to_i32());
        println!("{}", _data_to_u64());
        println!("{}", _data_to_i64());
        println!("{}", _data_to_u128());
        println!("{}", _data_to_i128());
        println!("{}", _data_to_usize());
        println!("{}", _data_to_isize());
        println!("{}", _data_to_char());
        println!("{}", _data_to_bool());
        println!("{}", _data_to_str());
        println!("{}", _data_to_slice());
        println!("{}", _data_to_f32());
        println!("{}", _data_to_f64());
    }

    //may remove later
    pub(crate) fn _feature_gate(&self) -> Option<String> {
        match self {
            _AflHelpers::_Char => {
                let s = "#![feature(assoc_char_funcs)]".to_string();
                Some(s)
            }
            _ => None,
        }
    }

    pub(crate) fn _is_slice(&self) -> bool {
        match self {
            _AflHelpers::_Slice(..) => return true,
            _ => false,
        }
    }

    pub(crate) fn _is_tuple(&self) -> bool {
        match self {
            _AflHelpers::_Tuple(..) => return true,
            _ => false,
        }
    }

    pub(crate) fn _generate_param_initial_statement(
        &self,
        param_index: usize,
        fixed_start_index: usize,
        dynamic_start_index: usize,
        dynamic_param_index: usize,
        total_dynamic_param_numbers: usize,
        dynamic_param_length: &String,
        origin_fuzzable_type: &FuzzableType,
    ) -> String {
        match self {
            _AflHelpers::_NoHelper => {
                format!("No helper")
            }
            _ => {
                let rhs = self._generate_param_initial_rhs(
                    fixed_start_index,
                    dynamic_start_index,
                    dynamic_param_index,
                    total_dynamic_param_numbers,
                    dynamic_param_length,
                    origin_fuzzable_type,
                );
                format!("let _param{param_index} = {rhs};", param_index = param_index, rhs = rhs)
            }
        }
    }

    pub(crate) fn _generate_param_initial_rhs(
        &self,
        fixed_start_index: usize,
        dynamic_start_index: usize,
        dynamic_param_index: usize,
        total_dynamic_param_numbers: usize,
        dynamic_param_length: &String,
        origin_fuzzable_type: &FuzzableType,
    ) -> String {
        match self {
            _AflHelpers::_Bool
            | _AflHelpers::_U8
            | _AflHelpers::_I8
            | _AflHelpers::_U16
            | _AflHelpers::_I16
            | _AflHelpers::_U32
            | _AflHelpers::_I32
            | _AflHelpers::_Char
            | _AflHelpers::_U64
            | _AflHelpers::_I64
            | _AflHelpers::_U128
            | _AflHelpers::_I128
            | _AflHelpers::_Usize
            | _AflHelpers::_Isize
            | _AflHelpers::_F32
            | _AflHelpers::_F64 => {
                format!(
                    "{afl_function_name}(data, {fixed_start_index})",
                    afl_function_name = self._to_function_name(),
                    fixed_start_index = fixed_start_index
                )
            }
            _AflHelpers::_Str | _AflHelpers::_Slice(..) => {
                let latter_index = if dynamic_param_index == total_dynamic_param_numbers - 1 {
                    format!("data.len()")
                } else {
                    format!(
                        "{dynamic_start_index} + {dynamic_param_index} * {dynamic_param_length}",
                        dynamic_start_index = dynamic_start_index,
                        dynamic_param_index = dynamic_param_index + 1,
                        dynamic_param_length = dynamic_param_length
                    )
                };
                format!(
                    "{afl_function_name}(data, {dynamic_start_index} + {dynamic_param_index} * {dynamic_param_length}, {latter_index})",
                    afl_function_name = self._to_function_name(),
                    dynamic_start_index = dynamic_start_index,
                    dynamic_param_index = dynamic_param_index,
                    dynamic_param_length = dynamic_param_length,
                    latter_index = latter_index
                )
            }
            _AflHelpers::_Tuple(inner_afl_helpers) => {
                if let FuzzableType::Tuple(inner_fuzzables) = origin_fuzzable_type {
                    let mut res = "(".to_string();
                    let inner_afl_helpers_number = inner_afl_helpers.len();

                    let mut inner_fixed_start_index = fixed_start_index;
                    let mut inner_dynamic_param_index = dynamic_param_index;
                    for i in 0..inner_afl_helpers_number {
                        if i != 0 {
                            res.push_str(", ");
                        }
                        let inner_afl_helper = &inner_afl_helpers[i];
                        let inner_origin_fuzzable_type = &inner_fuzzables[i];
                        let inner_rhs = inner_afl_helper._generate_param_initial_rhs(
                            inner_fixed_start_index,
                            dynamic_start_index,
                            inner_dynamic_param_index,
                            total_dynamic_param_numbers,
                            dynamic_param_length,
                            inner_origin_fuzzable_type,
                        );
                        res.push_str(inner_rhs.as_str());
                        inner_fixed_start_index = inner_fixed_start_index
                            + inner_origin_fuzzable_type._fixed_part_length();
                        inner_dynamic_param_index = inner_dynamic_param_index
                            + inner_origin_fuzzable_type._dynamic_length_param_number();
                    }
                    res.push_str(")");
                    res
                } else {
                    "Type not match in afl_util".to_string()
                }
            }
            _AflHelpers::_NoHelper => {
                format!("No helper")
            }
        }
    }
}

//使用FxHashset去重
pub(crate) fn _get_all_dependent_afl_helpers_of_sequence(
    fuzzable_params: &Vec<FuzzableType>,
) -> FxHashSet<_AflHelpers> {
    let mut res = FxHashSet::default();
    for fuzzable_param in fuzzable_params {
        let afi_helper = _AflHelpers::_new_from_fuzzable(fuzzable_param);
        let dependencies = afi_helper._get_all_dependent_afl_helpers();
        for dependency in &dependencies {
            res.insert(dependency.clone());
        }
    }
    res
}

//获得所有的函数的定义，对于slice的话，由于采用了范型，只需要加入一次
pub(crate) fn _get_afl_helpers_functions_of_sequence(
    fuzzable_params: &Vec<FuzzableType>,
) -> Option<Vec<String>> {
    let afl_helpers = _get_all_dependent_afl_helpers_of_sequence(fuzzable_params);
    if afl_helpers.len() < 1 {
        return None;
    }
    let mut afl_helper_functions = Vec::new();

    let mut contains_slice_flag = false;
    for afl_helper in afl_helpers {
        if !contains_slice_flag && afl_helper._is_slice() {
            contains_slice_flag = true;
            afl_helper_functions.push(afl_helper._to_full_function().to_string());
            continue;
        }
        afl_helper_functions.push(afl_helper._to_full_function().to_string())
    }
    Some(afl_helper_functions)
}

//获得可能的feature gate,
pub(crate) fn _get_feature_gates_of_sequence(fuzzable_params: &Vec<FuzzableType>) -> Option<Vec<String>> {
    let all_afl_helpers = _get_all_dependent_afl_helpers_of_sequence(fuzzable_params);
    let mut feature_gates = FxHashSet::default();
    for afl_helper in all_afl_helpers {
        let feature_gate = afl_helper._feature_gate();
        if feature_gate.is_some() {
            let feature_gate = feature_gate.unwrap();
            feature_gates.insert(feature_gate);
        }
    }
    if feature_gates.len() < 1 {
        return None;
    }
    let mut features = Vec::new();
    for feature_gate in feature_gates {
        features.push(feature_gate);
    }
    Some(features)
}

pub(crate) fn _data_to_u8() -> &'static str {
    "fn _to_u8(data:&[u8], index:usize)->u8 {
    data[index]
}\n"
}

pub(crate) fn _data_to_i8() -> &'static str {
    "fn _to_i8(data:&[u8], index:usize)->i8 {    
    data[index] as i8
}\n"
}

pub(crate) fn _data_to_u16() -> &'static str {
    "fn _to_u16(data:&[u8], index:usize)->u16 {
    let data0 = _to_u8(data, index) as u16;
    let data1 = _to_u8(data, index+1) as u16;
    data0 << 8 | data1
}\n"
}

pub(crate) fn _data_to_i16() -> &'static str {
    "fn _to_i16(data:&[u8], index:usize)->i16 {
    let data0 = _to_i8(data, index) as i16;
    let data1 = _to_i8(data, index+1) as i16;
    data0 << 8 | data1
}\n"
}

pub(crate) fn _data_to_u32() -> &'static str {
    "fn _to_u32(data:&[u8], index:usize)->u32 {
    let data0 = _to_u16(data, index) as u32;
    let data1 = _to_u16(data, index+2) as u32;
    data0 << 16 | data1
}\n"
}

pub(crate) fn _data_to_i32() -> &'static str {
    "fn _to_i32(data:&[u8], index:usize)->i32 {
    let data0 = _to_i16(data, index) as i32;
    let data1 = _to_i16(data, index+2) as i32;
    data0 << 16 | data1
}\n"
}

pub(crate) fn _data_to_f32() -> &'static str {
    "fn _to_f32(data:&[u8], index: usize) -> f32 {
    let data_slice = &data[index..index+4];
    use std::convert::TryInto;
    let data_array:[u8;4] = data_slice.try_into().expect(\"slice with incorrect length\");
    f32::from_le_bytes(data_array)
}\n"
}

pub(crate) fn _data_to_u64() -> &'static str {
    "fn _to_u64(data:&[u8], index:usize)->u64 {
    let data0 = _to_u32(data, index) as u64;
    let data1 = _to_u32(data, index+4) as u64;
    data0 << 32 | data1
}\n"
}

pub(crate) fn _data_to_i64() -> &'static str {
    "fn _to_i64(data:&[u8], index:usize)->i64 {
    let data0 = _to_i32(data, index) as i64;
    let data1 = _to_i32(data, index+4) as i64;
    data0 << 32 | data1
}\n"
}

pub(crate) fn _data_to_f64() -> &'static str {
    "fn _to_f64(data:&[u8], index: usize) -> f64 {
    let data_slice = &data[index..index+8];
    use std::convert::TryInto;
    let data_array:[u8;8] = data_slice.try_into().expect(\"slice with incorrect length\");
    f64::from_le_bytes(data_array)
}\n"
}

pub(crate) fn _data_to_u128() -> &'static str {
    "fn _to_u128(data:&[u8], index:usize)->u128 {
    let data0 = _to_u64(data, index) as u128;
    let data1 = _to_u64(data, index+8) as u128;
    data0 << 64 | data1
}\n"
}

pub(crate) fn _data_to_i128() -> &'static str {
    "fn _to_i128(data:&[u8], index:usize)->i128 {
    let data0 = _to_i64(data, index) as i128;
    let data1 = _to_i64(data, index+8) as i128;
    data0 << 64 | data1
}\n"
}

pub(crate) fn _data_to_usize() -> &'static str {
    "fn _to_usize(data:&[u8], index:usize)->usize {
    _to_u64(data, index) as usize
}\n"
}

pub(crate) fn _data_to_isize() -> &'static str {
    "fn _to_isize(data:&[u8], index:usize)->isize {
    _to_i64(data, index) as isize
}\n"
}

pub(crate) fn _data_to_char() -> &'static str {
    "fn _to_char(data:&[u8], index: usize)->char {
    let char_value = _to_u32(data,index);
    match char::from_u32(char_value) {
        Some(c)=>c,
        None=>{
            use std::process;
            process::exit(0);
        }
    }
}\n"
}

pub(crate) fn _data_to_bool() -> &'static str {
    "fn _to_bool(data:&[u8], index: usize)->bool {
    let bool_value = _to_u8(data, index);
    if bool_value %2 == 0 {
        true
    } else {
        false
    }
}\n"
}

pub(crate) fn _data_to_str() -> &'static str {
    "fn _to_str(data:&[u8], start_index: usize, end_index: usize)->&str {
    let data_slice = &data[start_index..end_index];
    use std::str;
    match str::from_utf8(data_slice) {
        Ok(s)=>s,
        Err(_)=>{
            use std::process;
            process::exit(0);
        }
    }
}\n"
}

//会有big endian和 little endian的问题，不过只是去fuzz的话，应该没啥影响
pub(crate) fn _data_to_slice() -> &'static str {
    "fn _to_slice<T>(data:&[u8], start_index: usize, end_index: usize)->&[T] {
    let data_slice = &data[start_index..end_index];
    let (_, shorts, _) = unsafe {data_slice.align_to::<T>()};
    shorts
}\n"
}
