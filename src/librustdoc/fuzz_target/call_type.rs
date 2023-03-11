use crate::clean::{self};
use crate::formats::cache::Cache;
use crate::fuzz_target::api_function::ApiUnsafety;
use crate::fuzz_target::api_util::_type_name;
use crate::fuzz_target::impl_util::FullNameMap;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub(crate) enum CallType {
    _NotCompatible,
    _DirectCall,                                  //直接调用
    _BorrowedRef(Box<CallType>),                  //取不可变引用
    _MutBorrowedRef(Box<CallType>),               //取可变引用
    _ConstRawPointer(Box<CallType>, clean::Type), //转换为不可变裸指针
    _MutRawPointer(Box<CallType>, clean::Type),   //转换为可变裸指针
    _AsConvert(String),                           //通过as进行转换
    _UnsafeDeref(Box<CallType>),                  //解引用裸指针
    _Deref(Box<CallType>),                        //解引用引用
    _UnwrapResult(Box<CallType>),                 //获得result变量的ok值
    _ToResult(Box<CallType>),                     //产生一个result类型, never used
    _UnwrapOption(Box<CallType>),                 //获得option变量的值
    _ToOption(Box<CallType>),                     //产生一个option类型
}

impl CallType {
    pub(crate) fn _to_call_string(&self, variable_name: &String, full_name_map: &FullNameMap, cache: &Cache) -> String {
        match self {
            CallType::_NotCompatible => String::new(),
            CallType::_DirectCall => variable_name.clone(),
            CallType::_BorrowedRef(inner_) => {
                let mut call_string = "&(".to_string();
                let inner_call_string = inner_._to_call_string(variable_name, full_name_map, cache);
                call_string.push_str(inner_call_string.as_str());
                call_string.push_str(")");
                call_string
            }
            CallType::_MutBorrowedRef(inner_) => {
                let mut call_string = "&mut (".to_string();
                let inner_call_string = inner_._to_call_string(variable_name, full_name_map, cache);
                call_string.push_str(inner_call_string.as_str());
                call_string.push_str(")");
                call_string
            }
            CallType::_ConstRawPointer(inner_, ty_) => {
                //TODO:需要转换之后的类型名
                let mut call_string = "&(".to_string();
                let inner_call_string = inner_._to_call_string(variable_name, full_name_map, cache);
                call_string.push_str(inner_call_string.as_str());
                call_string.push_str(") as *const ");
                call_string.push_str(_type_name(ty_, full_name_map, cache).as_str());
                call_string
            }
            CallType::_MutRawPointer(inner_, ty_) => {
                //TODO:需要转换之后的类型名
                let mut call_string = "&(".to_string();
                let inner_call_string = inner_._to_call_string(variable_name, full_name_map, cache);
                call_string.push_str(inner_call_string.as_str());
                call_string.push_str(") as *mut ");
                call_string.push_str(_type_name(ty_, full_name_map, cache).as_str());
                call_string
            }
            CallType::_AsConvert(str_) => {
                //TODO:需要转换之后的类型名
                let mut call_string = variable_name.to_string();
                call_string.push_str(" as ");
                call_string.push_str(str_.as_str());
                call_string
            }
            CallType::_UnsafeDeref(inner_) | CallType::_Deref(inner_) => {
                //TODO:unsafe deref需要考虑unsafe标记
                let mut call_string = "*(".to_string();
                let inner_call_string = inner_._to_call_string(variable_name, full_name_map, cache);
                call_string.push_str(inner_call_string.as_str());
                call_string.push_str(")");
                call_string
            }
            CallType::_UnwrapResult(inner_) => {
                //TODO:暂时先unwrap，后面再想办法处理逻辑
                let inner_call_string = inner_._to_call_string(variable_name, full_name_map, cache);
                format!("_unwrap_result({})", inner_call_string)
            }
            CallType::_UnwrapOption(inner_) => {
                //TODO:暂时先unwrap,后面在想办法处理
                let inner_call_string = inner_._to_call_string(variable_name, full_name_map, cache);
                format!("_unwrap_option({})", inner_call_string)
            }
            CallType::_ToOption(inner_) => {
                let inner_call_string = inner_._to_call_string(variable_name, full_name_map, cache);
                format!("Some({})", inner_call_string)
            }
            CallType::_ToResult(inner_) => {
                let inner_call_string = inner_._to_call_string(variable_name, full_name_map, cache);
                format!("Ok({})", inner_call_string)
            }
        }
    }

    pub(crate) fn unsafe_call_type(&self) -> ApiUnsafety {
        match self {
            CallType::_UnsafeDeref(..) => ApiUnsafety::Unsafe,
            _ => ApiUnsafety::Normal,
        }
    }

    pub(crate) fn _contains_move_call_type(&self) -> bool {
        self._contains_unwrap_call_type()
    }

    pub(crate) fn _is_unwrap_call_type(&self) -> bool {
        match self {
            CallType::_UnwrapOption(..) | CallType::_UnwrapResult(..) => true,
            _ => false,
        }
    }
    pub(crate) fn _contains_unwrap_call_type(&self) -> bool {
        match self {
            CallType::_NotCompatible | CallType::_DirectCall | CallType::_AsConvert(..) => false,
            CallType::_UnwrapOption(..) | CallType::_UnwrapResult(..) => true,
            CallType::_BorrowedRef(call_type)
            | CallType::_MutBorrowedRef(call_type)
            | CallType::_ConstRawPointer(call_type, _)
            | CallType::_MutRawPointer(call_type, _)
            | CallType::_UnsafeDeref(call_type)
            | CallType::_Deref(call_type)
            | CallType::_ToOption(call_type)
            | CallType::_ToResult(call_type) => call_type._contains_move_call_type(),
        }
    }

    pub(crate) fn _call_type_to_array(&self) -> Vec<CallType> {
        match self {
            CallType::_NotCompatible | CallType::_DirectCall | CallType::_AsConvert(..) => {
                vec![self.clone()]
            }
            CallType::_UnwrapOption(call_type)
            | CallType::_UnwrapResult(call_type)
            | CallType::_BorrowedRef(call_type)
            | CallType::_MutBorrowedRef(call_type)
            | CallType::_ConstRawPointer(call_type, _)
            | CallType::_MutRawPointer(call_type, _)
            | CallType::_UnsafeDeref(call_type)
            | CallType::_Deref(call_type)
            | CallType::_ToOption(call_type)
            | CallType::_ToResult(call_type) => {
                let mut call_types = vec![self.clone()];
                let mut inner_call_types = call_type._call_type_to_array();
                call_types.append(&mut inner_call_types);
                call_types
            }
        }
    }

    pub(crate) fn _split_at_unwrap_call_type(&self) -> Vec<CallType> {
        if !self._contains_unwrap_call_type() {
            return vec![self.clone()];
        }
        let raw_array = self._call_type_to_array();
        //println!("raw array = {:?}", raw_array);
        let mut res = Vec::new();
        let raw_array_len = raw_array.len();
        let mut one_split = Vec::new();
        for i in 0..raw_array_len {
            let current_call_type = &raw_array[i];
            //println!("current call type: {:?}", current_call_type);
            if !current_call_type._is_unwrap_call_type() {
                one_split.push(current_call_type.clone());
                if i == raw_array_len - 1 {
                    res.push(one_split.clone());
                }
            } else {
                let one_split_len = one_split.len();
                if one_split_len > 0 {
                    //注意要在one_split的最后加一个diretc call
                    one_split.push(CallType::_DirectCall);
                    res.push(one_split.clone());
                }
                one_split.clear();
                one_split.push(current_call_type.clone());
            }
        }
        let mut call_types = Vec::new();
        for call_type_array in &res {
            //println!("before concat: {:?}", call_type_array);
            let call_type = CallType::_array_to_call_type(call_type_array);
            //println!("after concat: {:?}", call_type);
            call_types.push(call_type);
        }
        call_types.reverse();
        //println!("call_type_array = {:?}",call_types);
        let last_call_type = call_types.last().unwrap();
        if last_call_type._is_unwrap_call_type() {
            call_types.push(CallType::_DirectCall);
        }
        call_types
    }

    pub(crate) fn _array_to_call_type(call_type_array: &Vec<CallType>) -> Self {
        CallType::_inner_array_to_call_type(call_type_array, 0)
    }

    fn _inner_array_to_call_type(call_type_array: &Vec<CallType>, start: usize) -> Self {
        let array_len = call_type_array.len();
        if start >= array_len {
            println!("should not go to here in inner array to call type");
            return CallType::_NotCompatible;
        }
        if start == array_len - 1 {
            return call_type_array[start].clone();
        }
        let current_type = call_type_array[start].clone();
        let inner_type = CallType::_inner_array_to_call_type(call_type_array, start + 1);
        match current_type {
            CallType::_DirectCall | CallType::_AsConvert(..) | CallType::_NotCompatible => {
                println!("should not go to here in inner array to call type 2");
                return CallType::_NotCompatible;
            }
            CallType::_BorrowedRef(..) => CallType::_BorrowedRef(Box::new(inner_type)),
            CallType::_MutBorrowedRef(..) => CallType::_MutBorrowedRef(Box::new(inner_type)),
            CallType::_ConstRawPointer(_, ref type_) => {
                CallType::_ConstRawPointer(Box::new(inner_type), type_.clone())
            }
            CallType::_MutRawPointer(_, ref type_) => {
                CallType::_MutRawPointer(Box::new(inner_type), type_.clone())
            }
            CallType::_UnsafeDeref(..) => CallType::_UnsafeDeref(Box::new(inner_type)),
            CallType::_Deref(..) => CallType::_Deref(Box::new(inner_type)),
            CallType::_UnwrapOption(..) => CallType::_UnwrapOption(Box::new(inner_type)),
            CallType::_ToOption(..) => CallType::_ToOption(Box::new(inner_type)),
            CallType::_UnwrapResult(..) => CallType::_UnwrapResult(Box::new(inner_type)),
            CallType::_ToResult(..) => CallType::_ToResult(Box::new(inner_type)),
        }
    }
}
