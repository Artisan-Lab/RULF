use crate::clean::{self, PrimitiveType};

use super::call_type::CallType;
use super::fuzzable_type::FuzzableType;
use super::type_name::{type_full_name, TypeNameLevel, TypeNameMap};

/// support special std type. Std types are dealt with case by case now.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StdCallType {
    IpAddr,       // std::net::IpAddr
    VecU8,        // Vec<u8>
    RefMutVecU8,  // &mut Vec<u8>
    NonZeroUsize, // std::num::NonZeroUsize
    NonZeroI8,    // std::num::NonZeroI8,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StdType {
    IpAddr,
    VecU8,
    NonZeroUsize,
    NonZeroI8,
}

impl StdCallType {
    pub fn try_from_type(type_: &clean::Type, type_name_map: &TypeNameMap) -> Result<Self, ()> {
        let type_full_name = type_full_name(type_, type_name_map, TypeNameLevel::All);
        match type_full_name.as_str() {
            "std::net::ip::IpAddr" => Ok(StdCallType::IpAddr),
            "Vec<u8>" => Ok(StdCallType::VecU8),
            "&mut Vec<u8>" => Ok(StdCallType::RefMutVecU8),
            "core::num::NonZeroUsize" => Ok(StdCallType::NonZeroUsize),
            "core::num::NonZeroI8" => Ok(StdCallType::NonZeroI8),
            _ => Err(()),
        }
    }

    pub fn std_type_and_call_type(&self) -> (StdType, CallType) {
        match self {
            StdCallType::IpAddr => (StdType::IpAddr, CallType::_DirectCall),
            StdCallType::VecU8 => (StdType::VecU8, CallType::_DirectCall),
            StdCallType::RefMutVecU8 => {
                (StdType::VecU8, CallType::_MutBorrowedRef(Box::new(CallType::_DirectCall)))
            },
            StdCallType::NonZeroUsize => {
                (StdType::NonZeroUsize, CallType::_DirectCall)
            },
            StdCallType::NonZeroI8 => {
                (StdType::NonZeroI8, CallType::_DirectCall)
            }
        }
    }

    pub fn requires_mut_tag(&self) -> bool {
        match self {
            StdCallType::RefMutVecU8 => true,
            StdCallType::IpAddr | StdCallType::VecU8 | StdCallType::NonZeroUsize | StdCallType::NonZeroI8 => false,
        }
    }
}

impl StdType {
    pub fn fuzzable_type_and_call_type(&self) -> Vec<(FuzzableType, CallType)> {
        match self {
            StdType::IpAddr => vec![(FuzzableType::RefStr, CallType::_DirectCall)],
            StdType::VecU8 => vec![(
                FuzzableType::RefSlice(Box::new(FuzzableType::Primitive(PrimitiveType::U8))),
                CallType::_DirectCall,
            )],
            StdType::NonZeroUsize => vec![(FuzzableType::Primitive(PrimitiveType::Usize), CallType::_DirectCall)],
            StdType::NonZeroI8 => vec![(FuzzableType::Primitive(PrimitiveType::I8), CallType::_DirectCall)],
        }
    }

    pub fn call_string(&self, params: Vec<String>) -> String {
        match self {
            StdType::IpAddr => {
                if params.len() != 1 {
                    panic!("IpAddr requires only one parameter.");
                }
                let param = params.first().unwrap();
                format!(
                    "if let Ok(ip_addr) = {}.parse::<std::net::IpAddr>() {{ip_addr}} else {{std::process::exit(-1);}}",
                    param
                )
            },
            StdType::VecU8 => {
                if params.len() != 1 {
                    panic!("Vec<u8> requires only one parameter.");
                }
                let param = params.first().unwrap();
                format!("{}.to_vec()", param)
            },
            StdType::NonZeroUsize => {
                if params.len() != 1 {
                    panic!("NonZeroUsize requires only one parameter.");
                }
                let param = params.first().unwrap();
                format!(
                    "if let Some(res) = std::num::NonZeroUsize::new({}) {{res}} else {{std::process::exit(-1);}}",
                    param
                )
            },
            StdType::NonZeroI8 => {
                if params.len() != 1 {
                    panic!("NonZeroI8 requires only one parameter.");
                }
                let param = params.first().unwrap();
                format!(
                    "if let Some(res) = std::num::NonZeroI8::new({}) {{res}} else {{std::process::exit(-1);}}",
                    param
                )
            },
        }
    }
}
