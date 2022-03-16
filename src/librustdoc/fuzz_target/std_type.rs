use crate::clean;

use super::call_type::CallType;
use super::fuzzable_type::FuzzableType;
use super::type_name::{type_full_name, TypeNameLevel, TypeNameMap};

/// support special std type. Std types are dealt with case by case now.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StdCallType {
    RefPath, // &std::path::Path
    IpAddr,  // std::net::IpAddr
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StdType {
    RefPath,
    IpAddr,
}

impl StdCallType {
    pub fn try_from_type(type_: &clean::Type, type_name_map: &TypeNameMap) -> Result<Self, ()> {
        let type_full_name = type_full_name(type_, type_name_map, TypeNameLevel::All);
        match type_full_name.as_str() {
            "&std::path::Path" => Ok(StdCallType::RefPath),
            "std::net::ip::IpAddr" => Ok(StdCallType::IpAddr),
            _ => Err(()),
        }
    }

    pub fn std_type_and_call_type(&self) -> (StdType, CallType) {
        match self {
            StdCallType::RefPath => (StdType::RefPath, CallType::_DirectCall),
            StdCallType::IpAddr => (StdType::IpAddr, CallType::_DirectCall),
        }
    }
}

impl StdType {
    pub fn fuzzable_type_and_call_type(&self) -> Vec<(FuzzableType, CallType)> {
        match self {
            StdType::RefPath => vec![(FuzzableType::RefStr, CallType::_DirectCall)],
            StdType::IpAddr => vec![(FuzzableType::RefStr, CallType::_DirectCall)],
        }
    }

    pub fn call_string(&self, params: Vec<String>) -> String {
        match self {
            StdType::RefPath => {
                if params.len() != 1 {
                    panic!("std::path::Path::new requires only one parameter.");
                }
                let param = params.first().unwrap();
                format!("std::path::Path::new({})", param)
            }
            StdType::IpAddr => {
                if params.len() != 1 {
                    panic!("IpAddr parse requires only one parameter.");
                }
                let param = params.first().unwrap();
                format!(
                    "if let Ok(ip_addr) = {}.parse::<std::net::IpAddr>() {{ip_addr}} else {{std::process::exit(-1);}}",
                    param
                )
            }
        }
    }
}
