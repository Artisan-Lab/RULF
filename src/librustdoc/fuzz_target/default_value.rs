use std::convert::TryFrom;

use crate::clean::{self, Lifetime, PrimitiveType};

use rustc_hir::Mutability;

use super::{
    call_type::CallType,
    type_name::{type_full_name, TypeNameLevel, TypeNameMap},
};

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum DefaultValue {
    StaticStr,
    MutableSlice(clean::Type),
}

impl DefaultValue {
    pub fn default_value(&self) -> &'static str {
        match self {
            DefaultValue::StaticStr => "\"42\"",
            DefaultValue::MutableSlice(_) => "Vec::new()",
        }
    }

    pub fn call_type(&self) -> CallType {
        match self {
            DefaultValue::StaticStr => CallType::_DirectCall,
            DefaultValue::MutableSlice(_) => {
                CallType::_MutBorrowedRef(Box::new(CallType::_DirectCall))
            }
        }
    }

    pub fn requires_mut_tag(&self) -> bool {
        match self {
            DefaultValue::MutableSlice(_) => true,
            DefaultValue::StaticStr => false,
        }
    }

    pub fn requies_type_notation(&self) -> bool {
        match self {
            DefaultValue::MutableSlice(_) => true,
            DefaultValue::StaticStr => false,
        }
    }

    pub fn type_notation(&self, type_name_map: &TypeNameMap) -> String {
        match self {
            DefaultValue::StaticStr => "&'static str".to_string(),
            DefaultValue::MutableSlice(ty) => {
                let primitive_type_name = type_full_name(ty, type_name_map, TypeNameLevel::All);
                format!("Vec<{}>", primitive_type_name)
            }
        }
    }
}

impl TryFrom<&clean::Type> for DefaultValue {
    type Error = ();
    fn try_from(ty: &clean::Type) -> Result<Self, Self::Error> {
        match ty {
            clean::Type::BorrowedRef { lifetime, mutability, type_ } => {
                if let Some(lifetime_) = lifetime {
                    if *lifetime_ == Lifetime::statik()
                        && *mutability == Mutability::Not
                        && **type_ == clean::Type::Primitive(PrimitiveType::Str)
                    {
                        return Ok(DefaultValue::StaticStr);
                    }
                }
                if *mutability == Mutability::Mut {
                    if let clean::Type::Slice(ty_) = &**type_ {
                        if let Some(primitive_type) = ty_.primitive_type() {
                            let slice_ty = clean::Type::Primitive(primitive_type);
                            return Ok(DefaultValue::MutableSlice(slice_ty));
                        }
                    }
                }
                Err(())
            }
            _ => Err(()),
        }
    }
}
