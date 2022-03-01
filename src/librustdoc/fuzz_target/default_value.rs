use std::convert::TryFrom;

use crate::clean::{self, Lifetime, PrimitiveType};

use rustc_hir::Mutability;

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum DefaultValue {
    StaticStr,
}

impl DefaultValue {
    pub const fn default_value(&self) -> &'static str {
        match self {
            DefaultValue::StaticStr => "\"42\"",
        }
    }
}

impl TryFrom<&clean::Type> for DefaultValue {
    type Error = ();
    fn try_from(ty: &clean::Type) -> Result<Self, Self::Error> {
        match ty {
            clean::Type::BorrowedRef {lifetime, mutability, type_} => {
                if let Some(lifetime_) = lifetime {
                    if *lifetime_ == Lifetime::statik() && *mutability == Mutability::Not 
                        && **type_ == clean::Type::Primitive(PrimitiveType::Str) {
                            return Ok(DefaultValue::StaticStr);
                        }
                }
                Err(())
            },
            _ => Err(()),
        }
    }
}