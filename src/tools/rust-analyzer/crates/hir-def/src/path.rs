//! A desugared representation of paths like `crate::foo` or `<Type as Trait>::bar`.
mod lower;

use std::{
    fmt::{self, Display},
    iter,
};

use crate::{
    body::LowerCtx,
    intern::Interned,
    type_ref::{ConstScalarOrPath, LifetimeRef},
};
use hir_expand::name::Name;
use syntax::ast;

use crate::type_ref::{TypeBound, TypeRef};

pub use hir_expand::mod_path::{path, ModPath, PathKind};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImportAlias {
    /// Unnamed alias, as in `use Foo as _;`
    Underscore,
    /// Named alias
    Alias(Name),
}

impl Display for ImportAlias {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ImportAlias::Underscore => f.write_str("_"),
            ImportAlias::Alias(name) => f.write_str(&name.to_smol_str()),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Path {
    /// Type based path like `<T>::foo`.
    /// Note that paths like `<Type as Trait>::foo` are desugard to `Trait::<Self=Type>::foo`.
    type_anchor: Option<Interned<TypeRef>>,
    mod_path: Interned<ModPath>,
    /// Invariant: the same len as `self.mod_path.segments`
    generic_args: Box<[Option<Interned<GenericArgs>>]>,
}

/// Generic arguments to a path segment (e.g. the `i32` in `Option<i32>`). This
/// also includes bindings of associated types, like in `Iterator<Item = Foo>`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GenericArgs {
    pub args: Vec<GenericArg>,
    /// This specifies whether the args contain a Self type as the first
    /// element. This is the case for path segments like `<T as Trait>`, where
    /// `T` is actually a type parameter for the path `Trait` specifying the
    /// Self type. Otherwise, when we have a path `Trait<X, Y>`, the Self type
    /// is left out.
    pub has_self_type: bool,
    /// Associated type bindings like in `Iterator<Item = T>`.
    pub bindings: Vec<AssociatedTypeBinding>,
    /// Whether these generic args were desugared from `Trait(Arg) -> Output`
    /// parenthesis notation typically used for the `Fn` traits.
    pub desugared_from_fn: bool,
}

/// An associated type binding like in `Iterator<Item = T>`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AssociatedTypeBinding {
    /// The name of the associated type.
    pub name: Name,
    /// The type bound to this associated type (in `Item = T`, this would be the
    /// `T`). This can be `None` if there are bounds instead.
    pub type_ref: Option<TypeRef>,
    /// Bounds for the associated type, like in `Iterator<Item:
    /// SomeOtherTrait>`. (This is the unstable `associated_type_bounds`
    /// feature.)
    pub bounds: Vec<Interned<TypeBound>>,
}

/// A single generic argument.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum GenericArg {
    Type(TypeRef),
    Lifetime(LifetimeRef),
    Const(ConstScalarOrPath),
}

impl Path {
    /// Converts an `ast::Path` to `Path`. Works with use trees.
    /// It correctly handles `$crate` based path from macro call.
    pub fn from_src(path: ast::Path, ctx: &LowerCtx<'_>) -> Option<Path> {
        lower::lower_path(path, ctx)
    }

    /// Converts a known mod path to `Path`.
    pub fn from_known_path(
        path: ModPath,
        generic_args: impl Into<Box<[Option<Interned<GenericArgs>>]>>,
    ) -> Path {
        let generic_args = generic_args.into();
        assert_eq!(path.len(), generic_args.len());
        Path { type_anchor: None, mod_path: Interned::new(path), generic_args }
    }

    pub fn kind(&self) -> &PathKind {
        &self.mod_path.kind
    }

    pub fn type_anchor(&self) -> Option<&TypeRef> {
        self.type_anchor.as_deref()
    }

    pub fn segments(&self) -> PathSegments<'_> {
        PathSegments { segments: self.mod_path.segments(), generic_args: &self.generic_args }
    }

    pub fn mod_path(&self) -> &ModPath {
        &self.mod_path
    }

    pub fn qualifier(&self) -> Option<Path> {
        if self.mod_path.is_ident() {
            return None;
        }
        let res = Path {
            type_anchor: self.type_anchor.clone(),
            mod_path: Interned::new(ModPath::from_segments(
                self.mod_path.kind,
                self.mod_path.segments()[..self.mod_path.segments().len() - 1].iter().cloned(),
            )),
            generic_args: self.generic_args[..self.generic_args.len() - 1].to_vec().into(),
        };
        Some(res)
    }

    pub fn is_self_type(&self) -> bool {
        self.type_anchor.is_none() && *self.generic_args == [None] && self.mod_path.is_Self()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PathSegment<'a> {
    pub name: &'a Name,
    pub args_and_bindings: Option<&'a GenericArgs>,
}

pub struct PathSegments<'a> {
    segments: &'a [Name],
    generic_args: &'a [Option<Interned<GenericArgs>>],
}

impl<'a> PathSegments<'a> {
    pub const EMPTY: PathSegments<'static> = PathSegments { segments: &[], generic_args: &[] };
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    pub fn len(&self) -> usize {
        self.segments.len()
    }
    pub fn first(&self) -> Option<PathSegment<'a>> {
        self.get(0)
    }
    pub fn last(&self) -> Option<PathSegment<'a>> {
        self.get(self.len().checked_sub(1)?)
    }
    pub fn get(&self, idx: usize) -> Option<PathSegment<'a>> {
        assert_eq!(self.segments.len(), self.generic_args.len());
        let res = PathSegment {
            name: self.segments.get(idx)?,
            args_and_bindings: self.generic_args.get(idx).unwrap().as_ref().map(|it| &**it),
        };
        Some(res)
    }
    pub fn skip(&self, len: usize) -> PathSegments<'a> {
        assert_eq!(self.segments.len(), self.generic_args.len());
        PathSegments { segments: &self.segments[len..], generic_args: &self.generic_args[len..] }
    }
    pub fn take(&self, len: usize) -> PathSegments<'a> {
        assert_eq!(self.segments.len(), self.generic_args.len());
        PathSegments { segments: &self.segments[..len], generic_args: &self.generic_args[..len] }
    }
    pub fn iter(&self) -> impl Iterator<Item = PathSegment<'a>> {
        self.segments.iter().zip(self.generic_args.iter()).map(|(name, args)| PathSegment {
            name,
            args_and_bindings: args.as_ref().map(|it| &**it),
        })
    }
}

impl GenericArgs {
    pub(crate) fn from_ast(
        lower_ctx: &LowerCtx<'_>,
        node: ast::GenericArgList,
    ) -> Option<GenericArgs> {
        lower::lower_generic_args(lower_ctx, node)
    }

    pub(crate) fn empty() -> GenericArgs {
        GenericArgs {
            args: Vec::new(),
            has_self_type: false,
            bindings: Vec::new(),
            desugared_from_fn: false,
        }
    }
}

impl From<Name> for Path {
    fn from(name: Name) -> Path {
        Path {
            type_anchor: None,
            mod_path: Interned::new(ModPath::from_segments(PathKind::Plain, iter::once(name))),
            generic_args: Box::new([None]),
        }
    }
}

impl From<Name> for Box<Path> {
    fn from(name: Name) -> Box<Path> {
        Box::new(Path::from(name))
    }
}
