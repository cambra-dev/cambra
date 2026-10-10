//! Module types: the type of a module's public members, `Module{…}`
//! (`docs/chl-spec.md`, "9.8 Module types").
//!
//! A Module type is not a [`Type`]. No value has one: a module is a value only
//! as an argument or a binding, and a Module-typed parameter lowers to a `let`
//! per entry, of the argument's member at the entry's type (`docs/modules.md`,
//! "A Module type is not a `Type`"). A type alias names a [`Type`] or a
//! Module type, which is what [`AliasType`] holds.

use crate::ccl::Type;
use crate::ccl::chl_print::chl_type;
use crate::ccl::ty::TypeParam;
use smol_str::SmolStr;
use std::fmt;
use std::rc::Rc;

/// The public members a Module type names: its type members, and its other
/// members with their types, each in the order written.
#[derive(Debug, Clone, PartialEq)]
pub struct ModuleType {
    pub types: Vec<TypeEntry>,
    pub entries: Vec<ModuleEntry>,
}

/// A type member a [`ModuleType`] names.
#[derive(Debug, Clone, PartialEq)]
pub struct TypeEntry {
    pub name: SmolStr,
    pub form: TypeEntryForm,
}

/// What a [`TypeEntry`] states of its member.
#[derive(Debug, Clone, PartialEq)]
pub enum TypeEntryForm {
    /// `Name = T`: the member is `T`, and the entries after it write `T`.
    Exact(Type),
    /// `Name <: T`, or `Name: Type` with no bound: the member is some type of
    /// that kind, and the entries after it write `param` for it.
    Abstract {
        param: Rc<TypeParam>,
        bound: Option<Type>,
    },
}

impl TypeEntry {
    /// The type the entries after this one write for its member.
    pub fn written(&self) -> Type {
        match &self.form {
            TypeEntryForm::Exact(ty) => ty.clone(),
            TypeEntryForm::Abstract { param, .. } => Type::Param(Rc::clone(param)),
        }
    }
}

/// One member a [`ModuleType`] names.
#[derive(Debug, Clone, PartialEq)]
pub struct ModuleEntry {
    pub name: SmolStr,
    /// The member's type, or for a member that is a run, its Module type.
    pub ty: AliasType,
}

/// What a type alias names: a type, or a Module type.
#[derive(Debug, Clone, PartialEq)]
pub enum AliasType {
    Type(Type),
    Module(Rc<ModuleType>),
}

impl AliasType {
    /// Call `f` on each type this holds: the type, or each entry's, at every
    /// depth of Module type.
    pub fn walk_types<'a>(&'a self, f: &mut impl FnMut(&'a Type)) {
        match self {
            AliasType::Type(ty) => f(ty),
            AliasType::Module(module) => {
                for entry in &module.types {
                    match &entry.form {
                        TypeEntryForm::Exact(ty) => f(ty),
                        TypeEntryForm::Abstract { bound, .. } => {
                            if let Some(bound) = bound {
                                f(bound);
                            }
                        }
                    }
                }
                for entry in &module.entries {
                    entry.ty.walk_types(f);
                }
            }
        }
    }

    /// Mutable analog of [`walk_types`](Self::walk_types).
    pub fn walk_types_mut(&mut self, f: &mut impl FnMut(&mut Type)) {
        match self {
            AliasType::Type(ty) => f(ty),
            AliasType::Module(module) => {
                let module = Rc::make_mut(module);
                for entry in &mut module.types {
                    match &mut entry.form {
                        TypeEntryForm::Exact(ty) => f(ty),
                        TypeEntryForm::Abstract { bound, .. } => {
                            if let Some(bound) = bound {
                                f(bound);
                            }
                        }
                    }
                }
                for entry in &mut module.entries {
                    entry.ty.walk_types_mut(f);
                }
            }
        }
    }
}

impl ModuleType {
    /// The entry named `name`, if the Module type has one.
    pub fn entry(&self, name: &str) -> Option<&ModuleEntry> {
        self.entries.iter().find(|entry| entry.name == name)
    }

    /// The type member named `name`, if the Module type has one.
    pub fn type_entry(&self, name: &str) -> Option<&TypeEntry> {
        self.types.iter().find(|entry| entry.name == name)
    }
}

/// `Module{Receipt <: {id: String}, charge: Int => Receipt}`, the type members
/// first.
impl fmt::Display for ModuleType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Module{")?;
        let mut separator = "";
        for entry in &self.types {
            f.write_str(separator)?;
            separator = ", ";
            match &entry.form {
                TypeEntryForm::Exact(ty) => write!(f, "{} = {}", entry.name, chl_type(ty))?,
                TypeEntryForm::Abstract {
                    bound: Some(bound), ..
                } => write!(f, "{} <: {}", entry.name, chl_type(bound))?,
                TypeEntryForm::Abstract { bound: None, .. } => {
                    write!(f, "{}: Type", entry.name)?;
                }
            }
        }
        for entry in &self.entries {
            f.write_str(separator)?;
            separator = ", ";
            write!(f, "{}: {}", entry.name, entry.ty)?;
        }
        f.write_str("}")
    }
}

impl fmt::Display for AliasType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AliasType::Type(ty) => f.write_str(&chl_type(ty)),
            AliasType::Module(module) => write!(f, "{module}"),
        }
    }
}
