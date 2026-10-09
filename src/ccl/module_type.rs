//! Module types: the type of a module's public members, `Module{…}`
//! (`docs/chl-spec.md`, "9.8 Module types").
//!
//! A Module type is not a [`Type`]. No value has one: a module is a value only
//! as an argument or a binding, and a Module-typed parameter lowers to a `let`
//! per entry, of the argument's member at the entry's type (`docs/modules.md`,
//! "Module types are not value types"). A type alias names a [`Type`] or a
//! Module type, which is what [`AliasType`] holds.

use crate::ccl::Type;
use crate::ccl::chl_print::chl_type;
use smol_str::SmolStr;
use std::fmt;
use std::rc::Rc;

/// The public members a Module type names, each with its type, in the order
/// written.
#[derive(Debug, Clone, PartialEq)]
pub struct ModuleType {
    pub entries: Vec<ModuleEntry>,
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
                for entry in &mut Rc::make_mut(module).entries {
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
}

/// `Module{events: Feed(Event), charge: Int => Receipt}`.
impl fmt::Display for ModuleType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Module{")?;
        for (i, entry) in self.entries.iter().enumerate() {
            if i > 0 {
                f.write_str(", ")?;
            }
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
