//! Module files on disk, under the directory of the root file
//! (`docs/chl-spec.md`, "9.15 Module files").

use super::{MissingModule, ModuleFile, ModuleFiles, RootFile};
use crate::chl_parser::ModulePath;
use crate::chl_parser::module_path::{STD_ROOT, segment_error};
use smol_str::SmolStr;
use std::collections::BTreeMap;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

/// The files of a program's modules, read from its module root: the directory
/// containing the root file.
///
/// Module path `a::b::c` names `<root>/a/b/c.cambra`. Each segment must match a
/// directory entry's name exactly, so a file differing only in case is not the
/// module's, on a case-insensitive file system too.
#[derive(Debug)]
pub struct DiskFiles {
    /// The module root as the root file's path gives it, empty for a root file
    /// named without a directory.
    root: PathBuf,
    /// The module each file read so far is, by canonical path, so a file that a
    /// second module path reaches is refused.
    read: BTreeMap<PathBuf, ModulePath>,
}

impl DiskFiles {
    /// Read the root file at `path`, and open its directory as the module root.
    ///
    /// Fails when the file cannot be read, or when its name is not
    /// `<segment>.cambra` for a module path segment other than the std root's.
    pub fn open(path: &Path) -> Result<(RootFile, Self), String> {
        let shown = path.display();
        let stem = match (path.file_stem(), path.extension()) {
            (Some(stem), Some(extension)) if extension == "cambra" => stem
                .to_str()
                .ok_or_else(|| format!("the root file `{shown}` has a name that is not UTF-8"))?,
            _ => return Err(format!("the root file `{shown}` is not a `.cambra` file")),
        };
        if let Some(why) = segment_error(stem) {
            return Err(format!(
                "the root file `{shown}` does not name a module: {why}"
            ));
        }
        if stem == STD_ROOT {
            return Err(format!(
                "the root file `{shown}` does not name a module: `{STD_ROOT}` is the std root"
            ));
        }
        let text = fs::read_to_string(path).map_err(|e| format!("cannot read `{shown}`: {e}"))?;
        let canonical =
            fs::canonicalize(path).map_err(|e| format!("cannot read `{shown}`: {e}"))?;

        let module = ModulePath::new([SmolStr::from(stem)]);
        let files = DiskFiles {
            root: path.parent().map(Path::to_path_buf).unwrap_or_default(),
            read: BTreeMap::from([(canonical, module.clone())]),
        };
        let root = RootFile {
            path: shown.to_string(),
            module: Some(module),
            text,
        };
        Ok((root, files))
    }

    /// Where `relative`, a path under the module root, is on disk.
    fn on_disk(&self, relative: &Path) -> PathBuf {
        if self.root.as_os_str().is_empty() {
            Path::new(".").join(relative)
        } else {
            self.root.join(relative)
        }
    }

    /// How diagnostics name the path `relative` to the module root.
    fn shown(&self, relative: &Path) -> String {
        self.root.join(relative).display().to_string()
    }
}

impl ModuleFiles for DiskFiles {
    fn fetch(&mut self, module: &ModulePath) -> Result<ModuleFile, MissingModule> {
        let relative = PathBuf::from(module.relative_file());
        let file = self.shown(&relative);

        // Each component of the path must be an entry of its directory, spelled
        // exactly. Opening the path whole would accept `Cart.cambra` for `cart`
        // on a case-insensitive file system.
        let mut walked = PathBuf::new();
        for component in relative.iter() {
            let entries = match fs::read_dir(self.on_disk(&walked)) {
                Ok(entries) => entries,
                Err(e) if e.kind() == io::ErrorKind::NotFound => {
                    return Err(MissingModule::NoFile { file });
                }
                Err(e) => {
                    return Err(MissingModule::Unreadable {
                        file: self.shown(&walked),
                        error: e.to_string(),
                    });
                }
            };
            let names: Vec<_> = entries
                .filter_map(|entry| entry.ok().map(|entry| entry.file_name()))
                .collect();
            if !names.iter().any(|name| name == component) {
                let differs_in_case = names.iter().find(|name| {
                    name.to_str()
                        .zip(component.to_str())
                        .is_some_and(|(name, component)| name.eq_ignore_ascii_case(component))
                });
                return Err(match differs_in_case {
                    Some(name) => MissingModule::CaseMismatch {
                        file,
                        found: self.shown(&walked.join(name)),
                    },
                    None => MissingModule::NoFile { file },
                });
            }
            walked.push(component);
        }

        let unreadable = |e: io::Error| MissingModule::Unreadable {
            file: file.clone(),
            error: e.to_string(),
        };
        let path = self.on_disk(&relative);
        let canonical = fs::canonicalize(&path).map_err(unreadable)?;
        if let Some(other) = self.read.get(&canonical) {
            return Err(MissingModule::SameFile {
                file,
                module: other.clone(),
            });
        }
        let text = fs::read_to_string(&path).map_err(unreadable)?;
        self.read.insert(canonical, module.clone());
        Ok(ModuleFile { path: file, text })
    }
}
