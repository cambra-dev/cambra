//! The files one compilation reads, and the diagnostic rendering that labels
//! spans in them.
//!
//! A [`Span`](super::ast::Span) names its file by [`FileId`], an index into the
//! compilation's [`SourceMap`]. Rendering a diagnostic fetches each label's
//! file from the map, so one report can label spans in several files.

use std::sync::{Arc, OnceLock};

/// One file of a compilation: an index into that compilation's [`SourceMap`].
///
/// Meaningful only within the compilation whose map minted it, except
/// [`FileId::ROOT`], which is every map's root. Anything that outlives a
/// compilation names the file by path.
// Wire shape (inspector): a bare number, the index.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize)]
#[serde(transparent)]
pub struct FileId(u32);

impl FileId {
    /// The root of every [`SourceMap`]: the first file added. A one-file parse
    /// names its file by it without building a map, and the spans of two maps'
    /// roots compare equal.
    pub const ROOT: FileId = FileId(0);
}

/// One file of a [`SourceMap`].
#[derive(Debug, Clone)]
struct SourceFile {
    /// The name diagnostics show for the file.
    path: String,
    text: Arc<str>,
    /// The file's newline index, built the first time a diagnostic renders a
    /// span in it.
    lines: OnceLock<ariadne::Source<Arc<str>>>,
}

/// Every file one compilation reads, by [`FileId`].
///
/// The first file added is the compilation's root.
#[derive(Debug, Clone, Default)]
pub struct SourceMap {
    files: Vec<SourceFile>,
}

impl SourceMap {
    /// A map holding one file, its root.
    pub fn single(path: impl Into<String>, text: impl AsRef<str>) -> Self {
        let mut sources = SourceMap::default();
        sources.add(path, text);
        sources
    }

    /// Add a file and return the id its spans carry.
    pub fn add(&mut self, path: impl Into<String>, text: impl AsRef<str>) -> FileId {
        let id = FileId(
            u32::try_from(self.files.len()).expect("a compilation reads fewer than 2^32 files"),
        );
        self.files.push(SourceFile {
            path: path.into(),
            text: Arc::from(text.as_ref()),
            lines: OnceLock::new(),
        });
        id
    }

    /// The compilation's root: the first file added, [`FileId::ROOT`].
    pub fn root(&self) -> FileId {
        assert!(
            !self.files.is_empty(),
            "a SourceMap with no files has no root"
        );
        FileId::ROOT
    }

    /// The name diagnostics show for `file`.
    pub fn path(&self, file: FileId) -> &str {
        &self.file(file).path
    }

    /// The source text of `file`. Every span in it is a byte range of this
    /// string.
    pub fn text(&self, file: FileId) -> &str {
        &self.file(file).text
    }

    fn file(&self, file: FileId) -> &SourceFile {
        self.files
            .get(file.0 as usize)
            .unwrap_or_else(|| panic!("{file:?} is not a file of this SourceMap"))
    }
}

/// The ariadne configuration every diagnostic renders with.
///
/// A [`Span`](super::ast::Span) holds byte offsets, and ariadne reads offsets
/// as character indices unless told otherwise, which misplaces every label
/// after a multi-byte character. The report builders apply it themselves and
/// take only the colour, so no caller can build a report without it.
pub fn report_config(color: bool) -> ariadne::Config {
    ariadne::Config::default()
        .with_color(color)
        .with_index_type(ariadne::IndexType::Byte)
}

/// The source cache a report renders against: each label's [`FileId`] fetches
/// its file.
impl ariadne::Cache<FileId> for &SourceMap {
    type Storage = Arc<str>;

    fn fetch(
        &mut self,
        id: &FileId,
    ) -> Result<&ariadne::Source<Arc<str>>, Box<dyn std::fmt::Debug + '_>> {
        let file = self.file(*id);
        Ok(file
            .lines
            .get_or_init(|| ariadne::Source::from(Arc::clone(&file.text))))
    }

    fn display<'a>(&self, id: &'a FileId) -> Option<Box<dyn std::fmt::Display + 'a>> {
        Some(Box::new(self.path(*id).to_owned()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Span;
    use ariadne::{Label, Report, ReportKind};

    fn render(sources: &SourceMap, report: Report<'_, Span>) -> String {
        let mut buf = Vec::new();
        report.write(sources, &mut buf).expect("write to a Vec");
        String::from_utf8(buf).expect("ariadne writes UTF-8")
    }

    #[test]
    fn a_report_labels_spans_in_two_files() {
        let mut sources = SourceMap::default();
        let lib = sources.add("lib.cambra", "pub limit = 10\n");
        let user = sources.add("user.cambra", "x = lib.limit + \"a\"\n");
        let report = Report::build(ReportKind::Error, user, 4)
            .with_config(report_config(false))
            .with_message("mismatch")
            .with_label(Label::new(Span::new(user, 4, 13)).with_message("used here"))
            .with_label(Label::new(Span::new(lib, 4, 9)).with_message("declared here"))
            .finish();
        let out = render(&sources, report);
        assert!(out.contains("user.cambra:1:5"), "{out}");
        assert!(out.contains("lib.cambra:1:5"), "{out}");
        assert!(
            out.contains("used here") && out.contains("declared here"),
            "{out}"
        );
    }

    /// A label after a multi-byte character underlines the bytes its span names,
    /// and the header counts the column in characters.
    #[test]
    fn a_label_after_a_multibyte_character_points_at_its_bytes() {
        let text = "s = \"é\" + 1\n";
        let sources = SourceMap::single("main.cambra", text);
        let file = sources.root();
        let start = text.find('1').expect("present");
        let report = Report::build(ReportKind::Error, file, start)
            .with_config(report_config(false))
            .with_message("m")
            .with_label(Label::new(Span::new(file, start, start + 1)).with_message("here"))
            .finish();
        let out = render(&sources, report);
        assert!(out.contains("main.cambra:1:11"), "{out}");
    }
}
