pub mod check;
pub mod kernel;
pub mod lexer;
pub mod parse;
pub mod syntax;

use std::collections::BTreeSet;
use std::fmt;
use std::path::{Path, PathBuf};

#[derive(Clone, Debug)]
pub struct Error {
    /// The imported file the error is in; `None` for the file being checked.
    pub file: Option<String>,
    pub line: usize,
    pub msg: String,
}

impl Error {
    pub fn new(line: usize, msg: impl Into<String>) -> Self {
        Error { file: None, line, msg: msg.into() }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(file) = &self.file {
            write!(f, "{file}: ")?;
        }
        write!(f, "line {}: {}", self.line, self.msg)
    }
}

/// What `verify_in` reports for each item of the checked file, as soon as it is checked: the
/// item, and the proof's name and conclusion if it is a proof.
pub type Report<'a> = &'a mut dyn FnMut(&parse::Item, Option<&(String, syntax::Formula)>);

/// Checks `src`, whose imports are found in `dir`. `path` is the file's own path, if it has
/// one, so that importing it back is caught as a cycle.
pub fn verify_in(src: &str, dir: &Path, path: Option<&Path>, report: Report) -> Result<(), Error> {
    let mut l = Loader { checker: check::Checker::default(), done: BTreeSet::new(), open: Vec::new() };
    if let Some(p) = path {
        let p = p.canonicalize().map_err(|e| Error::new(1, format!("can't read this file: {e}")))?;
        let name = p.file_stem().map_or(String::new(), |s| s.to_string_lossy().into_owned());
        l.open.push((p, name));
    }
    l.source(src, dir, report)
}

/// Checks a whole file, returning each proof's name and conclusion in order.
pub fn verify(src: &str) -> Result<Vec<(String, syntax::Formula)>, Error> {
    let mut proved = Vec::new();
    verify_in(src, Path::new("."), None, &mut |_, p| proved.extend(p.cloned()))?;
    Ok(proved)
}

/// Imports are pasted in once each, in order; a file can't import itself, even indirectly.
struct Loader {
    checker: check::Checker,
    done: BTreeSet<PathBuf>,
    /// The files being imported, outermost first, with their names.
    open: Vec<(PathBuf, String)>,
}

impl Loader {
    fn source(&mut self, src: &str, dir: &Path, report: Report) -> Result<(), Error> {
        let file = parse::parse(&lexer::lex(src)?)?;
        for import in &file.imports {
            self.import(dir, import)?;
        }
        for item in &file.items {
            let proved = self.checker.item(item)?;
            report(item, proved.as_ref());
        }
        Ok(())
    }

    fn import(&mut self, dir: &Path, import: &parse::Import) -> Result<(), Error> {
        let name = &import.name;
        let err = |msg: String| Error::new(import.line, msg);
        let path = dir.join(format!("{name}.hai"));
        let canon = path.canonicalize().map_err(|e| err(format!("can't import `{name}`: {e}")))?;
        if let Some(i) = self.open.iter().position(|(p, _)| *p == canon) {
            let mut cycle: Vec<&str> = self.open[i..].iter().map(|(_, n)| n.as_str()).collect();
            cycle.push(name);
            return Err(err(format!("import cycle: {}", cycle.join(" → "))));
        }
        if self.done.contains(&canon) {
            return Ok(());
        }
        let src = std::fs::read_to_string(&canon).map_err(|e| err(format!("can't import `{name}`: {e}")))?;
        self.open.push((canon.clone(), name.clone()));
        // Every import is next to the file importing it, so the file name alone is unambiguous.
        self.source(&src, dir, &mut |_, _| {}).map_err(|mut e| {
            e.file.get_or_insert_with(|| format!("{name}.hai"));
            e
        })?;
        self.open.pop();
        self.done.insert(canon);
        Ok(())
    }
}
