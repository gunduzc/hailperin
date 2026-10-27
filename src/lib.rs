pub mod check;
pub mod fmt;
pub mod kernel;
pub mod lexer;
pub mod parse;
pub mod print;

use std::collections::BTreeMap;
use std::fmt as stdfmt;
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

impl stdfmt::Display for Error {
    fn fmt(&self, f: &mut stdfmt::Formatter) -> stdfmt::Result {
        if let Some(file) = &self.file {
            write!(f, "{file}: ")?;
        }
        write!(f, "line {}: {}", self.line, self.msg)
    }
}

/// What `verify_in` reports for each item of the checked file, as soon as it is checked: the
/// item, and the theorem's name and conclusion if it is a theorem.
pub type Report<'a> = &'a mut dyn FnMut(&parse::Item, Option<&(String, kernel::formula::Formula)>);

/// Checks `src`, whose imports are found in `dir`. `path` is the file's own path, if it has
/// one, so that importing it back is caught as a cycle.
pub fn verify_in(src: &str, dir: &Path, path: Option<&Path>, report: Report) -> Result<(), Error> {
    let mut l = loader(path, dir)?;
    l.source(src, dir, report).map(drop)
}

/// Checks a whole file, returning each theorem's name and conclusion in order.
pub fn verify(src: &str) -> Result<Vec<(String, kernel::formula::Formula)>, Error> {
    let mut proved = Vec::new();
    verify_in(src, Path::new("."), None, &mut |_, p| proved.extend(p.cloned()))?;
    Ok(proved)
}

/// Checks a file and returns, for each line of each theorem, its variables in scope, its
/// open assumptions and its formula.
pub fn explain_in(src: &str, dir: &Path, path: Option<&Path>) -> Result<Vec<String>, Error> {
    let mut l = loader(path, dir)?;
    l.checker.explain = true;
    l.source(src, dir, &mut |_, _| {})?;
    Ok(l.checker.take_trace())
}

fn loader(path: Option<&Path>, dir: &Path) -> Result<Loader, Error> {
    crate::print::clear_folds();
    let root = dir.canonicalize().unwrap_or_else(|_| dir.to_path_buf());
    let mut l = Loader { checker: check::Checker::default(), done: BTreeMap::new(), open: Vec::new(), root };
    if let Some(p) = path {
        let p = p.canonicalize().map_err(|e| Error::new(1, format!("can't read this file: {e}")))?;
        let name = p.file_stem().map_or(String::new(), |s| s.to_string_lossy().into_owned());
        l.open.push((p, name));
    }
    Ok(l)
}

/// Imports are checked once each, in order, and each file sees only what it imports; a file
/// can't import itself, even indirectly.
struct Loader {
    checker: check::Checker,
    /// The files checked, with the files each sees.
    done: BTreeMap<PathBuf, Vec<usize>>,
    /// The files being imported, outermost first, with their names.
    open: Vec<(PathBuf, String)>,
    /// The checked file's directory, which messages name imported files from.
    root: PathBuf,
}

impl Loader {
    /// Checks a file after its imports. It sees what they see, and itself: the files it
    /// sees, in the order it would load them alone, are returned.
    fn source(&mut self, src: &str, dir: &Path, report: Report) -> Result<Vec<usize>, Error> {
        let file = parse::parse(&lexer::lex(src)?)?;
        let mut sees = Vec::new();
        for import in &file.imports {
            for f in self.import(dir, import)? {
                if !sees.contains(&f) {
                    sees.push(f);
                }
            }
        }
        let name = self.open.last().map_or_else(String::new, |(p, _)| self.shown(p));
        sees.push(self.checker.add_file(name));
        self.checker.enter(sees.clone());
        for item in &file.items {
            let proved = self.checker.item(item)?;
            report(item, proved.as_ref());
        }
        Ok(sees)
    }

    /// A file as messages name it: its path from the checked file's directory.
    fn shown(&self, path: &Path) -> String {
        path.strip_prefix(&self.root).unwrap_or(path).to_string_lossy().into_owned()
    }

    /// Checks an imported file once, and returns the files it sees.
    fn import(&mut self, dir: &Path, import: &parse::Import) -> Result<Vec<usize>, Error> {
        let name = &import.name;
        let err = |msg: String| Error::new(import.line, msg);
        let path = dir.join(format!("{name}.hai"));
        let canon = path.canonicalize().map_err(|e| err(format!("can't import `{name}`: {e}")))?;
        if let Some(i) = self.open.iter().position(|(p, _)| *p == canon) {
            let mut cycle: Vec<&str> = self.open[i..].iter().map(|(_, n)| n.as_str()).collect();
            cycle.push(name);
            return Err(err(format!("import cycle: {}", cycle.join(" -> "))));
        }
        if let Some(sees) = self.done.get(&canon) {
            return Ok(sees.clone());
        }
        let src = std::fs::read_to_string(&canon).map_err(|e| err(format!("can't import `{name}`: {e}")))?;
        self.open.push((canon.clone(), name.clone()));
        // The import's own imports are next to it, wherever a symlink pointed to it from.
        let here = canon.parent().unwrap_or(dir);
        // An imported file's lines are not explained: only the file being checked.
        let explain = std::mem::replace(&mut self.checker.explain, false);
        let shown = self.shown(&canon);
        let res = self.source(&src, here, &mut |_, _| {}).map_err(|mut e| {
            e.file.get_or_insert(shown);
            e
        });
        self.checker.explain = explain;
        let sees = res?;
        self.open.pop();
        self.done.insert(canon, sees.clone());
        Ok(sees)
    }
}
