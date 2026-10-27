//! Tokens. A file is ASCII. A name is a letter, then letters, digits and single underscores
//! between them. A comment runs from `--` to the end of its line. Whitespace separates tokens
//! and does nothing else.

use crate::Error;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tok {
    /// A name starting with an uppercase letter: a predicate, definition or theory.
    Upper(String),
    /// A name starting with a lowercase letter: a variable, label, theorem or rule.
    Lower(String),
    Kw(Kw),
    Sym(Sym),
    /// The path after `import`: names, `.` and `..`, joined by `/`.
    Path(String),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kw {
    Theorem,
    Lemma,
    Define,
    Import,
    Predicate,
    Variable,
    Assume,
    Therefore,
    By,
    Forall,
    Exists,
    And,
    Or,
    Not,
    Absurd,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Sym {
    LParen,
    RParen,
    Colon,
    Dot,
    Arrow,
    Equals,
}

impl From<Kw> for Tok {
    fn from(k: Kw) -> Tok {
        Tok::Kw(k)
    }
}

impl From<Sym> for Tok {
    fn from(s: Sym) -> Tok {
        Tok::Sym(s)
    }
}

#[derive(Clone, Debug)]
pub struct Token {
    pub tok: Tok,
    pub line: usize,
}

pub const KEYWORDS: &[(&str, Kw)] = &[
    ("theorem", Kw::Theorem),
    ("lemma", Kw::Lemma),
    ("define", Kw::Define),
    ("import", Kw::Import),
    ("predicate", Kw::Predicate),
    ("variable", Kw::Variable),
    ("assume", Kw::Assume),
    ("therefore", Kw::Therefore),
    ("by", Kw::By),
    ("forall", Kw::Forall),
    ("exists", Kw::Exists),
    ("and", Kw::And),
    ("or", Kw::Or),
    ("not", Kw::Not),
    ("absurd", Kw::Absurd),
];

pub fn keyword(word: &str) -> Option<Kw> {
    KEYWORDS.iter().find(|(w, _)| *w == word).map(|(_, k)| *k)
}

pub fn lex(src: &str) -> Result<Vec<Token>, Error> {
    let bytes = src.as_bytes();
    let at = |i: usize, c: u8| bytes.get(i) == Some(&c);
    let (mut i, mut line, mut out) = (0, 1, Vec::new());
    while i < bytes.len() {
        let c = bytes[i];
        if !c.is_ascii() {
            return Err(Error::new(line, "files are ASCII, and this byte isn't"));
        }
        if c.is_ascii_whitespace() {
            if c == b'\n' {
                line += 1;
            }
            i += 1;
            continue;
        }
        // A comment: `--` to the end of the line.
        if c == b'-' && at(i + 1, b'-') {
            while i < bytes.len() && bytes[i] != b'\n' {
                if !bytes[i].is_ascii() {
                    return Err(Error::new(line, "files are ASCII, and this byte isn't"));
                }
                i += 1;
            }
            continue;
        }
        // After `import`, everything up to whitespace is one path.
        if matches!(out.last(), Some(Token { tok: Tok::Kw(Kw::Import), .. })) {
            let start = i;
            while i < bytes.len() && !bytes[i].is_ascii_whitespace() {
                i += 1;
            }
            out.push(Token { tok: Tok::Path(path(&src[start..i], line)?), line });
            continue;
        }
        if c.is_ascii_alphabetic() {
            let start = i;
            while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                i += 1;
            }
            let word = &src[start..i];
            if word.ends_with('_') || word.contains("__") {
                return Err(Error::new(line, format!("`{word}` is not a name: an underscore needs a letter or digit after it")));
            }
            if at(i, b'\'') {
                return Err(Error::new(line, format!("`{word}'` is not a name: write `{word}p` or `{word}1` for a prime")));
            }
            let tok = match keyword(word) {
                Some(k) => Tok::Kw(k),
                None if c.is_ascii_uppercase() => Tok::Upper(word.to_string()),
                None => Tok::Lower(word.to_string()),
            };
            out.push(Token { tok, line });
            continue;
        }
        let (sym, len) = match c {
            b'(' => (Sym::LParen, 1),
            b')' => (Sym::RParen, 1),
            b':' => (Sym::Colon, 1),
            b'.' => (Sym::Dot, 1),
            b'=' => (Sym::Equals, 1),
            b'-' if at(i + 1, b'>') => (Sym::Arrow, 2),
            b'{' if at(i + 1, b'-') => return Err(Error::new(line, "comments are `--` to the end of the line, not `{- -}`")),
            b'_' => return Err(Error::new(line, "a name starts with a letter, not `_`")),
            b'\'' => return Err(Error::new(line, "there are no primes: write `xp` or `x1`")),
            _ => return Err(Error::new(line, format!("unexpected character `{}`", c as char))),
        };
        out.push(Token { tok: Tok::Sym(sym), line });
        i += len;
    }
    Ok(out)
}

/// A path to import: parts joined by `/`, each a lowercase name, `.` or `..`. Relative, so
/// a file checks the same wherever the directory it sits in is.
fn path(p: &str, line: usize) -> Result<String, Error> {
    if p.starts_with('/') {
        return Err(Error::new(line, format!("`{p}` is absolute: import by a path relative to this file")));
    }
    for part in p.split('/') {
        let name = part.bytes().next().is_some_and(|c| c.is_ascii_lowercase())
            && part.bytes().all(|c| c.is_ascii_alphanumeric() || c == b'_')
            && !part.ends_with('_')
            && !part.contains("__");
        if !(name || part == "." || part == "..") {
            return Err(Error::new(line, format!("`{p}` is not a path: each part between `/` is a lowercase name, `.` or `..`")));
        }
    }
    Ok(p.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn toks(src: &str) -> Vec<Tok> {
        lex(src).unwrap().into_iter().map(|t| t.tok).collect()
    }

    #[test]
    fn words_symbols_and_lines() {
        let ts = lex("theorem p\n  sp1: A -> B by imp_e PA.pz x").unwrap();
        assert_eq!(ts[0].tok, Tok::Kw(Kw::Theorem));
        assert_eq!(ts[1].tok, Tok::Lower("p".into()));
        assert_eq!(ts[2].line, 2);
        assert!(ts.iter().any(|t| t.tok == Tok::Sym(Sym::Arrow)));
        assert!(ts.iter().any(|t| t.tok == Tok::Upper("PA".into())));
        assert!(ts.iter().any(|t| t.tok == Tok::Sym(Sym::Dot)));
        assert!(ts.iter().any(|t| t.tok == Tok::Lower("imp_e".into())));
    }

    #[test]
    fn line_comments() {
        assert_eq!(toks("a -- x -> y\nb"), [Tok::Lower("a".into()), Tok::Lower("b".into())]);
        assert_eq!(lex("a -- c\nb").unwrap()[1].line, 2);
        assert_eq!(lex("{- old -}").unwrap_err().msg, "comments are `--` to the end of the line, not `{- -}`");
    }

    #[test]
    fn names() {
        assert_eq!(toks("plus_comm d11"), [Tok::Lower("plus_comm".into()), Tok::Lower("d11".into())]);
        assert!(lex("foo_").unwrap_err().msg.contains("underscore"));
        assert!(lex("a__b").unwrap_err().msg.contains("underscore"));
        assert_eq!(lex("_x").unwrap_err().msg, "a name starts with a letter, not `_`");
        assert!(lex("sp'").unwrap_err().msg.contains("prime"));
    }

    #[test]
    fn import_paths() {
        assert_eq!(toks("import ../fs0/syntax"), [Tok::Kw(Kw::Import), Tok::Path("../fs0/syntax".into())]);
        assert_eq!(toks("import ./pa\nimport q"), [Tok::Kw(Kw::Import), Tok::Path("./pa".into()), Tok::Kw(Kw::Import), Tok::Path("q".into())]);
        assert!(lex("import /home/pa").unwrap_err().msg.contains("absolute"));
        assert!(lex("import fs0/*").unwrap_err().msg.contains("not a path"));
        assert!(lex("import a//b").unwrap_err().msg.contains("not a path"));
        assert!(lex("import Pa").unwrap_err().msg.contains("not a path"));
    }

    #[test]
    fn rejected_characters() {
        assert_eq!(lex("a -} b").unwrap_err().msg, "unexpected character `-`");
        assert_eq!(lex("A $ B").unwrap_err().msg, "unexpected character `$`");
        assert_eq!(lex("-- caf\u{e9}").unwrap_err().msg, "files are ASCII, and this byte isn't");
        assert_eq!(lex("\u{2200}x").unwrap_err().msg, "files are ASCII, and this byte isn't");
    }
}
