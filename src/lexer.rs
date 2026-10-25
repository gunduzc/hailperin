//! Tokens. A file is ASCII. A name is a letter, then letters, digits and single underscores
//! between them. Comments are `{- ... -}` and nest. Whitespace separates tokens and does
//! nothing else.

use crate::Error;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tok {
    /// A name starting with an uppercase letter: a predicate, definition or theory.
    Upper(String),
    /// A name starting with a lowercase letter: a variable, label, theorem or rule.
    Lower(String),
    Kw(Kw),
    Sym(Sym),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kw {
    Theorem,
    Theory,
    Define,
    Include,
    Import,
    In,
    Assume,
    Lemma,
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
    ("theory", Kw::Theory),
    ("define", Kw::Define),
    ("include", Kw::Include),
    ("import", Kw::Import),
    ("in", Kw::In),
    ("assume", Kw::Assume),
    ("lemma", Kw::Lemma),
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
        // Nestable comments.
        if c == b'{' && at(i + 1, b'-') {
            let opened = line;
            let mut depth = 0;
            loop {
                if i >= bytes.len() {
                    return Err(Error::new(opened, "unclosed comment `{-`"));
                }
                if !bytes[i].is_ascii() {
                    return Err(Error::new(line, "files are ASCII, and this byte isn't"));
                }
                if bytes[i] == b'{' && at(i + 1, b'-') {
                    depth += 1;
                    i += 2;
                } else if bytes[i] == b'-' && at(i + 1, b'}') {
                    depth -= 1;
                    i += 2;
                    if depth == 0 {
                        break;
                    }
                } else {
                    if bytes[i] == b'\n' {
                        line += 1;
                    }
                    i += 1;
                }
            }
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
            b'-' if at(i + 1, b'}') => return Err(Error::new(line, "`-}` without a matching `{-`")),
            b'_' => return Err(Error::new(line, "a name starts with a letter, not `_`")),
            b'\'' => return Err(Error::new(line, "there are no primes: write `xp` or `x1`")),
            _ => return Err(Error::new(line, format!("unexpected character `{}`", c as char))),
        };
        out.push(Token { tok: Tok::Sym(sym), line });
        i += len;
    }
    Ok(out)
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
    fn nested_comments() {
        assert_eq!(toks("a {- x {- y -} z -} b"), [Tok::Lower("a".into()), Tok::Lower("b".into())]);
        let e = lex("a\n{- x {- y -}\n").unwrap_err();
        assert_eq!((e.line, e.msg.as_str()), (2, "unclosed comment `{-`"));
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
    fn rejected_characters() {
        assert_eq!(lex("a -} b").unwrap_err().msg, "`-}` without a matching `{-`");
        assert_eq!(lex("A $ B").unwrap_err().msg, "unexpected character `$`");
        assert_eq!(lex("{- caf\u{e9} -}").unwrap_err().msg, "files are ASCII, and this byte isn't");
        assert_eq!(lex("\u{2200}x").unwrap_err().msg, "files are ASCII, and this byte isn't");
    }
}
