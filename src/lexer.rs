use crate::Error;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tok {
    Name(String),
    Kw(Kw),
    Sym(Sym),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kw {
    Let,
    Proof,
    Given,
    Have,
    Shows,
    By,
    Assume,
    Obtain,
    From,
    All,
    Import,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Sym {
    LParen,
    RParen,
    Dollar,
    Pipe,
    Hole,
    Colon,
    Equals,
    LBrace,
    RBrace,
}

#[derive(Clone, Debug)]
pub struct Token {
    pub tok: Tok,
    pub line: usize,
}

pub fn lex(src: &str) -> Result<Vec<Token>, Error> {
    let chars: Vec<char> = src.chars().collect();
    let at = |i: usize, c: char| chars.get(i) == Some(&c);
    let name_char = |c: char| c.is_alphanumeric() || c == '_' || c == '\'';
    let (mut i, mut line, mut out) = (0, 1, Vec::new());
    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() {
            if c == '\n' {
                line += 1;
            }
            i += 1;
            continue;
        }
        // Nestable comments.
        if c == '{' && at(i + 1, '-') {
            let opened = line;
            let mut depth = 0;
            loop {
                if i >= chars.len() {
                    return Err(Error::new(opened, "unclosed comment `{-`"));
                }
                if chars[i] == '{' && at(i + 1, '-') {
                    depth += 1;
                    i += 2;
                } else if chars[i] == '-' && at(i + 1, '}') {
                    depth -= 1;
                    i += 2;
                    if depth == 0 {
                        break;
                    }
                } else {
                    if chars[i] == '\n' {
                        line += 1;
                    }
                    i += 1;
                }
            }
            continue;
        }
        if c.is_alphabetic() {
            let start = i;
            while i < chars.len() && name_char(chars[i]) {
                i += 1;
            }
            let word: String = chars[start..i].iter().collect();
            let tok = match word.as_str() {
                "let" => Tok::Kw(Kw::Let),
                "proof" => Tok::Kw(Kw::Proof),
                "given" => Tok::Kw(Kw::Given),
                "have" => Tok::Kw(Kw::Have),
                "shows" => Tok::Kw(Kw::Shows),
                "by" => Tok::Kw(Kw::By),
                "assume" => Tok::Kw(Kw::Assume),
                "obtain" => Tok::Kw(Kw::Obtain),
                "from" => Tok::Kw(Kw::From),
                "all" => Tok::Kw(Kw::All),
                "import" => Tok::Kw(Kw::Import),
                _ => Tok::Name(word),
            };
            out.push(Token { tok, line });
            continue;
        }
        let (sym, len) = match c {
            '(' => (Sym::LParen, 1),
            ')' => (Sym::RParen, 1),
            '$' => (Sym::Dollar, 1),
            ':' => (Sym::Colon, 1),
            '=' => (Sym::Equals, 1),
            '{' => (Sym::LBrace, 1),
            '}' => (Sym::RBrace, 1),
            '|' if at(i + 1, '>') => (Sym::Pipe, 2),
            '_' if chars.get(i + 1).is_some_and(|&n| name_char(n)) => {
                return Err(Error::new(line, "names must start with a letter"));
            }
            '_' => (Sym::Hole, 1),
            '.' => return Err(Error::new(line, "`.` is reserved for qualified names")),
            '-' if at(i + 1, '}') => return Err(Error::new(line, "`-}` without a matching `{-`")),
            _ => return Err(Error::new(line, format!("unexpected character `{c}`"))),
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
        let ts = lex("proof p\n  shows imp A A $ x' |> f _").unwrap();
        assert_eq!(ts[0].tok, Tok::Kw(Kw::Proof));
        assert_eq!(ts[2].tok, Tok::Kw(Kw::Shows));
        assert_eq!(ts[2].line, 2);
        assert!(ts.iter().any(|t| t.tok == Tok::Name("x'".into())));
        assert!(ts.iter().any(|t| t.tok == Tok::Sym(Sym::Pipe)));
        assert!(ts.iter().any(|t| t.tok == Tok::Sym(Sym::Hole)));
    }

    #[test]
    fn nested_comments() {
        assert_eq!(toks("a {- x {- y -} z -} b"), [Tok::Name("a".into()), Tok::Name("b".into())]);
        let e = lex("a\n{- x {- y -}\n").unwrap_err();
        assert_eq!((e.line, e.msg.as_str()), (2, "unclosed comment `{-`"));
    }

    #[test]
    fn rejected_characters() {
        assert_eq!(lex("A.B").unwrap_err().msg, "`.` is reserved for qualified names");
        assert_eq!(lex("_x").unwrap_err().msg, "names must start with a letter");
        assert_eq!(lex("a -} b").unwrap_err().msg, "`-}` without a matching `{-`");
    }
}
