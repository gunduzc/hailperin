//! `hailperin fmt`: the file with its indentation rewritten, one level per block, and nothing
//! else changed. Comments and line breaks stay where they are.

use crate::lexer::{lex, Kw, Sym, Tok, Token};
use crate::Error;

const INDENT: usize = 2;

pub fn format(src: &str) -> Result<String, Error> {
    let toks = lex(src)?;
    let n_lines = src.lines().count();
    // The indentation of each source line, by the first token on it, if any.
    let mut indent: Vec<Option<usize>> = vec![None; n_lines + 1];
    let mut blocks: Vec<String> = Vec::new();
    let mut in_theory = false;
    let mut i = 0;
    let mut last_line = 0;
    let mut line_depth = 0;
    let at_label = |toks: &[Token], i: usize| {
        matches!(toks.get(i).map(|t| &t.tok), Some(Tok::Lower(_))) && matches!(toks.get(i + 1).map(|t| &t.tok), Some(Tok::Sym(Sym::Colon)))
    };
    while i < toks.len() {
        let t = &toks[i];
        let first_on_line = t.line != last_line;
        last_line = t.line;
        // What this token starts, and the depth it sits at.
        let (starts, depth) = match &t.tok {
            Tok::Kw(Kw::Theorem) | Tok::Kw(Kw::Theory) | Tok::Kw(Kw::Define) | Tok::Kw(Kw::Import) => {
                blocks.clear();
                in_theory = matches!(t.tok, Tok::Kw(Kw::Theory));
                if let Tok::Kw(Kw::Theorem) = t.tok {
                    if let Some(Tok::Lower(name)) = toks.get(i + 1).map(|t| &t.tok) {
                        blocks.push(name.clone());
                    }
                }
                (true, 0)
            }
            Tok::Kw(Kw::Lemma) => {
                let d = blocks.len();
                if let Some(Tok::Lower(name)) = toks.get(i + 1).map(|t| &t.tok) {
                    blocks.push(name.clone());
                }
                (true, d)
            }
            Tok::Kw(Kw::Assume) | Tok::Kw(Kw::Include) => (true, blocks.len().max(usize::from(in_theory))),
            Tok::Lower(name) if at_label(&toks, i) => {
                let d = blocks.len().max(usize::from(in_theory));
                if blocks.last() == Some(name) {
                    // The result line closes its block.
                    blocks.pop();
                }
                (true, d)
            }
            Tok::Lower(_) if in_theory && first_on_line => (true, 1),
            _ => (false, blocks.len().max(usize::from(in_theory))),
        };
        if starts {
            line_depth = depth;
        }
        if first_on_line {
            let d = if starts { depth } else { line_depth + 1 };
            indent[t.line] = Some(d * INDENT);
        }
        i += 1;
    }
    // Lines without tokens, comments and blanks, take the indentation of the next line that
    // has one.
    let mut out = String::new();
    let lines: Vec<&str> = src.lines().collect();
    for (k, line) in lines.iter().enumerate() {
        let n = k + 1;
        let trimmed = line.trim();
        if trimmed.is_empty() {
            out.push('\n');
            continue;
        }
        let ind = indent[n].or_else(|| indent[n..].iter().flatten().next().copied()).unwrap_or(0);
        out.push_str(&" ".repeat(ind));
        out.push_str(trimmed);
        out.push('\n');
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blocks_indent_and_results_close() {
        let src = "theorem t\nassume a: A\nlemma l\nassume b: B\nl: B by b\n{- done -}\nt: A -> A\n  by imp_i a a\n";
        let want = "theorem t\n  assume a: A\n  lemma l\n    assume b: B\n    l: B by b\n  {- done -}\n  t: A -> A\n    by imp_i a a\n";
        assert_eq!(format(src).unwrap(), want);
    }

    #[test]
    fn theories_and_definitions() {
        let src = "define X = A\ntheory T\ninclude S\nax: forall x.\nP x\ntheorem u\nu: A by x\n";
        let want = "define X = A\ntheory T\n  include S\n  ax: forall x.\n    P x\ntheorem u\n  u: A by x\n";
        assert_eq!(format(src).unwrap(), want);
    }
}
