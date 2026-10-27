//! `hailperin fmt`: the file printed in its canonical layout. One item per line, one
//! indentation level per block, `by` in one column per segment, and nothing else. The source's
//! own line breaks and spacing are forgotten; comments keep their place, before the item they
//! precede or at the end of the line they trail.

use crate::lexer::{lex, Kw, Sym, Tok, Token};
use crate::Error;

#[derive(Clone, Debug)]
pub struct Options {
    /// Spaces per level of nesting.
    pub indent: usize,
    /// Pad `by` to one column per segment, or leave one space before it.
    pub pad: bool,
    /// The column is shared by the whole theorem, not only by each segment.
    pub theorem_wide: bool,
}

impl Default for Options {
    fn default() -> Self {
        Options { indent: 2, pad: true, theorem_wide: false }
    }
}

/// One line of output: the tokens of one item, with the comments that belong to it.
struct Item {
    toks: Vec<Tok>,
    first_line: usize,
    last_line: usize,
    /// Nesting depth, for indentation.
    depth: usize,
    /// The segment the item's `by` aligns with, if it has one. A segment is a run of steps in
    /// one block that no lemma interrupts. A `therefore` stands alone.
    group: Option<usize>,
}

/// A comment: its line, its text from `--` on, and whether tokens precede it on its line.
struct Comment {
    line: usize,
    text: String,
    trailing: bool,
}

pub fn format(src: &str, opts: &Options) -> Result<String, Error> {
    let toks = lex(src)?;
    let comments = comments(src);
    let items = items(&toks, opts.theorem_wide);
    let mut out = String::new();
    let mut next_comment = 0;
    let mut prev_top_level = false;
    // The `by` column of each group.
    let columns = columns(&items, opts);
    for (k, it) in items.iter().enumerate() {
        let top = it.depth == 0;
        // Comments on their own lines before this item.
        let mut pending: Vec<&Comment> = Vec::new();
        while next_comment < comments.len() && comments[next_comment].line < it.first_line {
            let c = &comments[next_comment];
            next_comment += 1;
            if !c.trailing {
                pending.push(c);
            }
        }
        // A blank line between top-level items, except inside a run of declarations,
        // definitions or imports.
        let same_run = k > 0 && top && matches!((&items[k - 1].toks[0], &it.toks[0]), (Tok::Kw(a), Tok::Kw(b)) if a == b && matches!(a, Kw::Predicate | Kw::Define | Kw::Import));
        if k > 0 && !same_run && (top || prev_top_level && !pending.is_empty()) {
            out.push('\n');
        }
        let indent = " ".repeat(it.depth * opts.indent);
        for c in pending {
            out.push_str(&indent);
            out.push_str(&c.text);
            out.push('\n');
        }
        out.push_str(&indent);
        out.push_str(&render(it, it.group.map(|g| columns[g]), opts));
        // Comments trailing any of the item's lines.
        while next_comment < comments.len() && comments[next_comment].line <= it.last_line {
            let c = &comments[next_comment];
            next_comment += 1;
            if c.trailing {
                out.push_str("  ");
                out.push_str(&c.text);
            } else {
                // An own-line comment inside a multi-line item goes after it, on its own line.
                out.push('\n');
                out.push_str(&indent);
                out.push_str(&c.text);
            }
        }
        out.push('\n');
        prev_top_level = top;
    }
    let mut first = true;
    for c in &comments[next_comment..] {
        if first && !items.is_empty() {
            out.push('\n');
        }
        first = false;
        out.push_str(&c.text);
        out.push('\n');
    }
    Ok(out)
}

fn comments(src: &str) -> Vec<Comment> {
    let mut out = Vec::new();
    for (i, line) in src.lines().enumerate() {
        if let Some(p) = line.find("--") {
            out.push(Comment { line: i + 1, text: line[p..].trim_end().to_string(), trailing: !line[..p].trim().is_empty() });
        }
    }
    out
}

const STARTERS: [Kw; 8] = [Kw::Theorem, Kw::Lemma, Kw::Define, Kw::Import, Kw::Predicate, Kw::Variable, Kw::Assume, Kw::Therefore];
const TOP: [Kw; 3] = [Kw::Theorem, Kw::Define, Kw::Import];

/// Cuts the token stream into items and assigns each its depth and alignment group.
fn items(toks: &[Token], theorem_wide: bool) -> Vec<Item> {
    // Item boundaries: a starting keyword, or a label (lowercase name, colon) that is not the
    // name right after `assume`, `theorem` or `lemma`.
    let mut starts = Vec::new();
    for (i, t) in toks.iter().enumerate() {
        let starts_here = match &t.tok {
            Tok::Kw(k) if STARTERS.contains(k) => true,
            Tok::Lower(_) => {
                let colon = matches!(toks.get(i + 1).map(|t| &t.tok), Some(Tok::Sym(Sym::Colon)));
                let named = i > 0 && matches!(toks[i - 1].tok, Tok::Kw(Kw::Assume | Kw::Theorem | Kw::Lemma));
                colon && !named
            }
            _ => false,
        };
        if starts_here || i == 0 {
            starts.push(i);
        }
    }
    starts.dedup();
    let mut items = Vec::new();
    // The blocks enclosing the next item, outermost first, each with its open segment.
    let mut stack: Vec<Option<usize>> = Vec::new();
    let mut segments = 0;
    for (n, &s) in starts.iter().enumerate() {
        let e = starts.get(n + 1).copied().unwrap_or(toks.len());
        let toks_here: Vec<Tok> = toks[s..e].iter().map(|t| t.tok.clone()).collect();
        let (first_line, last_line) = (toks[s].line, toks[e - 1].line);
        let head = match &toks_here[0] {
            Tok::Kw(k) => Some(*k),
            _ => None,
        };
        if head.is_some_and(|k| TOP.contains(&k)) {
            stack.clear();
        }
        let depth = stack.len();
        let step = toks_here.contains(&Tok::Kw(Kw::By)) && head != Some(Kw::Therefore);
        let at = if theorem_wide { stack.first_mut() } else { stack.last_mut() };
        let mut item_group = None;
        if let (true, Some(seg)) = (step, at) {
            item_group = Some(*seg.get_or_insert_with(|| {
                segments += 1;
                segments - 1
            }));
        }
        items.push(Item { toks: toks_here, first_line, last_line, depth, group: item_group });
        match head {
            Some(Kw::Theorem) | Some(Kw::Lemma) => stack.push(None),
            Some(Kw::Therefore) => {
                stack.pop();
                // The steps after a lemma start a new segment.
                if let (false, Some(seg)) = (theorem_wide, stack.last_mut()) {
                    *seg = None;
                }
            }
            _ => {}
        }
    }
    items
}

/// The `by` column of each segment: one past the longest text before `by` in it.
fn columns(items: &[Item], opts: &Options) -> Vec<usize> {
    let n = items.iter().filter_map(|i| i.group).max().map_or(0, |g| g + 1);
    let mut cols = vec![0; n];
    for it in items {
        if let Some(g) = it.group {
            let (before, _) = split_by(&it.toks);
            let width = it.depth * opts.indent + render_toks(before).len();
            cols[g] = cols[g].max(width + 1);
        }
    }
    cols
}

fn split_by(toks: &[Tok]) -> (&[Tok], &[Tok]) {
    match toks.iter().position(|t| *t == Tok::Kw(Kw::By)) {
        Some(p) => (&toks[..p], &toks[p..]),
        None => (toks, &[]),
    }
}

fn render(it: &Item, column: Option<usize>, opts: &Options) -> String {
    let (before, after) = split_by(&it.toks);
    let mut s = render_toks(before);
    if !after.is_empty() {
        let here = it.depth * opts.indent + s.len();
        let pad = match column {
            Some(c) if opts.pad => c.saturating_sub(here).max(1),
            _ => 1,
        };
        s.push_str(&" ".repeat(pad));
        s.push_str(&render_toks(after));
    }
    s
}

/// Tokens joined with spaces, except around punctuation: none before `:`, `)` and `.`, none
/// after `(`, and none after the `.` of a theory member `T.m`.
fn render_toks(toks: &[Tok]) -> String {
    let mut s = String::new();
    for (i, t) in toks.iter().enumerate() {
        let prev = if i > 0 { Some(&toks[i - 1]) } else { None };
        let space = match (prev, t) {
            (None, _) => false,
            (_, Tok::Sym(Sym::Colon | Sym::RParen | Sym::Dot)) => false,
            (Some(Tok::Sym(Sym::LParen)), _) => false,
            (Some(Tok::Sym(Sym::Dot)), _) => !matches!(toks.get(i.wrapping_sub(2)), Some(Tok::Upper(_))),
            _ => true,
        };
        if space {
            s.push(' ');
        }
        s.push_str(&text(t));
    }
    s
}

fn text(t: &Tok) -> String {
    match t {
        Tok::Upper(n) | Tok::Lower(n) | Tok::Path(n) => n.clone(),
        Tok::Kw(k) => crate::lexer::KEYWORDS.iter().find(|(_, kw)| kw == k).map(|(w, _)| (*w).to_string()).unwrap_or_default(),
        Tok::Sym(s) => match s {
            Sym::LParen => "(".into(),
            Sym::RParen => ")".into(),
            Sym::Colon => ":".into(),
            Sym::Dot => ".".into(),
            Sym::Arrow => "->".into(),
            Sym::Equals => "=".into(),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fmt(src: &str) -> String {
        format(src, &Options::default()).unwrap()
    }

    #[test]
    fn blocks_indent_and_by_aligns_per_segment() {
        // The steps before a lemma, the lemma's, and the steps after it are three segments, and
        // each `therefore` stands alone.
        let src = "theorem t:\npredicate A\nassume a: A\ns: A by reit a\nlonger: A and A by and_i a a\nlemma l:\nassume b: A\n k: A by reit b\n kk: A and A and A by and_i b b b\n therefore A -> A and A and A\n-- done\nm: A by reit a\ntherefore A\n";
        let want = "theorem t:\n  predicate A\n  assume a: A\n  s: A            by reit a\n  longer: A and A by and_i a a\n  lemma l:\n    assume b: A\n    k: A              by reit b\n    kk: A and A and A by and_i b b b\n    therefore A -> A and A and A\n  -- done\n  m: A by reit a\n  therefore A\n";
        assert_eq!(fmt(src), want);
    }

    #[test]
    fn definitions_assumptions_comments_and_spacing() {
        let src = "define X = A\ndefine Ax (P x) = forall x.\nP x  -- all\ntheorem u:\nassume ax: Ax Q\nk: forall x. Q x by reit ax\ntherefore Ax Q -> forall x. Q x\n";
        let want = "define X = A\ndefine Ax (P x) = forall x. P x  -- all\n\ntheorem u:\n  assume ax: Ax Q\n  k: forall x. Q x by reit ax\n  therefore Ax Q -> forall x. Q x\n";
        assert_eq!(fmt(src), want);
    }

    #[test]
    fn one_space_and_theorem_wide() {
        let src = "theorem t:\npredicate A\nassume a: A\ns: A by reit a\nlemma l:\nassume b: A\nkk: A and A and A by and_i b b b\ntherefore A -> A and A and A\nm: A by reit a\ntherefore A\n";
        let space = format(src, &Options { pad: false, ..Options::default() }).unwrap();
        assert_eq!(space, "theorem t:\n  predicate A\n  assume a: A\n  s: A by reit a\n  lemma l:\n    assume b: A\n    kk: A and A and A by and_i b b b\n    therefore A -> A and A and A\n  m: A by reit a\n  therefore A\n");
        let wide = format(src, &Options { theorem_wide: true, ..Options::default() }).unwrap();
        assert_eq!(wide, "theorem t:\n  predicate A\n  assume a: A\n  s: A                by reit a\n  lemma l:\n    assume b: A\n    kk: A and A and A by and_i b b b\n    therefore A -> A and A and A\n  m: A                by reit a\n  therefore A\n");
    }

    #[test]
    fn declarations_stay_together() {
        assert_eq!(fmt("import a\nimport b\npredicate P x\n\npredicate Q\ndefine X = Q\n"), "import a\nimport b\n\npredicate P x\npredicate Q\n\ndefine X = Q\n");
        assert_eq!(fmt("define X = Q\n\ndefine Y = X\ntheorem t:\n assume x: X\n therefore X -> X\n"), "define X = Q\ndefine Y = X\n\ntheorem t:\n  assume x: X\n  therefore X -> X\n");
    }

    #[test]
    fn whitespace_in_the_source_is_forgotten() {
        let a = fmt("theorem t:\n  predicate A\n  assume a: A\n  therefore A -> A\n");
        let b = fmt("theorem t: predicate A assume a:\n\n   A therefore\nA ->\n A");
        assert_eq!(a, b);
    }
}
