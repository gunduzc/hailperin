//! `hailperin fmt`: the file printed in its canonical layout. One item per line, one
//! indentation level per block, `by` in one column per segment, and nothing else. The source's
//! own line breaks are kept, its spacing and indentation forgotten: a continuation line is
//! indented a fixed amount past its item. Comments keep their place, before the item they
//! precede or at the end of the line they trail. With a width, longer lines are broken too.

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
    /// Spaces a continuation line is indented past its item.
    pub continuation: usize,
    /// Lines longer than this are broken: before `by` first, then before an operator.
    pub width: Option<usize>,
}

impl Default for Options {
    fn default() -> Self {
        Options { indent: 2, pad: true, theorem_wide: false, continuation: 4, width: None }
    }
}

/// One item: the tokens of one declaration, step or `therefore`, line by line.
struct Item {
    /// Each output line: the source line it comes from, and its tokens.
    lines: Vec<(usize, Vec<Tok>)>,
    first_line: usize,
    /// Nesting depth, for indentation.
    depth: usize,
    /// The segment the item's `by` aligns with, if it has one. A segment is a run of steps in
    /// one block that no lemma interrupts. A `therefore` stands alone.
    group: Option<usize>,
    /// A token of the first line padded to start at a column its group shares, from the
    /// line's start: a definition's `=`, or the formula after a label.
    align: Option<(usize, usize)>,
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
    // Whether the source has a blank line strictly between two lines.
    let blanks: Vec<usize> = src.lines().enumerate().filter(|(_, l)| l.trim().is_empty()).map(|(i, _)| i + 1).collect();
    let blank_between = |a: usize, b: usize| blanks.iter().any(|&l| a < l && l < b);
    let mut items = items(&toks, opts.theorem_wide);
    if opts.pad {
        align_columns(&mut items, &blank_between);
    }
    if let Some(width) = opts.width {
        for it in &mut items {
            break_long(it, width, opts);
        }
    }
    // The `by` column of each group.
    let columns = columns(&mut items, opts);
    let mut out = String::new();
    let mut next_comment = 0;
    let mut prev_top_level = false;
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
        // definitions or imports, and wherever the source has one.
        let same_run = k > 0 && top && matches!((head(&items[k - 1]), head(it)), (Some(Tok::Kw(a)), Some(Tok::Kw(b))) if a == b && matches!(a, Kw::Predicate | Kw::Define | Kw::Import));
        let mut last = items.get(k.wrapping_sub(1)).map_or(0, |p| p.lines.last().map_or(0, |(l, _)| *l));
        let first = pending.first().map_or(it.first_line, |c| c.line);
        if k > 0 && (!same_run && (top || prev_top_level && !pending.is_empty()) || blank_between(last, first)) {
            out.push('\n');
        }
        let indent = " ".repeat(it.depth * opts.indent);
        let cont = " ".repeat(it.depth * opts.indent + opts.continuation);
        for c in pending {
            if c.line != first && blank_between(last, c.line) {
                out.push('\n');
            }
            out.push_str(&indent);
            out.push_str(&c.text);
            out.push('\n');
            last = c.line;
        }
        if first != it.first_line && blank_between(last, it.first_line) {
            out.push('\n');
        }
        let rendered = render(it, it.group.map(|g| columns[g]), opts);
        for (j, ((line, _), text)) in it.lines.iter().zip(&rendered).enumerate() {
            out.push_str(text);
            // Comments on this source line, after the last output line it gave, and own-line
            // comments before the next.
            // When the next item starts on this source line too, the comments wait for it.
            let next_here = j + 1 == it.lines.len() && items.get(k + 1).is_some_and(|n| n.first_line == *line);
            let last_of_line = it.lines.get(j + 1).is_none_or(|(l, _)| l != line) && !next_here;
            let until = it.lines.get(j + 1).map_or(*line, |(l, _)| *l - 1);
            while last_of_line && next_comment < comments.len() && comments[next_comment].line <= until {
                let c = &comments[next_comment];
                next_comment += 1;
                if c.trailing {
                    out.push_str("  ");
                    out.push_str(&c.text);
                } else {
                    out.push('\n');
                    out.push_str(&cont);
                    out.push_str(&c.text);
                }
            }
            out.push('\n');
        }
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

fn head(it: &Item) -> Option<&Tok> {
    it.lines.first().and_then(|(_, t)| t.first())
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
        let mut lines: Vec<(usize, Vec<Tok>)> = Vec::new();
        for t in &toks[s..e] {
            match lines.last_mut() {
                Some((l, line)) if *l == t.line => line.push(t.tok.clone()),
                _ => lines.push((t.line, vec![t.tok.clone()])),
            }
        }
        let head = match &toks[s].tok {
            Tok::Kw(k) => Some(*k),
            _ => None,
        };
        if head.is_some_and(|k| TOP.contains(&k)) {
            stack.clear();
        }
        let depth = stack.len();
        let step = toks[s..e].iter().any(|t| t.tok == Tok::Kw(Kw::By)) && head != Some(Kw::Therefore);
        let at = if theorem_wide { stack.first_mut() } else { stack.last_mut() };
        let mut group = None;
        if let (true, Some(seg)) = (step, at) {
            group = Some(*seg.get_or_insert_with(|| {
                segments += 1;
                segments - 1
            }));
        }
        items.push(Item { lines, first_line: toks[s].line, depth, group, align: None });
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

/// Where an item's first line aligns, and the width before it: a definition's `=`, or the
/// formula after a step's or an assumption's label.
fn anchor(it: &Item) -> Option<(usize, usize)> {
    let line = &it.lines[0].1;
    let colon = Tok::Sym(Sym::Colon);
    let i = match line.first()? {
        Tok::Kw(Kw::Define) => line.iter().position(|t| *t == Tok::Sym(Sym::Equals))?,
        Tok::Kw(Kw::Assume) if line.get(2) == Some(&colon) && line.len() > 3 => 3,
        Tok::Lower(_) if line.get(1) == Some(&colon) && line.len() > 2 => 2,
        _ => return None,
    };
    Some((i, render_toks(&line[..i]).len()))
}

/// The alignment columns: one past the widest before the point, per run of definitions or of
/// assumptions with no blank line between them, and per segment and depth of steps.
fn align_columns(items: &mut [Item], blank_between: &dyn Fn(usize, usize) -> bool) {
    // A run continues while the head keyword and depth stay the same and no blank line parts it.
    let runs = |it: &Item| matches!(head(it), Some(Tok::Kw(Kw::Define | Kw::Assume)));
    let mut k = 0;
    while k < items.len() {
        let mut end = k;
        while runs(&items[k]) && end + 1 < items.len() {
            let (a, b) = (&items[end], &items[end + 1]);
            // Top-level items other than definitions get a blank line between them, which ends a
            // run as one in the source does.
            let parted = b.depth == 0 && head(b) != Some(&Tok::Kw(Kw::Define));
            if parted || head(b) != head(a) || b.depth != a.depth || blank_between(a.lines.last().map_or(0, |(l, _)| *l), b.first_line) {
                break;
            }
            end += 1;
        }
        let group: Vec<usize> = if runs(&items[k]) { (k..=end).collect() } else { Vec::new() };
        set_column(items, &group);
        k = end + 1;
    }
    // Steps by segment, and by depth, since a theorem-wide segment spans its lemmas.
    let mut keys: Vec<(usize, usize)> = items.iter().filter_map(|i| i.group.map(|g| (g, i.depth))).collect();
    keys.sort();
    keys.dedup();
    for key in keys {
        let group: Vec<usize> = (0..items.len()).filter(|&i| items[i].group.map(|g| (g, items[i].depth)) == Some(key)).collect();
        set_column(items, &group);
    }
}

/// Gives the items of one group the column one past the widest before their alignment point.
fn set_column(items: &mut [Item], group: &[usize]) {
    let col = group.iter().filter_map(|&i| anchor(&items[i])).map(|(_, w)| w + 1).max();
    for &i in group {
        if let (Some((p, _)), Some(col)) = (anchor(&items[i]), col) {
            items[i].align = Some((p, col));
        }
    }
}

/// Tokens `..end` of line `j` of an item, the first line padded at its alignment point.
fn line_text(it: &Item, j: usize, end: usize) -> String {
    let line = &it.lines[j].1;
    match it.align.filter(|&(p, _)| j == 0 && p < end) {
        Some((p, col)) => {
            let before = render_toks(&line[..p]);
            let pad = col.saturating_sub(before.len()).max(1);
            format!("{before}{}{}", " ".repeat(pad), render_toks(&line[p..end]))
        }
        None => render_toks(&line[..end]),
    }
}

/// Where line `j` of an item starts: its indentation, or the continuation's.
fn start(it: &Item, j: usize, opts: &Options) -> usize {
    it.depth * opts.indent + if j == 0 { 0 } else { opts.continuation }
}

/// The line of an item with `by` after other tokens, and where `by` is in it.
fn inline_by(it: &Item) -> Option<(usize, usize)> {
    it.lines.iter().enumerate().find_map(|(j, (_, t))| t.iter().position(|t| *t == Tok::Kw(Kw::By)).filter(|&p| p > 0).map(|p| (j, p)))
}

/// The `by` column of each segment: one past the longest text before an inline `by` in it.
/// With a width, an item whose line would run past it at that column has its `by` moved to a
/// line of its own, and the columns are worked out again.
fn columns(items: &mut [Item], opts: &Options) -> Vec<usize> {
    let n = items.iter().filter_map(|i| i.group).max().map_or(0, |g| g + 1);
    loop {
        let mut cols = vec![0; n];
        for it in items.iter() {
            if let (Some(g), Some((j, p))) = (it.group, inline_by(it)) {
                let width = start(it, j, opts) + line_text(it, j, p).len();
                cols[g] = cols[g].max(width + 1);
            }
        }
        let Some(width) = opts.width.filter(|_| opts.pad) else { return cols };
        let mut moved = false;
        for it in items.iter_mut() {
            if let (Some(g), Some((j, p))) = (it.group, inline_by(it)) {
                if cols[g] + render_toks(&it.lines[j].1[p..]).len() > width {
                    split_line(it, j, p);
                    moved = true;
                }
            }
        }
        if !moved {
            return cols;
        }
    }
}

/// Splits line `j` of an item before token `p`, the rest going on a new line from the same
/// source line.
fn split_line(it: &mut Item, j: usize, p: usize) {
    let (l, line) = &mut it.lines[j];
    let rest = line.split_off(p);
    let l = *l;
    it.lines.insert(j + 1, (l, rest));
}

/// Breaks the lines of an item that run past `width`: an inline `by` goes on a line of its own,
/// then a formula breaks before an operator, the outermost first, `->` before `or` before
/// `and`, as late as fits.
fn break_long(it: &mut Item, width: usize, opts: &Options) {
    let mut j = 0;
    while j < it.lines.len() {
        // As printed, with any padding before a definition's `=`.
        let printed = render(it, None, opts)[j].len();
        let line = &it.lines[j].1;
        let at = printed - render_toks(line).len();
        if printed > width {
            let by = line.iter().position(|t| *t == Tok::Kw(Kw::By)).filter(|&p| p > 0);
            if let Some(p) = by.or_else(|| break_point(&line[..by.unwrap_or(line.len())], width.saturating_sub(at))) {
                split_line(it, j, p);
                continue;
            }
        }
        j += 1;
    }
}

/// Where to break a formula's tokens so the first part fits in `room`: the latest fitting
/// operator of the best kind, or the first of the best kind when none fits.
fn break_point(toks: &[Tok], room: usize) -> Option<usize> {
    let mut depth = 0;
    let mut ops: Vec<((usize, usize), usize)> = Vec::new();
    for (i, t) in toks.iter().enumerate() {
        let rank = match t {
            Tok::Sym(Sym::LParen) => {
                depth += 1;
                continue;
            }
            Tok::Sym(Sym::RParen) => {
                depth -= 1;
                continue;
            }
            Tok::Sym(Sym::Arrow) => 0,
            Tok::Kw(Kw::Or) => 1,
            Tok::Kw(Kw::And) => 2,
            _ => continue,
        };
        if i > 0 {
            ops.push(((depth, rank), i));
        }
    }
    let best = ops.iter().map(|(k, _)| *k).min()?;
    let mut kinds: Vec<(usize, usize)> = ops.iter().map(|(k, _)| *k).collect();
    kinds.sort();
    kinds.dedup();
    for kind in kinds {
        if let Some((_, i)) = ops.iter().rev().find(|(k, i)| *k == kind && render_toks(&toks[..*i]).len() <= room) {
            return Some(*i);
        }
    }
    ops.iter().find(|(k, _)| *k == best).map(|(_, i)| *i)
}

/// Each line of an item: indented, with `by` padded to `column` when it follows other tokens,
/// or put at the column when it starts a line.
fn render(it: &Item, column: Option<usize>, opts: &Options) -> Vec<String> {
    let mut out = Vec::new();
    for (j, (_, line)) in it.lines.iter().enumerate() {
        let at = start(it, j, opts);
        let by = line.iter().position(|t| *t == Tok::Kw(Kw::By));
        let mut s = String::new();
        match by {
            Some(0) => {
                // The segment's column, unless that would run past the width.
                let col = column.filter(|_| opts.pad).unwrap_or(0).max(at);
                let col = if opts.width.is_some_and(|w| col + render_toks(line).len() > w) { at } else { col };
                s.push_str(&" ".repeat(col));
                s.push_str(&render_toks(line));
            }
            Some(p) => {
                let before = line_text(it, j, p);
                s.push_str(&" ".repeat(at));
                s.push_str(&before);
                let here = at + before.len();
                let pad = match column {
                    Some(c) if opts.pad => c.saturating_sub(here).max(1),
                    _ => 1,
                };
                s.push_str(&" ".repeat(pad));
                s.push_str(&render_toks(&line[p..]));
            }
            None => {
                s.push_str(&" ".repeat(at));
                s.push_str(&line_text(it, j, line.len()));
            }
        }
        out.push(s);
    }
    out
}

/// Tokens joined with spaces, except around punctuation: none before `:`, `)` and `.`, and
/// none after `(`.
fn render_toks(toks: &[Tok]) -> String {
    let mut s = String::new();
    for (i, t) in toks.iter().enumerate() {
        let prev = if i > 0 { Some(&toks[i - 1]) } else { None };
        let space = match (prev, t) {
            (None, _) => false,
            (_, Tok::Sym(Sym::Colon | Sym::RParen | Sym::Dot)) => false,
            (Some(Tok::Sym(Sym::LParen)), _) => false,
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
        let want = "theorem t:\n  predicate A\n  assume a: A\n  s:      A       by reit a\n  longer: A and A by and_i a a\n  lemma l:\n    assume b: A\n    k:  A             by reit b\n    kk: A and A and A by and_i b b b\n    therefore A -> A and A and A\n  -- done\n  m: A by reit a\n  therefore A\n";
        assert_eq!(fmt(src), want);
    }

    #[test]
    fn definitions_assumptions_comments_and_spacing() {
        let src = "define X = A\ndefine Ax (P x) = forall x.\nP x  -- all\ntheorem u:\nassume ax: Ax Q\nk: forall x. Q x by reit ax\ntherefore Ax Q -> forall x. Q x\n";
        let want = "define X        = A\ndefine Ax (P x) = forall x.\n    P x  -- all\n\ntheorem u:\n  assume ax: Ax Q\n  k: forall x. Q x by reit ax\n  therefore Ax Q -> forall x. Q x\n";
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
    fn declarations_stay_together_unless_a_blank_line_parts_them() {
        assert_eq!(fmt("import a\nimport b\npredicate P x\npredicate Q\ndefine X = Q\n"), "import a\nimport b\n\npredicate P x\npredicate Q\n\ndefine X = Q\n");
        assert_eq!(fmt("define X = Q\n\n\ndefine Y = X\ntheorem t:\n assume x: X\n\n therefore X -> X\n"), "define X = Q\n\ndefine Y = X\n\ntheorem t:\n  assume x: X\n\n  therefore X -> X\n");
    }

    #[test]
    fn formulas_align_after_labels() {
        let src = "theorem t:\npredicate A\nassume a: A\nassume bb: A\nk: A by reit a\nkkk: A by reit bb\ntherefore A\n";
        let want = "theorem t:\n  predicate A\n  assume a:  A\n  assume bb: A\n  k:   A by reit a\n  kkk: A by reit bb\n  therefore A\n";
        assert_eq!(fmt(src), want);
    }

    #[test]
    fn a_trailing_comment_stays_after_the_last_item_of_its_line() {
        let got = fmt("theorem t:\n  variable x  assume h: P x  -- note\n  therefore forall x. P x -> P x\n");
        assert_eq!(got, "theorem t:\n  variable x\n  assume h: P x  -- note\n  therefore forall x. P x -> P x\n");
    }

    #[test]
    fn stable_on_a_file_that_doesnt_parse() {
        // Top-level assumptions get blank lines between them, so they don't align.
        let once = fmt("assume a: A\nassume bb: A\n");
        assert_eq!(once, "assume a: A\n\nassume bb: A\n");
        assert_eq!(fmt(&once), once);
    }

    #[test]
    fn equals_align_per_run_of_definitions() {
        let src = "define A1 = Q\ndefine Long x y =   Q\n-- apart\ndefine Ab = Q\n\ndefine B = Q\n";
        let want = "define A1       = Q\ndefine Long x y = Q\n-- apart\ndefine Ab       = Q\n\ndefine B = Q\n";
        assert_eq!(fmt(src), want);
        let space = format(src, &Options { pad: false, ..Options::default() }).unwrap();
        assert_eq!(space, "define A1 = Q\ndefine Long x y = Q\n-- apart\ndefine Ab = Q\n\ndefine B = Q\n");
    }

    #[test]
    fn spacing_is_forgotten_and_line_breaks_kept() {
        let a = fmt("theorem t:\n  predicate A\n  assume a: A\n  therefore A -> A\n");
        let b = fmt("theorem t:   predicate A\n     assume a:   A\ntherefore    A    ->   A");
        assert_eq!(a, b);
        let src = "define D (P x) = (forall x. P x) -> P x -- first\n  -- between\n -> (forall y. P y)\n";
        let want = "define D (P x) = (forall x. P x) -> P x  -- first\n    -- between\n    -> (forall y. P y)\n";
        assert_eq!(fmt(src), want);
        let two = format(src, &Options { continuation: 2, ..Options::default() }).unwrap();
        assert_eq!(two, want.replace("    ", "  "));
    }

    #[test]
    fn by_on_its_own_line_keeps_the_column() {
        let src = "theorem t:\npredicate A\nassume a: A\ns: A by reit a\nlong: A and A and A\nby and_i a a a\ntherefore A -> A\n";
        let want = "theorem t:\n  predicate A\n  assume a: A\n  s:    A by reit a\n  long: A and A and A\n          by and_i a a a\n  therefore A -> A\n";
        assert_eq!(fmt(src), want);
    }

    #[test]
    fn a_width_breaks_long_lines_by_first_then_outermost() {
        let src = "predicate P x\npredicate Q\ndefine D = (forall x. P x -> Q) -> (forall y. P y and Q) -> Q or Q\ntheorem t:\n  assume q: Q\n  k: (forall x. P x -> Q) -> (forall y. P y and Q) -> Q by reit q\n  therefore Q -> Q\n";
        let opts = Options { width: Some(40), ..Options::default() };
        let once = format(src, &opts).unwrap();
        let want = "predicate P x\npredicate Q\n\ndefine D = (forall x. P x -> Q)\n    -> (forall y. P y and Q) -> Q or Q\n\ntheorem t:\n  assume q: Q\n  k: (forall x. P x -> Q)\n      -> (forall y. P y and Q) -> Q\n      by reit q\n  therefore Q -> Q\n";
        assert_eq!(once, want);
        assert_eq!(format(&once, &opts).unwrap(), once);
        // Without a width, nothing is broken.
        assert_eq!(fmt(src).lines().count(), 9);
    }

    #[test]
    fn a_width_counts_padding_and_moves_a_far_by_in() {
        // `define A`'s line fits until `=` is padded, and the own-line `by` at its segment's
        // column would run past the width.
        let src = "predicate Q\ndefine A = Q and Q and Q\ndefine Longer x = Q\ntheorem t:\n  assume q: Q\n  longish_label: Q by reit q\n  s: Q\n  by and_i q q q\n  therefore Q -> Q\n";
        let want = "predicate Q\n\ndefine A        = Q and Q\n    and Q\ndefine Longer x = Q\n\ntheorem t:\n  assume q: Q\n  longish_label: Q by reit q\n  s:             Q\n      by and_i q q q\n  therefore Q -> Q\n";
        assert_eq!(format(src, &Options { width: Some(28), ..Options::default() }).unwrap(), want);
    }
}
