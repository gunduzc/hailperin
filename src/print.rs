//! Formulas in the file's own syntax, for messages. `imp A absurd` prints as `not A`, and an
//! instance of a definition over individuals and statements prints as the definition's name.

use crate::kernel::formula::{Formula, Name, Node};
use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap};

/// A definition that messages print by name: `name params = body`, the parameters individuals
/// and statements.
pub struct Fold {
    pub name: String,
    pub params: Vec<Name>,
    pub body: Formula,
}

thread_local! {
    /// The definitions of the check under way, each with its file, in the order they were made.
    static FOLDS: RefCell<Vec<(usize, Fold)>> = const { RefCell::new(Vec::new()) };
    /// The files the file being checked sees, in the order it would load them alone.
    static SEES: RefCell<Vec<usize>> = const { RefCell::new(Vec::new()) };
}

/// Forgets the definitions folded so far, for a new check.
pub fn clear_folds() {
    FOLDS.with(|f| f.borrow_mut().clear());
    SEES.with(|s| s.borrow_mut().clear());
}

/// Prints instances of this definition, from this file, by its name from now on.
pub fn add_fold(file: usize, fold: Fold) {
    FOLDS.with(|f| f.borrow_mut().push((file, fold)));
}

/// Prints with the definitions of these files only, so that a line prints the same whichever
/// file is checked.
pub fn set_sees(files: &[usize]) {
    SEES.with(|s| *s.borrow_mut() = files.to_vec());
}

/// `f` as an instance of a definition, the latest that fits in the order the file being
/// checked would load them alone: its name and arguments.
fn folded(f: &Formula) -> Option<String> {
    if matches!(f.node(), Node::Atom(..) | Node::Absurd) {
        return None;
    }
    let sees = SEES.with(|s| s.borrow().clone());
    FOLDS.with(|folds| {
        let folds = folds.borrow();
        let visible = sees.iter().rev().flat_map(|file| folds.iter().rev().filter(move |(f, _)| f == file).map(|(_, fold)| fold));
        for fold in visible {
            let metas: BTreeSet<Name> = fold.params.iter().cloned().collect();
            let (mut sol, mut statements) = (HashMap::new(), HashMap::new());
            if !crate::check::fit(&fold.body, f, &metas, &mut Vec::new(), &mut sol, &mut statements) {
                continue;
            }
            // A statement is in parentheses unless it is a name alone.
            let arg = |p: &Name| {
                sol.get(p).map(|v| v.to_string()).or_else(|| {
                    statements.get(p).map(|s| match s.node() {
                        Node::Atom(_, xs) if xs.is_empty() => show(s),
                        _ => format!("({})", show(s)),
                    })
                })
            };
            if let Some(args) = fold.params.iter().map(arg).collect::<Option<Vec<_>>>() {
                let mut s = fold.name.clone();
                for a in args {
                    s.push(' ');
                    s.push_str(&a);
                }
                return Some(s);
            }
        }
        None
    })
}

/// Precedence levels: 0 formula (`->`, quantifiers), 1 `or`, 2 `and`, 3 `not`, 4 atoms.
pub fn show(f: &Formula) -> String {
    let mut s = String::new();
    write(f, 0, &mut s);
    plain(&s)
}

/// The text with every name the checker made fresh, `a'`, renamed to one a reader could have
/// written, `a1`: the base with the smallest number the text doesn't use.
fn plain(s: &str) -> String {
    let word = |c: char| c.is_ascii_alphanumeric() || c == '_' || c == '\'';
    let words: Vec<&str> = s.split(|c: char| !word(c)).filter(|w| !w.is_empty()).collect();
    let mut taken: BTreeSet<String> = words.iter().map(|w| w.to_string()).collect();
    let mut renamed: HashMap<&str, String> = HashMap::new();
    for w in words.iter().filter(|w| w.contains('\'')) {
        if !renamed.contains_key(w) {
            let base = w.trim_end_matches('\'');
            let new = (1..).map(|k| format!("{base}{k}")).find(|n| !taken.contains(n)).expect("some number is free");
            taken.insert(new.clone());
            renamed.insert(w, new);
        }
    }
    if renamed.is_empty() {
        return s.to_string();
    }
    let mut out = String::new();
    let mut rest = s;
    while let Some(i) = rest.find(word) {
        out.push_str(&rest[..i]);
        let len = rest[i..].find(|c: char| !word(c)).unwrap_or(rest.len() - i);
        let w = &rest[i..i + len];
        out.push_str(renamed.get(w).map_or(w, String::as_str));
        rest = &rest[i + len..];
    }
    out.push_str(rest);
    out
}

fn write(f: &Formula, level: u8, out: &mut String) {
    let paren = |need: bool, out: &mut String, inner: &dyn Fn(&mut String)| {
        if need {
            out.push('(');
            inner(out);
            out.push(')');
        } else {
            inner(out);
        }
    };
    if let Some(s) = folded(f) {
        out.push_str(&s);
        return;
    }
    match f.node() {
        Node::Absurd => out.push_str("absurd"),
        Node::Atom(p, args) => {
            out.push_str(p);
            for a in args {
                out.push(' ');
                out.push_str(a);
            }
        }
        Node::Imp(a, b) if matches!(b.node(), Node::Absurd) => {
            out.push_str("not ");
            write(a, 3, out);
        }
        Node::Imp(a, b) => paren(level > 0, out, &|out| {
            write(a, 1, out);
            out.push_str(" -> ");
            write(b, 0, out);
        }),
        Node::Or(a, b) => paren(level > 1, out, &|out| {
            write(a, 2, out);
            out.push_str(" or ");
            write(b, 1, out);
        }),
        Node::And(a, b) => paren(level > 2, out, &|out| {
            write(a, 3, out);
            out.push_str(" and ");
            write(b, 2, out);
        }),
        Node::All(..) | Node::Ex(..) => paren(level > 0, out, &|out| {
            let (kw, is_all) = match f.node() {
                Node::All(..) => ("forall", true),
                _ => ("exists", false),
            };
            out.push_str(kw);
            let mut cur = f;
            loop {
                // A quantifier that folds into a definition starts that definition's text.
                if !std::ptr::eq(cur, f) && folded(cur).is_some() {
                    break;
                }
                match cur.node() {
                    Node::All(x, body) if is_all => {
                        out.push(' ');
                        out.push_str(x);
                        cur = body;
                    }
                    Node::Ex(x, body) if !is_all => {
                        out.push(' ');
                        out.push_str(x);
                        cur = body;
                    }
                    _ => break,
                }
            }
            out.push_str(". ");
            write(cur, 0, out);
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::formula::{absurd, all, and, ex, imp, or, Name};

    fn atom(p: &str, args: &[&str]) -> Formula {
        crate::kernel::formula::atom(p, &args.iter().map(|a| Name::from(*a)).collect::<Vec<_>>())
    }

    fn n(x: &str) -> Name {
        x.into()
    }

    #[test]
    fn precedence_and_sugar() {
        let (a, b, c) = (atom("A", &[]), atom("B", &[]), atom("P", &["x"]));
        assert_eq!(show(&imp(a.clone(), imp(b.clone(), a.clone()))), "A -> B -> A");
        assert_eq!(show(&imp(imp(a.clone(), b.clone()), a.clone())), "(A -> B) -> A");
        assert_eq!(show(&imp(a.clone(), absurd())), "not A");
        assert_eq!(show(&imp(and(a.clone(), b.clone()), absurd())), "not (A and B)");
        assert_eq!(show(&or(and(a.clone(), b.clone()), c.clone())), "A and B or P x");
        assert_eq!(show(&and(a.clone(), or(b.clone(), c.clone()))), "A and (B or P x)");
        assert_eq!(show(&all(&n("x"), all(&n("y"), imp(c.clone(), b.clone())))), "forall x y. P x -> B");
        assert_eq!(show(&imp(all(&n("x"), c.clone()), ex(&n("y"), c.clone()))), "(forall x. P x) -> exists y. P x");
        assert_eq!(show(&and(a.clone(), all(&n("x"), c.clone()))), "A and (forall x. P x)");
    }
}
