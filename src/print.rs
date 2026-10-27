//! Formulas in the file's own syntax, for messages. `imp A absurd` prints as `not A`, and an
//! instance of a definition over individuals prints as the definition's name.

use crate::kernel::formula::{Formula, Name, Node};
use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap};

/// A definition that messages print by name: `name params = body`, the parameters individuals.
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
            let mut sol = HashMap::new();
            if !crate::check::match_vars(&fold.body, f, &metas, &mut Vec::new(), &mut sol) {
                continue;
            }
            if let Some(args) = fold.params.iter().map(|p| sol.get(p)).collect::<Option<Vec<_>>>() {
                let mut s = fold.name.clone();
                for a in args {
                    s.push(' ');
                    s.push_str(a);
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
    s
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
