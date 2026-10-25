//! Formulas in the file's own syntax, for messages. `imp A absurd` prints as `not A`.

use crate::kernel::formula::Formula;

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
    match f {
        Formula::Absurd => out.push_str("absurd"),
        Formula::Atom(p, args) => {
            out.push_str(p);
            for a in args {
                out.push(' ');
                out.push_str(a);
            }
        }
        Formula::Imp(a, b) if matches!(**b, Formula::Absurd) => {
            out.push_str("not ");
            write(a, 3, out);
        }
        Formula::Imp(a, b) => paren(level > 0, out, &|out| {
            write(a, 1, out);
            out.push_str(" -> ");
            write(b, 0, out);
        }),
        Formula::Or(a, b) => paren(level > 1, out, &|out| {
            write(a, 2, out);
            out.push_str(" or ");
            write(b, 1, out);
        }),
        Formula::And(a, b) => paren(level > 2, out, &|out| {
            write(a, 3, out);
            out.push_str(" and ");
            write(b, 2, out);
        }),
        Formula::All(..) | Formula::Ex(..) => paren(level > 0, out, &|out| {
            let (kw, is_all) = match f {
                Formula::All(..) => ("forall", true),
                _ => ("exists", false),
            };
            out.push_str(kw);
            let mut cur = f;
            loop {
                match cur {
                    Formula::All(x, body) if is_all => {
                        out.push(' ');
                        out.push_str(x);
                        cur = body;
                    }
                    Formula::Ex(x, body) if !is_all => {
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
    use crate::kernel::formula::{all, and, ex, imp, or};

    fn atom(p: &str, args: &[&str]) -> Formula {
        Formula::Atom(p.into(), args.iter().map(|a| a.to_string()).collect())
    }

    #[test]
    fn precedence_and_sugar() {
        let (a, b, c) = (atom("A", &[]), atom("B", &[]), atom("P", &["x"]));
        assert_eq!(show(&imp(a.clone(), imp(b.clone(), a.clone()))), "A -> B -> A");
        assert_eq!(show(&imp(imp(a.clone(), b.clone()), a.clone())), "(A -> B) -> A");
        assert_eq!(show(&imp(a.clone(), Formula::Absurd)), "not A");
        assert_eq!(show(&imp(and(a.clone(), b.clone()), Formula::Absurd)), "not (A and B)");
        assert_eq!(show(&or(and(a.clone(), b.clone()), c.clone())), "A and B or P x");
        assert_eq!(show(&and(a.clone(), or(b.clone(), c.clone()))), "A and (B or P x)");
        assert_eq!(show(&all("x", all("y", imp(c.clone(), b.clone())))), "forall x y. P x -> B");
        assert_eq!(show(&imp(all("x", c.clone()), ex("y", c.clone()))), "(forall x. P x) -> exists y. P x");
        assert_eq!(show(&and(a.clone(), all("x", c.clone()))), "A and (forall x. P x)");
    }
}
