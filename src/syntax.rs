//! Formulas. Terms are variables only; `==` is alpha-equivalence; substitution never captures.

use std::collections::BTreeSet;
use std::fmt;

#[derive(Clone, Debug)]
pub enum Formula {
    Absurd,
    Atom(String, Vec<String>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Imp(Box<Formula>, Box<Formula>),
    All(String, Box<Formula>),
    Ex(String, Box<Formula>),
}

/// A predicate given as a formula with holes. Free variables other than the holes are
/// the caller's; whoever instantiates with the template closes over them.
#[derive(Clone, Debug)]
pub struct Template {
    pub holes: Vec<String>,
    pub body: Formula,
}

pub fn imp(a: Formula, b: Formula) -> Formula {
    Formula::Imp(Box::new(a), Box::new(b))
}

pub fn and(a: Formula, b: Formula) -> Formula {
    Formula::And(Box::new(a), Box::new(b))
}

pub fn or(a: Formula, b: Formula) -> Formula {
    Formula::Or(Box::new(a), Box::new(b))
}

pub fn all(x: &str, a: Formula) -> Formula {
    Formula::All(x.to_string(), Box::new(a))
}

pub fn ex(x: &str, a: Formula) -> Formula {
    Formula::Ex(x.to_string(), Box::new(a))
}

/// Hole names start with `_`, which user names can't.
pub fn hole_names(n: usize) -> Vec<String> {
    (0..n).map(|i| format!("_h{i}")).collect()
}

/// `base` with primes added until it clashes with nothing in `avoid`.
pub fn fresh(base: &str, avoid: &BTreeSet<String>) -> String {
    let mut name = base.to_string();
    while avoid.contains(&name) {
        name.push('\'');
    }
    name
}

impl Formula {
    pub fn free_vars(&self) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        self.collect_free(&mut Vec::new(), &mut out);
        out
    }

    fn collect_free(&self, bound: &mut Vec<String>, out: &mut BTreeSet<String>) {
        match self {
            Formula::Absurd => {}
            Formula::Atom(_, args) => out.extend(args.iter().filter(|a| !bound.contains(a)).cloned()),
            Formula::And(a, b) | Formula::Or(a, b) | Formula::Imp(a, b) => {
                a.collect_free(bound, out);
                b.collect_free(bound, out);
            }
            Formula::All(x, a) | Formula::Ex(x, a) => {
                bound.push(x.clone());
                a.collect_free(bound, out);
                bound.pop();
            }
        }
    }

    /// The predicate names the formula mentions.
    pub fn preds(&self) -> BTreeSet<String> {
        match self {
            Formula::Absurd => BTreeSet::new(),
            Formula::Atom(p, _) => BTreeSet::from([p.clone()]),
            Formula::And(a, b) | Formula::Or(a, b) | Formula::Imp(a, b) => &a.preds() | &b.preds(),
            Formula::All(_, a) | Formula::Ex(_, a) => a.preds(),
        }
    }

    pub fn is_free(&self, x: &str) -> bool {
        self.free_vars().contains(x)
    }

    /// Simultaneously replaces free variables, renaming binders that would capture.
    pub fn subst_vars(&self, s: &[(String, String)]) -> Formula {
        match self {
            Formula::Absurd => Formula::Absurd,
            Formula::Atom(p, args) => {
                let args = args
                    .iter()
                    .map(|a| s.iter().find(|(x, _)| x == a).map_or_else(|| a.clone(), |(_, y)| y.clone()))
                    .collect();
                Formula::Atom(p.clone(), args)
            }
            Formula::And(a, b) => and(a.subst_vars(s), b.subst_vars(s)),
            Formula::Or(a, b) => or(a.subst_vars(s), b.subst_vars(s)),
            Formula::Imp(a, b) => imp(a.subst_vars(s), b.subst_vars(s)),
            Formula::All(x, a) | Formula::Ex(x, a) => {
                let mut s: Vec<(String, String)> = s.iter().filter(|(v, _)| v != x && a.is_free(v)).cloned().collect();
                let (x, a) = if s.iter().any(|(_, y)| y == x) {
                    let mut avoid = a.free_vars();
                    avoid.extend(s.iter().map(|(_, y)| y.clone()));
                    let z = fresh(x, &avoid);
                    s.push((x.clone(), z.clone()));
                    (z, a.subst_vars(&s))
                } else {
                    (x.clone(), a.subst_vars(&s))
                };
                self.rebind(&x, a)
            }
        }
    }

    /// The same quantifier as `self` (which must be one) over `x` and `body`.
    fn rebind(&self, x: &str, body: Formula) -> Formula {
        match self {
            Formula::Ex(..) => ex(x, body),
            _ => all(x, body),
        }
    }

    /// Simultaneously replaces predicates by templates. Binders that would capture a
    /// template's free variables are renamed. Fails on an arity mismatch.
    pub fn subst_preds(&self, map: &[(String, Template)]) -> Result<Formula, String> {
        let mut extras = BTreeSet::new();
        for (_, t) in map {
            extras.extend(t.extras());
        }
        self.subst_preds_in(map, &extras)
    }

    fn subst_preds_in(&self, map: &[(String, Template)], extras: &BTreeSet<String>) -> Result<Formula, String> {
        Ok(match self {
            Formula::Absurd => Formula::Absurd,
            Formula::Atom(p, args) => match map.iter().find(|(q, _)| q == p) {
                None => self.clone(),
                Some((_, t)) => {
                    if t.holes.len() != args.len() {
                        return Err(format!("`{p}` takes {} argument(s), got {}", t.holes.len(), args.len()));
                    }
                    let s: Vec<(String, String)> = t.holes.iter().cloned().zip(args.iter().cloned()).collect();
                    t.body.subst_vars(&s)
                }
            },
            Formula::And(a, b) => and(a.subst_preds_in(map, extras)?, b.subst_preds_in(map, extras)?),
            Formula::Or(a, b) => or(a.subst_preds_in(map, extras)?, b.subst_preds_in(map, extras)?),
            Formula::Imp(a, b) => imp(a.subst_preds_in(map, extras)?, b.subst_preds_in(map, extras)?),
            Formula::All(x, a) | Formula::Ex(x, a) => {
                if extras.contains(x) {
                    let mut avoid = a.free_vars();
                    avoid.extend(extras.iter().cloned());
                    let z = fresh(x, &avoid);
                    let a = a.subst_vars(&[(x.clone(), z.clone())]);
                    self.rebind(&z, a.subst_preds_in(map, extras)?)
                } else {
                    self.rebind(x, a.subst_preds_in(map, extras)?)
                }
            }
        })
    }

    /// Wraps `forall`s around `self`, the first variable outermost.
    pub fn close(self, prefix: &[String]) -> Formula {
        prefix.iter().rev().fold(self, |body, x| all(x, body))
    }
}

impl Template {
    /// Free variables other than the holes.
    pub fn extras(&self) -> BTreeSet<String> {
        let mut fv = self.body.free_vars();
        for h in &self.holes {
            fv.remove(h);
        }
        fv
    }
}

impl PartialEq for Formula {
    fn eq(&self, other: &Self) -> bool {
        alpha(self, other, &mut Vec::new())
    }
}

impl Eq for Formula {}

/// `env` pairs up the binders passed so far on each side, innermost last.
fn alpha(a: &Formula, b: &Formula, env: &mut Vec<(String, String)>) -> bool {
    let var = |x: &String, y: &String, env: &[(String, String)]| {
        let i = env.iter().rposition(|(l, _)| l == x);
        let j = env.iter().rposition(|(_, r)| r == y);
        match (i, j) {
            (Some(i), Some(j)) => i == j,
            (None, None) => x == y,
            _ => false,
        }
    };
    match (a, b) {
        (Formula::Absurd, Formula::Absurd) => true,
        (Formula::Atom(p, xs), Formula::Atom(q, ys)) => {
            p == q && xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| var(x, y, env))
        }
        (Formula::And(a1, a2), Formula::And(b1, b2))
        | (Formula::Or(a1, a2), Formula::Or(b1, b2))
        | (Formula::Imp(a1, a2), Formula::Imp(b1, b2)) => alpha(a1, b1, env) && alpha(a2, b2, env),
        (Formula::All(x, p), Formula::All(y, q)) | (Formula::Ex(x, p), Formula::Ex(y, q)) => {
            env.push((x.clone(), y.clone()));
            let same = alpha(p, q, env);
            env.pop();
            same
        }
        _ => false,
    }
}

impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Right-nested chains print flat: `imp A B C`.
        let chain = |f: &mut fmt::Formatter, op: &str, a: &Formula, b: &Formula| -> fmt::Result {
            write!(f, "{op} {}", Arg(a))?;
            let mut rest = b;
            loop {
                match (op, rest) {
                    ("and", Formula::And(x, y)) | ("or", Formula::Or(x, y)) | ("imp", Formula::Imp(x, y)) => {
                        write!(f, " {}", Arg(x))?;
                        rest = y;
                    }
                    _ => return write!(f, " {}", Arg(rest)),
                }
            }
        };
        match self {
            Formula::Absurd => write!(f, "absurd"),
            Formula::Atom(p, args) => {
                write!(f, "{p}")?;
                args.iter().try_for_each(|a| write!(f, " {a}"))
            }
            Formula::And(a, b) => chain(f, "and", a, b),
            Formula::Or(a, b) => chain(f, "or", a, b),
            Formula::Imp(a, b) => chain(f, "imp", a, b),
            Formula::All(x, a) => write!(f, "forall {x} $ {a}"),
            Formula::Ex(x, a) => write!(f, "exists {x} $ {a}"),
        }
    }
}

/// A formula in argument position: parenthesized unless it's a single word.
struct Arg<'a>(&'a Formula);

impl fmt::Display for Arg<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.0 {
            Formula::Absurd => write!(f, "absurd"),
            Formula::Atom(_, args) if args.is_empty() => write!(f, "{}", self.0),
            other => write!(f, "({other})"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn atom(p: &str, args: &[&str]) -> Formula {
        Formula::Atom(p.into(), args.iter().map(|a| a.to_string()).collect())
    }

    #[test]
    fn alpha_equivalence() {
        assert_eq!(all("x", atom("P", &["x"])), all("y", atom("P", &["y"])));
        assert_ne!(all("x", atom("P", &["y"])), all("y", atom("P", &["y"])));
        let a = all("x", all("x", atom("R", &["x", "x"])));
        assert_eq!(a, all("y", all("z", atom("R", &["z", "z"]))));
        assert_ne!(a, all("y", all("z", atom("R", &["y", "z"]))));
    }

    #[test]
    fn subst_vars_avoids_capture() {
        let a = ex("y", atom("R", &["x", "y"]));
        let b = a.subst_vars(&[("x".into(), "y".into())]);
        assert_eq!(b.to_string(), "exists y' $ R y y'");
        assert_eq!(atom("R", &["x", "y"]).subst_vars(&[("x".into(), "y".into()), ("y".into(), "x".into())]).to_string(), "R y x");
    }

    #[test]
    fn subst_preds_avoids_capture() {
        // forall y $ P y, with P := (R y _), must not let the template's y be captured.
        let t = Template { holes: vec!["_h0".into()], body: atom("R", &["y", "_h0"]) };
        let f = all("y", atom("P", &["y"])).subst_preds(&[("P".into(), t)]).unwrap();
        assert_eq!(f.to_string(), "forall y' $ R y y'");
    }

    #[test]
    fn subst_preds_checks_arity() {
        let t = Template { holes: vec![], body: atom("Q", &[]) };
        let e = atom("P", &["x"]).subst_preds(&[("P".into(), t)]).unwrap_err();
        assert_eq!(e, "`P` takes 0 argument(s), got 1");
    }

    #[test]
    fn display_flattens_chains() {
        let f = imp(atom("A", &[]), imp(atom("B", &[]), and(atom("C", &["x"]), atom("D", &[]))));
        assert_eq!(f.to_string(), "imp A B (and (C x) D)");
    }
}
