//! Formulas. Terms are variables only; `==` is alpha-equivalence; substitution never captures.
//!
//! A formula is a shared, immutable tree. Each node carries its free variables, so closedness
//! and capture checks are lookups, and a substitution copies only the path to what it changes.

use std::cmp::Ordering;
use std::collections::BTreeSet;
use std::fmt;
use std::rc::Rc;

/// A variable or predicate name. Shared, so copying one costs nothing.
pub type Name = Rc<str>;

#[derive(Clone, Debug)]
pub struct Formula(Rc<Inner>);

#[derive(Debug)]
struct Inner {
    node: Node,
    /// The free variables, sorted, without repeats.
    free: Vec<Name>,
}

#[derive(Debug)]
pub enum Node {
    Absurd,
    Atom(Name, Vec<Name>),
    And(Formula, Formula),
    Or(Formula, Formula),
    Imp(Formula, Formula),
    All(Name, Formula),
    Ex(Name, Formula),
}

/// A predicate given as a formula with holes. Free variables other than the holes, the
/// extras, are the caller's; whoever instantiates with the template closes over them.
#[derive(Clone, Debug)]
pub struct Template {
    holes: Vec<Name>,
    body: Formula,
    extras: Vec<Name>,
}

pub fn absurd() -> Formula {
    Formula::new(Node::Absurd)
}

pub fn atom(p: &str, args: &[Name]) -> Formula {
    Formula::new(Node::Atom(p.into(), args.to_vec()))
}

pub fn imp(a: Formula, b: Formula) -> Formula {
    Formula::new(Node::Imp(a, b))
}

pub fn and(a: Formula, b: Formula) -> Formula {
    Formula::new(Node::And(a, b))
}

pub fn or(a: Formula, b: Formula) -> Formula {
    Formula::new(Node::Or(a, b))
}

pub fn all(x: &Name, a: Formula) -> Formula {
    Formula::new(Node::All(x.clone(), a))
}

pub fn ex(x: &Name, a: Formula) -> Formula {
    Formula::new(Node::Ex(x.clone(), a))
}

/// Hole names start with `_`, which user names can't.
pub fn hole_names(n: usize) -> Vec<Name> {
    (0..n).map(|i| format!("_h{i}").into()).collect()
}

/// `base` with primes added until it clashes with nothing in `avoid`.
pub fn fresh(base: &str, avoid: &BTreeSet<&str>) -> Name {
    let mut name = base.to_string();
    while avoid.contains(name.as_str()) {
        name.push('\'');
    }
    name.into()
}

/// The sorted union of two sorted lists.
fn merge(a: &[Name], b: &[Name]) -> Vec<Name> {
    let mut out = Vec::with_capacity(a.len() + b.len());
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        match a[i].cmp(&b[j]) {
            Ordering::Less => {
                out.push(a[i].clone());
                i += 1;
            }
            Ordering::Greater => {
                out.push(b[j].clone());
                j += 1;
            }
            Ordering::Equal => {
                out.push(a[i].clone());
                i += 1;
                j += 1;
            }
        }
    }
    out.extend_from_slice(&a[i..]);
    out.extend_from_slice(&b[j..]);
    out
}

impl Formula {
    fn new(node: Node) -> Formula {
        let free = match &node {
            Node::Absurd => Vec::new(),
            Node::Atom(_, args) => {
                let mut v = args.clone();
                v.sort();
                v.dedup();
                v
            }
            Node::And(a, b) | Node::Or(a, b) | Node::Imp(a, b) => merge(&a.0.free, &b.0.free),
            Node::All(x, a) | Node::Ex(x, a) => a.0.free.iter().filter(|v| *v != x).cloned().collect(),
        };
        Formula(Rc::new(Inner { node, free }))
    }

    pub fn node(&self) -> &Node {
        &self.0.node
    }

    /// Whether both are the same tree in memory, which makes them equal.
    fn same(&self, other: &Formula) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }

    /// The free variables, sorted.
    pub fn free_vars(&self) -> &[Name] {
        &self.0.free
    }

    pub fn is_free(&self, x: &str) -> bool {
        self.0.free.binary_search_by(|v| (**v).cmp(x)).is_ok()
    }

    /// Each predicate the formula mentions, with the number of arguments it's given.
    pub fn preds(&self) -> BTreeSet<(&str, usize)> {
        let mut out = BTreeSet::new();
        self.collect_preds(&mut out);
        out
    }

    fn collect_preds<'a>(&'a self, out: &mut BTreeSet<(&'a str, usize)>) {
        match self.node() {
            Node::Absurd => {}
            Node::Atom(p, args) => {
                out.insert((p, args.len()));
            }
            Node::And(a, b) | Node::Or(a, b) | Node::Imp(a, b) => {
                a.collect_preds(out);
                b.collect_preds(out);
            }
            Node::All(_, a) | Node::Ex(_, a) => a.collect_preds(out),
        }
    }

    /// Simultaneously replaces free variables, renaming binders that would capture.
    pub fn subst_vars(&self, s: &[(Name, Name)]) -> Formula {
        // Pairs that change nothing are dropped: a substitution that changes nothing copies nothing.
        if s.iter().all(|(x, y)| x == y) {
            return self.clone();
        }
        let s: Vec<(Name, Name)> = s.iter().filter(|(x, y)| x != y).cloned().collect();
        self.subst_vars_in(&s)
    }

    fn subst_vars_in(&self, s: &[(Name, Name)]) -> Formula {
        if !s.iter().any(|(x, _)| self.is_free(x)) {
            return self.clone();
        }
        match self.node() {
            Node::Absurd => self.clone(),
            Node::Atom(p, args) => {
                let args = args.iter().map(|a| s.iter().find(|(x, _)| x == a).map_or(a, |(_, y)| y).clone()).collect();
                Formula::new(Node::Atom(p.clone(), args))
            }
            Node::And(a, b) | Node::Or(a, b) | Node::Imp(a, b) => {
                Formula::new(binary(self.node(), a.subst_vars_in(s), b.subst_vars_in(s)))
            }
            Node::All(x, a) | Node::Ex(x, a) => {
                // The pair for `x` itself stops here. A pair whose target is `x` would capture.
                let mut s: Vec<(Name, Name)> = s.iter().filter(|(v, _)| v != x && a.is_free(v)).cloned().collect();
                if s.iter().any(|(_, y)| y == x) {
                    let mut avoid: BTreeSet<&str> = a.free_vars().iter().map(|v| &**v).collect();
                    avoid.extend(s.iter().map(|(_, y)| &**y));
                    let z = fresh(x, &avoid);
                    s.push((x.clone(), z.clone()));
                    return Formula::new(quantifier(self.node(), z, a.subst_vars_in(&s)));
                }
                Formula::new(quantifier(self.node(), x.clone(), a.subst_vars_in(&s)))
            }
        }
    }

    /// Simultaneously replaces predicates by templates. Binders that would capture a
    /// template's free variables are renamed. Fails on an arity mismatch.
    pub fn subst_preds(&self, map: &[(&str, &Template)]) -> Result<Formula, String> {
        let extras: BTreeSet<&str> = map.iter().flat_map(|(_, t)| t.extras()).map(|v| &**v).collect();
        self.subst_preds_in(map, &extras)
    }

    fn subst_preds_in(&self, map: &[(&str, &Template)], extras: &BTreeSet<&str>) -> Result<Formula, String> {
        Ok(match self.node() {
            Node::Absurd => self.clone(),
            Node::Atom(p, args) => match map.iter().find(|(q, _)| &**p == *q) {
                None => self.clone(),
                Some((_, t)) => {
                    if t.holes.len() != args.len() {
                        return Err(format!("`{p}` takes {} argument(s), got {}", t.holes.len(), args.len()));
                    }
                    t.apply(args)
                }
            },
            Node::And(a, b) | Node::Or(a, b) | Node::Imp(a, b) => {
                let (a2, b2) = (a.subst_preds_in(map, extras)?, b.subst_preds_in(map, extras)?);
                if a.same(&a2) && b.same(&b2) {
                    self.clone()
                } else {
                    Formula::new(binary(self.node(), a2, b2))
                }
            }
            Node::All(x, a) | Node::Ex(x, a) => {
                if extras.contains(&**x) {
                    let mut avoid: BTreeSet<&str> = a.free_vars().iter().map(|v| &**v).collect();
                    avoid.extend(extras.iter().copied());
                    let z = fresh(x, &avoid);
                    let a = a.subst_vars_in(&[(x.clone(), z.clone())]);
                    Formula::new(quantifier(self.node(), z, a.subst_preds_in(map, extras)?))
                } else {
                    let body = a.subst_preds_in(map, extras)?;
                    if a.same(&body) {
                        self.clone()
                    } else {
                        Formula::new(quantifier(self.node(), x.clone(), body))
                    }
                }
            }
        })
    }

    /// Wraps `forall`s around `self`, the first variable outermost.
    pub fn close(self, prefix: &[Name]) -> Formula {
        prefix.iter().rev().fold(self, |body, x| all(x, body))
    }
}

/// The connective of `like` over `a` and `b`.
fn binary(like: &Node, a: Formula, b: Formula) -> Node {
    match like {
        Node::And(..) => Node::And(a, b),
        Node::Or(..) => Node::Or(a, b),
        _ => Node::Imp(a, b),
    }
}

/// The quantifier of `like`, binding `x` over `body`.
fn quantifier(like: &Node, x: Name, body: Formula) -> Node {
    match like {
        Node::Ex(..) => Node::Ex(x, body),
        _ => Node::All(x, body),
    }
}

impl Template {
    /// A template's holes must be distinct.
    pub fn new(holes: Vec<Name>, body: Formula) -> Result<Template, String> {
        let distinct: BTreeSet<&Name> = holes.iter().collect();
        if distinct.len() != holes.len() {
            return Err("a template's holes must be distinct".into());
        }
        let extras = body.free_vars().iter().filter(|v| !holes.contains(v)).cloned().collect();
        Ok(Template { holes, body, extras })
    }

    /// A statement: a template with no holes.
    pub fn statement(body: Formula) -> Template {
        let extras = body.free_vars().to_vec();
        Template { holes: Vec::new(), body, extras }
    }

    pub fn holes(&self) -> &[Name] {
        &self.holes
    }

    pub fn body(&self) -> &Formula {
        &self.body
    }

    /// The body with `args` for the holes.
    pub fn apply(&self, args: &[Name]) -> Formula {
        let s: Vec<(Name, Name)> = self.holes.iter().cloned().zip(args.iter().cloned()).collect();
        self.body.subst_vars(&s)
    }

    /// Free variables other than the holes, sorted.
    pub fn extras(&self) -> &[Name] {
        &self.extras
    }
}

impl PartialEq for Formula {
    fn eq(&self, other: &Self) -> bool {
        alpha(self, other, &mut Vec::new())
    }
}

impl Eq for Formula {}

/// `env` pairs up the binders passed so far on each side, innermost last. One tree on both
/// sides is equal to itself unless a binder passed so far renames one of its free variables.
fn alpha(a: &Formula, b: &Formula, env: &mut Vec<(Name, Name)>) -> bool {
    if a.same(b) && env.iter().all(|(l, r)| l == r || !(a.is_free(l) || a.is_free(r))) {
        return true;
    }
    let var = |x: &Name, y: &Name, env: &[(Name, Name)]| {
        let i = env.iter().rposition(|(l, _)| l == x);
        let j = env.iter().rposition(|(_, r)| r == y);
        match (i, j) {
            (Some(i), Some(j)) => i == j,
            (None, None) => x == y,
            _ => false,
        }
    };
    match (a.node(), b.node()) {
        (Node::Absurd, Node::Absurd) => true,
        (Node::Atom(p, xs), Node::Atom(q, ys)) => {
            p == q && xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| var(x, y, env))
        }
        (Node::And(a1, a2), Node::And(b1, b2)) | (Node::Or(a1, a2), Node::Or(b1, b2)) | (Node::Imp(a1, a2), Node::Imp(b1, b2)) => {
            alpha(a1, b1, env) && alpha(a2, b2, env)
        }
        (Node::All(x, p), Node::All(y, q)) | (Node::Ex(x, p), Node::Ex(y, q)) => {
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
                match (op, rest.node()) {
                    ("and", Node::And(x, y)) | ("or", Node::Or(x, y)) | ("imp", Node::Imp(x, y)) => {
                        write!(f, " {}", Arg(x))?;
                        rest = y;
                    }
                    _ => return write!(f, " {}", Arg(rest)),
                }
            }
        };
        match self.node() {
            Node::Absurd => write!(f, "absurd"),
            Node::Atom(p, args) => {
                write!(f, "{p}")?;
                args.iter().try_for_each(|a| write!(f, " {a}"))
            }
            Node::And(a, b) => chain(f, "and", a, b),
            Node::Or(a, b) => chain(f, "or", a, b),
            Node::Imp(a, b) => chain(f, "imp", a, b),
            Node::All(x, a) => write!(f, "forall {x} $ {a}"),
            Node::Ex(x, a) => write!(f, "exists {x} $ {a}"),
        }
    }
}

/// A formula in argument position: parenthesized unless it's a single word.
struct Arg<'a>(&'a Formula);

impl fmt::Display for Arg<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.0.node() {
            Node::Absurd => write!(f, "absurd"),
            Node::Atom(_, args) if args.is_empty() => write!(f, "{}", self.0),
            _ => write!(f, "({})", self.0),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn n(x: &str) -> Name {
        x.into()
    }

    fn at(p: &str, args: &[&str]) -> Formula {
        atom(p, &args.iter().map(|a| n(a)).collect::<Vec<_>>())
    }

    fn pair(x: &str, y: &str) -> (Name, Name) {
        (n(x), n(y))
    }

    #[test]
    fn free_variables_are_kept() {
        let f = imp(at("P", &["x", "y"]), all(&n("y"), at("Q", &["y", "z"])));
        assert_eq!(f.free_vars().iter().map(|v| &**v).collect::<Vec<_>>(), ["x", "y", "z"]);
        assert!(f.is_free("z") && !f.is_free("w"));
        assert!(!all(&n("x"), at("P", &["x"])).is_free("x"));
    }

    #[test]
    fn alpha_equivalence() {
        assert_eq!(all(&n("x"), at("P", &["x"])), all(&n("y"), at("P", &["y"])));
        assert_ne!(all(&n("x"), at("P", &["y"])), all(&n("y"), at("P", &["y"])));
        let a = all(&n("x"), all(&n("x"), at("R", &["x", "x"])));
        assert_eq!(a, all(&n("y"), all(&n("z"), at("R", &["z", "z"]))));
        assert_ne!(a, all(&n("y"), all(&n("z"), at("R", &["y", "z"]))));
    }

    #[test]
    fn shared_subtrees_still_compare_under_renaming() {
        // forall x y. R x y vs forall y x. R x y, with the body shared: not equal.
        let body = at("R", &["x", "y"]);
        let a = all(&n("x"), all(&n("y"), body.clone()));
        let b = all(&n("y"), all(&n("x"), body.clone()));
        assert_ne!(a, b);
        // With a body the renaming doesn't touch, the shared tree is equal to itself.
        let body = at("R", &["z"]);
        assert_eq!(all(&n("x"), body.clone()), all(&n("y"), body));
    }

    #[test]
    fn subst_vars_avoids_capture() {
        let a = ex(&n("y"), at("R", &["x", "y"]));
        let b = a.subst_vars(&[pair("x", "y")]);
        assert_eq!(b.to_string(), "exists y' $ R y y'");
        assert_eq!(at("R", &["x", "y"]).subst_vars(&[pair("x", "y"), pair("y", "x")]).to_string(), "R y x");
    }

    #[test]
    fn subst_vars_shares_what_it_leaves() {
        let f = imp(at("P", &["x"]), all(&n("y"), at("Q", &["y"])));
        let g = f.subst_vars(&[pair("x", "z")]);
        let (Node::Imp(_, fb), Node::Imp(_, gb)) = (f.node(), g.node()) else { panic!() };
        assert!(fb.same(gb));
        assert!(f.subst_vars(&[pair("w", "z")]).same(&f));
    }

    #[test]
    fn subst_preds_avoids_capture() {
        // forall y $ P y, with P := (R y _), must not let the template's y be captured.
        let t = Template::new(vec![n("_h0")], at("R", &["y", "_h0"])).unwrap();
        let f = all(&n("y"), at("P", &["y"])).subst_preds(&[("P", &t)]).unwrap();
        assert_eq!(f.to_string(), "forall y' $ R y y'");
    }

    #[test]
    fn subst_preds_checks_arity() {
        let t = Template::statement(at("Q", &[]));
        let e = at("P", &["x"]).subst_preds(&[("P", &t)]).unwrap_err();
        assert_eq!(e, "`P` takes 0 argument(s), got 1");
    }

    #[test]
    fn template_holes_are_distinct() {
        assert!(Template::new(vec![n("_h0"), n("_h0")], at("R", &["_h0", "_h0"])).is_err());
    }

    #[test]
    fn display_flattens_chains() {
        let f = imp(at("A", &[]), imp(at("B", &[]), and(at("C", &["x"]), at("D", &[]))));
        assert_eq!(f.to_string(), "imp A B (and (C x) D)");
    }
}
