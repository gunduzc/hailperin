//! The trusted kernel. `Thm` and `Lemma` can only be made here.
//!
//! A `Thm` is a closed formula together with the premises it rests on. The only rule is
//! modus ponens; axioms are closures of the instances built by `axiom`. A `Lemma` is a
//! checked proof, used afterwards by uniform substitution into its signature.

use crate::syntax::{all, and, ex, imp, or, Formula, Template};
use std::collections::BTreeSet;

#[derive(Clone, Debug)]
pub struct Thm {
    concl: Formula,
    hyps: Vec<Formula>,
}

/// A checked proof: for any templates for its parameters, its premises give its conclusion.
#[derive(Clone, Debug)]
pub struct Lemma {
    params: Vec<(String, usize)>,
    premises: Vec<Formula>,
    concl: Formula,
}

/// An axiom instance; binder variables are given by name.
#[derive(Clone, Debug)]
pub enum Axiom {
    Imp1(Formula, Formula),
    Imp2(Formula, Formula, Formula),
    AndI(Formula, Formula),
    AndE1(Formula, Formula),
    AndE2(Formula, Formula),
    OrI1(Formula, Formula),
    OrI2(Formula, Formula),
    OrE(Formula, Formula, Formula),
    Efq(Formula),
    Dist(String, Formula, Formula),
    Vac(String, Formula),
    Inst(String, String, Formula),
    ExI(String, String, Formula),
    ExE(String, Formula, Formula),
}

fn closed(f: &Formula, what: &str) -> Result<(), String> {
    match f.free_vars().into_iter().next() {
        Some(x) => Err(format!("{what} has `{x}` free: formulas must be closed")),
        None => Ok(()),
    }
}

impl Thm {
    pub fn concl(&self) -> &Formula {
        &self.concl
    }

    pub fn hyps(&self) -> &[Formula] {
        &self.hyps
    }
}

fn bind(params: &[(String, usize)], templates: &[Template]) -> Result<Vec<(String, Template)>, String> {
    if params.len() != templates.len() {
        return Err(format!("expected {} predicate argument(s), got {}", params.len(), templates.len()));
    }
    for ((p, n), t) in params.iter().zip(templates) {
        if t.holes.len() != *n {
            return Err(format!("`{p}` takes {n} argument(s), but the template takes {}", t.holes.len()));
        }
    }
    Ok(params.iter().map(|(p, _)| p.clone()).zip(templates.iter().cloned()).collect())
}

/// The prefix an instance is closed over: the caller's, which must cover the templates'
/// free variables, or else those variables in order.
fn choose_prefix(templates: &[Template], prefix: Option<&[String]>) -> Result<Vec<String>, String> {
    let mut extras = BTreeSet::new();
    for t in templates {
        extras.extend(t.extras());
    }
    match prefix {
        None => Ok(extras.into_iter().collect()),
        Some(p) => {
            if let Some(x) = extras.iter().find(|x| !p.contains(x)) {
                return Err(format!("`{x}` is free in an argument but not bound by the prefix"));
            }
            let distinct: BTreeSet<&String> = p.iter().collect();
            if distinct.len() != p.len() {
                return Err("the prefix binds a variable twice".into());
            }
            Ok(p.to_vec())
        }
    }
}

fn union(a: &[Formula], b: &[Formula]) -> Vec<Formula> {
    let mut out = a.to_vec();
    for h in b {
        if !out.contains(h) {
            out.push(h.clone());
        }
    }
    out
}

/// The closure of an axiom instance under `prefix`, outermost first.
pub fn axiom(ax: Axiom, prefix: &[String]) -> Result<Thm, String> {
    let instance = match ax {
        Axiom::Imp1(a, b) => imp(a.clone(), imp(b, a)),
        Axiom::Imp2(a, b, c) => imp(
            imp(a.clone(), imp(b.clone(), c.clone())),
            imp(imp(a.clone(), b), imp(a, c)),
        ),
        Axiom::AndI(a, b) => imp(a.clone(), imp(b.clone(), and(a, b))),
        Axiom::AndE1(a, b) => imp(and(a.clone(), b), a),
        Axiom::AndE2(a, b) => imp(and(a, b.clone()), b),
        Axiom::OrI1(a, b) => imp(a.clone(), or(a, b)),
        Axiom::OrI2(a, b) => imp(b.clone(), or(a, b)),
        Axiom::OrE(a, b, c) => imp(
            imp(a.clone(), c.clone()),
            imp(imp(b.clone(), c.clone()), imp(or(a, b), c)),
        ),
        Axiom::Efq(a) => imp(Formula::Absurd, a),
        Axiom::Dist(x, a, b) => imp(all(&x, imp(a.clone(), b.clone())), imp(all(&x, a), all(&x, b))),
        Axiom::Vac(x, a) => {
            if a.is_free(&x) {
                return Err(format!("vac: `{x}` is free in {a}"));
            }
            imp(a.clone(), all(&x, a))
        }
        // `y` must be bound by the closure even where it doesn't occur: otherwise
        // `imp (forall x absurd) absurd` would be an axiom, and it's false in the empty domain.
        Axiom::Inst(y, x, a) => {
            if !prefix.contains(&y) {
                return Err(format!("inst: `{y}` must be bound by the `forall` prefix"));
            }
            let inst = a.subst_vars(&[(x.clone(), y.clone())]);
            imp(all(&x, a), inst)
        }
        Axiom::ExI(y, x, a) => {
            if !prefix.contains(&y) {
                return Err(format!("ex_i: `{y}` must be bound by the `forall` prefix"));
            }
            let inst = a.subst_vars(&[(x.clone(), y.clone())]);
            imp(inst, ex(&x, a))
        }
        Axiom::ExE(x, a, c) => {
            if c.is_free(&x) {
                return Err(format!("ex_e: `{x}` is free in {c}"));
            }
            imp(all(&x, imp(a.clone(), c.clone())), imp(ex(&x, a), c))
        }
    };
    let concl = instance.close(prefix);
    closed(&concl, "this axiom instance")?;
    Ok(Thm { concl, hyps: Vec::new() })
}

/// From `A` and `imp A B`, `B`.
pub fn mp(a: &Thm, ab: &Thm) -> Result<Thm, String> {
    let Formula::Imp(p, q) = &ab.concl else {
        return Err(format!("{} is not an implication", ab.concl));
    };
    if **p != a.concl {
        return Err(format!("{} needs {p}, but got {}", ab.concl, a.concl));
    }
    Ok(Thm { concl: (**q).clone(), hyps: union(&a.hyps, &ab.hyps) })
}

/// A premise of the proof being checked.
pub fn assume(f: &Formula) -> Result<Thm, String> {
    closed(f, "this premise")?;
    Ok(Thm { concl: f.clone(), hyps: vec![f.clone()] })
}

impl Lemma {
    /// Checks that `body` proves `concl` from `premises` only.
    pub fn new(params: Vec<(String, usize)>, premises: Vec<Formula>, concl: Formula, body: &Thm) -> Result<Lemma, String> {
        closed(&concl, "the conclusion")?;
        if body.concl != concl {
            return Err(format!("the proof gives {}, not {concl}", body.concl));
        }
        for h in &body.hyps {
            if !premises.contains(h) {
                return Err("the proof uses an assumption that isn't one of its premises".into());
            }
        }
        Ok(Lemma { params, premises, concl })
    }

    pub fn params(&self) -> &[(String, usize)] {
        &self.params
    }

    pub fn premises(&self) -> &[Formula] {
        &self.premises
    }

    pub fn concl(&self) -> &Formula {
        &self.concl
    }

    /// Uniform substitution: the instance of the conclusion, given matching premises.
    /// Everything is closed over `prefix` (by default, the templates' free variables), which
    /// may bind more variables than occur, in any order.
    pub fn apply(&self, templates: &[Template], prefix: Option<&[String]>, args: &[&Thm]) -> Result<Thm, String> {
        let map = bind(&self.params, templates)?;
        let prefix = choose_prefix(templates, prefix)?;
        if args.len() != self.premises.len() {
            return Err(format!("expected {} piece(s) of evidence, got {}", self.premises.len(), args.len()));
        }
        let mut hyps = Vec::new();
        for (i, (premise, t)) in self.premises.iter().zip(args).enumerate() {
            let want = premise.subst_preds(&map)?.close(&prefix);
            if *t.concl() != want {
                return Err(format!("evidence {} should prove {want}, but proves {}", i + 1, t.concl()));
            }
            hyps = union(&hyps, &t.hyps);
        }
        let concl = self.concl.subst_preds(&map)?.close(&prefix);
        Ok(Thm { concl, hyps })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn atom(p: &str, args: &[&str]) -> Formula {
        Formula::Atom(p.into(), args.iter().map(|a| a.to_string()).collect())
    }

    #[test]
    fn identity() {
        let a = atom("A", &[]);
        let aa = imp(a.clone(), a.clone());
        let s3 = mp(&axiom(Axiom::Imp1(a.clone(), aa.clone()), &[]).unwrap(), &axiom(Axiom::Imp2(a.clone(), aa, a.clone()), &[]).unwrap()).unwrap();
        let id = mp(&axiom(Axiom::Imp1(a.clone(), a.clone()), &[]).unwrap(), &s3).unwrap();
        assert_eq!(id.concl().to_string(), "imp A A");
    }

    #[test]
    fn inst_needs_its_variable_bound() {
        // imp (forall x absurd) absurd is false in the empty domain; inst can't produce it.
        assert!(axiom(Axiom::Inst("y".into(), "x".into(), Formula::Absurd), &[]).is_err());
        let th = axiom(Axiom::Inst("y".into(), "x".into(), Formula::Absurd), &["y".into()]).unwrap();
        assert_eq!(th.concl().to_string(), "forall y $ imp (forall x $ absurd) absurd");
    }

    #[test]
    fn inst_in_any_position() {
        // forall y $ forall x $ imp (forall z $ P x z) (P x y): the instantiated y is outermost.
        let a = atom("P", &["x", "z"]);
        let th = axiom(Axiom::Inst("y".into(), "z".into(), a), &["y".into(), "x".into()]).unwrap();
        assert_eq!(th.concl().to_string(), "forall y $ forall x $ imp (forall z $ P x z) (P x y)");
    }

    #[test]
    fn side_conditions() {
        let px = atom("P", &["x"]);
        assert!(axiom(Axiom::Vac("x".into(), px.clone()), &["x".into()]).is_err());
        assert!(axiom(Axiom::ExE("x".into(), px.clone(), px.clone()), &[]).is_err());
    }

    #[test]
    fn axioms_must_close() {
        let e = axiom(Axiom::Imp1(atom("P", &["x"]), atom("Q", &[])), &[]).unwrap_err();
        assert_eq!(e, "this axiom instance has `x` free: formulas must be closed");
        assert!(axiom(Axiom::Imp1(atom("P", &["x"]), atom("Q", &[])), &["x".into()]).is_ok());
    }

    #[test]
    fn lemma_rejects_unlisted_assumptions() {
        let a = atom("A", &[]);
        let th = assume(&a).unwrap();
        assert!(Lemma::new(vec![], vec![], a.clone(), &th).is_err());
        assert!(Lemma::new(vec![], vec![a.clone()], a, &th).is_ok());
    }

    #[test]
    fn lemma_apply_substitutes() {
        // From P, get P: instantiate P := Q x, closed over x.
        let p = atom("P", &[]);
        let th = assume(&p).unwrap();
        let lemma = Lemma::new(vec![("P".into(), 0)], vec![p.clone()], p, &th).unwrap();
        let t = Template { holes: vec![], body: atom("Q", &["x"]) };
        let ev = assume(&all("x", atom("Q", &["x"]))).unwrap();
        let out = lemma.apply(&[t], None, &[&ev]).unwrap();
        assert_eq!(out.concl().to_string(), "forall x $ Q x");
    }
}
