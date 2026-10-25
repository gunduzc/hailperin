//! Checks a file: definitions, theories and theorems, in order.
//!
//! Nothing here is trusted. Every theorem comes from the kernel; this module only decides
//! which kernel functions to call, by reading formulas, choosing axiom instances and
//! inferring predicate arguments.
//!
//! Inside a block, the checker keeps a stack of the variables and assumptions in scope. A
//! line is a closed theorem: its formula under one `->` per assumption and one `forall` per
//! variable it is under, in the order they were opened. Those entries are the line's
//! *layers*, a subsequence of the stack. Modus ponens under the layers uses `dist` and
//! `imp2`. Closing the innermost layer with `imp_i` or `forall_i` is free, since the kernel
//! theorem doesn't change. Closing another layer first pushes it inward past the rest, one
//! swap at a time: Hailperin's QE1 and QE5, as derived rules.

use crate::kernel::formula::{all, and, ex, hole_names, imp, or, Formula, Template};
use crate::kernel::{self, Axiom, Lemma, Thm};
use crate::parse::{Arg, Assume, Block, FExpr, Item, Just, Line, Member, Ref, Step, TArg};
use crate::print::show;
use crate::Error;
use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;

pub const RULES: &[&str] = &[
    "imp_i", "imp_e", "and_i", "and_e1", "and_e2", "or_i1", "or_i2", "or_e", "absurd_e", "forall_i", "forall_e",
    "exists_i", "exists_e",
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    Individual,
    Pred(usize),
}

/// A definition, or a theory member: parameters and a body.
struct Def {
    params: Vec<(String, Kind)>,
    body: Formula,
}

/// One member of a theory, with the theory that declared it.
struct MemberInfo {
    label: String,
    origin: String,
    def: Rc<Def>,
}

struct TheoremInfo {
    lemma: Lemma,
}

enum Global {
    /// A primitive predicate: a capitalized name a definition or theory used without defining.
    Prim(usize),
    Def(Rc<Def>),
    Theory(Vec<MemberInfo>),
    Theorem(TheoremInfo),
}

#[derive(Default)]
pub struct Checker {
    globals: HashMap<String, Global>,
    /// Rules for reasoning under layers, proved once per shape (see `shape_rule`).
    rules: RefCell<HashMap<(Rule, String), Rc<Lemma>>>,
    /// Where each premise formula came from: the declaring theory and the member's label.
    origins: RefCell<Vec<(Formula, String, String)>>,
    /// Whether to record each line's scope and closure for `explain`.
    pub explain: bool,
    trace: RefCell<Vec<String>>,
}

/// The two rules for reasoning under a stack of layers.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Rule {
    Mp,
    Lift,
}

/// A variable or an assumption in scope.
#[derive(Clone, Debug)]
enum Entry {
    Var(String),
    Hyp(Formula),
}

/// A theorem whose conclusion is the stack entries at `layers`, in order, wrapped around a
/// body. The layers are increasing indices into the stack.
#[derive(Clone)]
struct Open {
    thm: Thm,
    layers: Vec<usize>,
}

/// A labeled line: its theorem, and the index of its assumption entry if it is one.
struct Labeled {
    label: String,
    open: Open,
    hyp_index: Option<usize>,
}

/// Everything in scope inside one theorem.
#[derive(Default)]
struct Cx {
    /// The theorem's predicate parameters, in order of first use.
    params: Vec<(String, usize)>,
    stack: Vec<Entry>,
    lines: Vec<Labeled>,
    /// The index in `lines` where the current block began, innermost last.
    blocks: Vec<usize>,
    /// The premises used so far: closed formulas.
    premises: Vec<Formula>,
}

impl Cx {
    fn lookup(&self, label: &str) -> Option<&Labeled> {
        self.lines.iter().rev().find(|l| l.label == label)
    }

    fn var_index(&self, name: &str) -> Option<usize> {
        self.stack.iter().position(|e| matches!(e, Entry::Var(v) if v == name))
    }

    fn vars(&self, depth: usize) -> Vec<String> {
        vars(&self.stack[..depth])
    }

    /// The entries at `layers`.
    fn ents(&self, layers: &[usize]) -> Vec<Entry> {
        layers.iter().map(|&i| self.stack[i].clone()).collect()
    }


    fn add_premise(&mut self, f: &Formula) {
        if !self.premises.contains(f) {
            self.premises.push(f.clone());
        }
    }
}

/// Names visible while reading a formula.
struct Scope<'a> {
    /// The theorem's parameters, which may grow, or a fixed map for definitions.
    params: &'a mut Vec<(String, usize)>,
    grow: bool,
    /// Variables bound by quantifiers around the point being read.
    bound: Vec<String>,
    /// Variables in scope in the proof.
    in_scope: Vec<String>,
    /// Free variables not yet in scope, if they are allowed: they enter scope.
    new: Option<Vec<String>>,
}

fn vars(entries: &[Entry]) -> Vec<String> {
    entries
        .iter()
        .filter_map(|e| match e {
            Entry::Var(v) => Some(v.clone()),
            Entry::Hyp(_) => None,
        })
        .collect()
}

/// The body under `entries`: strips one `forall` per variable (renamed to the variable) and
/// one assumption per hypothesis.
fn unwrap(f: &Formula, entries: &[Entry]) -> Result<Formula, String> {
    // The renamings are collected and done at once: one pass over the body, not one per layer.
    let mut s: Vec<(String, String)> = Vec::new();
    let mut cur = f;
    for e in entries {
        cur = match (e, cur) {
            (Entry::Var(y), Formula::All(z, b)) => {
                s.retain(|(v, _)| v != z);
                s.push((z.clone(), y.clone()));
                b
            }
            (Entry::Hyp(h), Formula::Imp(p, b)) if p.subst_vars(&s) == *h => b,
            (_, other) => return Err(format!("{} doesn't have the shape of the current block", show(&other.subst_vars(&s)))),
        };
    }
    Ok(cur.subst_vars(&s))
}

/// `entries` wrapped around `body`: `forall` for a variable, `->` for an assumption.
fn wrap(entries: &[Entry], body: Formula) -> Formula {
    entries.iter().rev().fold(body, |acc, e| match e {
        Entry::Var(x) => all(x, acc),
        Entry::Hyp(h) => imp(h.clone(), acc),
    })
}

/// A template over `vars`, with the template's holes for them.
fn abstract_over(f: &Formula, vars: &[String]) -> Result<Template, String> {
    let holes = hole_names(vars.len());
    let s: Vec<(String, String)> = vars.iter().cloned().zip(holes.iter().cloned()).collect();
    Template::new(holes, f.subst_vars(&s))
}

/// A stack's shape: `V` for a variable, `H` for an assumption.
fn shape(entries: &[Entry]) -> String {
    entries.iter().map(|e| if matches!(e, Entry::Var(_)) { 'V' } else { 'H' }).collect()
}

fn upper(name: &str) -> bool {
    name.chars().next().is_some_and(char::is_uppercase)
}

fn takes(h: &str, n: usize, got: usize, line: usize) -> Error {
    Error::new(line, format!("`{h}` takes {n} argument(s), got {got}"))
}

/// The union of two increasing lists of layers.
fn union(a: &[usize], b: &[usize]) -> Vec<usize> {
    let mut out: Vec<usize> = a.iter().chain(b).copied().collect();
    out.sort_unstable();
    out.dedup();
    out
}

/// The free variables of an axiom instance: those of its formulas, minus the one it binds,
/// plus the one it instantiates at.
fn axiom_free_vars(ax: &Axiom) -> BTreeSet<String> {
    let mut fv: BTreeSet<String> = axiom_formulas(ax).into_iter().flat_map(Formula::free_vars).collect();
    match ax {
        Axiom::Dist(x, ..) | Axiom::Vac(x, _) | Axiom::ExE(x, ..) => {
            fv.remove(x);
        }
        Axiom::Inst(y, x, _) | Axiom::ExI(y, x, _) => {
            fv.remove(x);
            fv.insert(y.clone());
        }
        _ => {}
    }
    fv
}

/// The variable entries of `entries`.
fn var_entries(entries: &[Entry]) -> Vec<Entry> {
    entries.iter().filter(|e| matches!(e, Entry::Var(_))).cloned().collect()
}

/// Free variables in order of first occurrence.
fn free_in_order(f: &Formula) -> Vec<String> {
    fn go(f: &Formula, bound: &mut Vec<String>, out: &mut Vec<String>) {
        match f {
            Formula::Absurd => {}
            Formula::Atom(_, args) => {
                for a in args {
                    if !bound.contains(a) && !out.contains(a) {
                        out.push(a.clone());
                    }
                }
            }
            Formula::And(a, b) | Formula::Or(a, b) | Formula::Imp(a, b) => {
                go(a, bound, out);
                go(b, bound, out);
            }
            Formula::All(x, a) | Formula::Ex(x, a) => {
                bound.push(x.clone());
                go(a, bound, out);
                bound.pop();
            }
        }
    }
    let mut out = Vec::new();
    go(f, &mut Vec::new(), &mut out);
    out
}

fn describe(e: &Entry) -> String {
    match e {
        Entry::Var(x) => format!("the variable `{x}`"),
        Entry::Hyp(h) => format!("the assumption {}", show(h)),
    }
}

impl Checker {
    /// Checks one item; returns the name and conclusion of a theorem.
    pub fn item(&mut self, item: &Item) -> Result<Option<(String, Formula)>, Error> {
        match item {
            Item::Define { name, params, body, line } => {
                self.new_global(name, *line)?;
                self.declare_prims(body, params)?;
                let def = self.definition(params, body, *line, false)?;
                self.globals.insert(name.clone(), Global::Def(Rc::new(def)));
                Ok(None)
            }
            Item::Theory { name, members, line } => {
                self.new_global(name, *line)?;
                for m in members {
                    if let Member::Axiom { params, formula, .. } = m {
                        self.declare_prims(formula, params)?;
                    }
                }
                let infos = self.theory(name, members).map_err(|e| Error::new(e.line, format!("{name}: {}", e.msg)))?;
                self.globals.insert(name.clone(), Global::Theory(infos));
                Ok(None)
            }
            Item::Theorem { name, theories, block, line } => {
                self.new_global(name, *line)?;
                let info = self.theorem(name, theories, block, *line).map_err(|e| Error::new(e.line, format!("{name}: {}", e.msg)))?;
                let concl = info.lemma.concl().clone();
                self.globals.insert(name.clone(), Global::Theorem(info));
                Ok(Some((name.clone(), concl)))
            }
        }
    }

    fn new_global(&self, name: &str, line: usize) -> Result<(), Error> {
        if RULES.contains(&name) {
            return Err(Error::new(line, format!("`{name}` is a rule")));
        }
        if self.globals.contains_key(name) {
            return Err(Error::new(line, format!("`{name}` is already defined")));
        }
        Ok(())
    }

    // ---- definitions and theories ----

    /// Capitalized names in a definition or axiom that nothing defines are primitive
    /// predicates, with the arity they are used at.
    fn declare_prims(&mut self, body: &FExpr, params: &[String]) -> Result<(), Error> {
        fn atoms<'a>(e: &'a FExpr, out: &mut Vec<(&'a str, usize, usize)>) {
            match e {
                FExpr::Absurd(_) => {}
                FExpr::Atom { name, args, line } => {
                    out.push((name, args.len(), *line));
                    for a in args {
                        if let TArg::Paren(f) = a {
                            atoms(f, out);
                        }
                    }
                }
                FExpr::Not(a, _) | FExpr::Forall(_, a, _) | FExpr::Exists(_, a, _) => atoms(a, out),
                FExpr::And(a, b, _) | FExpr::Or(a, b, _) | FExpr::Imp(a, b, _) => {
                    atoms(a, out);
                    atoms(b, out);
                }
            }
        }
        let mut found = Vec::new();
        atoms(body, &mut found);
        for (name, n, line) in found {
            if params.iter().any(|p| p == name) {
                continue;
            }
            match self.globals.get(name) {
                None => {
                    self.globals.insert(name.to_string(), Global::Prim(n));
                }
                Some(Global::Prim(m)) if *m != n => return Err(takes(name, *m, n, line)),
                _ => {}
            }
        }
        Ok(())
    }

    /// `define Name params = body`, or a theory member. Uppercase parameters are predicates
    /// or statements, with the arity read off the body; lowercase ones are individuals.
    fn definition(&self, params: &[String], body: &FExpr, line: usize, closed: bool) -> Result<Def, Error> {
        let mut seen = BTreeSet::new();
        for p in params {
            if !seen.insert(p) {
                return Err(Error::new(line, format!("parameter `{p}` appears twice")));
            }
            if RULES.contains(&p.as_str()) || self.globals.contains_key(p) {
                return Err(Error::new(line, format!("`{p}` is already defined, so it can't be a parameter")));
            }
        }
        let mut kinds = Vec::new();
        let mut preds = Vec::new();
        let mut bound = Vec::new();
        for p in params {
            if upper(p) {
                let mut uses = BTreeSet::new();
                applied_arities(body, p, &mut uses);
                let n = match uses.len() {
                    0 => 0,
                    1 => *uses.iter().next().unwrap(),
                    _ => return Err(Error::new(line, format!("`{p}` is applied to different numbers of arguments"))),
                };
                kinds.push((p.clone(), Kind::Pred(n)));
                preds.push((p.clone(), n));
            } else {
                if closed {
                    return Err(Error::new(line, format!("`{p}` is lowercase, and a theory member's parameters are predicates")));
                }
                kinds.push((p.clone(), Kind::Individual));
                bound.push(p.clone());
            }
        }
        let mut scope = Scope { params: &mut preds, grow: false, bound, in_scope: Vec::new(), new: None };
        let body = self.formula(body, &mut scope)?;
        Ok(Def { params: kinds, body })
    }

    fn theory(&self, name: &str, members: &[Member]) -> Result<Vec<MemberInfo>, Error> {
        let mut infos: Vec<MemberInfo> = Vec::new();
        for m in members {
            match m {
                Member::Include { theory, line } => {
                    let Some(Global::Theory(included)) = self.globals.get(theory) else {
                        return Err(Error::new(*line, format!("`{theory}` is not a theory")));
                    };
                    for inc in included {
                        match infos.iter().find(|i| i.label == inc.label) {
                            Some(have) if have.origin == inc.origin => {}
                            Some(have) => {
                                return Err(Error::new(
                                    *line,
                                    format!("`{}` is a member of both `{}` and `{}`", inc.label, have.origin, inc.origin),
                                ))
                            }
                            None => infos.push(MemberInfo { label: inc.label.clone(), origin: inc.origin.clone(), def: inc.def.clone() }),
                        }
                    }
                }
                Member::Axiom { label, params, formula, line } => {
                    if RULES.contains(&label.as_str()) {
                        return Err(Error::new(*line, format!("`{label}` is a rule")));
                    }
                    if infos.iter().any(|i| i.label == *label) {
                        return Err(Error::new(*line, format!("`{label}` is already a member")));
                    }
                    let def = self.definition(params, formula, *line, true)?;
                    if let Some(x) = def.body.free_vars().into_iter().next() {
                        return Err(Error::new(*line, format!("`{x}` is free in the axiom `{label}`: bind it with `forall` or `exists`")));
                    }
                    infos.push(MemberInfo { label: label.clone(), origin: name.to_string(), def: Rc::new(def) });
                }
            }
        }
        Ok(infos)
    }

    fn member<'a>(&'a self, theory: &str, label: &str, line: usize) -> Result<&'a MemberInfo, Error> {
        match self.globals.get(theory) {
            Some(Global::Theory(infos)) => infos
                .iter()
                .find(|i| i.label == label)
                .ok_or_else(|| Error::new(line, format!("`{theory}` has no member `{label}`"))),
            Some(_) => Err(Error::new(line, format!("`{theory}` is not a theory"))),
            None => Err(Error::new(line, format!("`{theory}` is not defined"))),
        }
    }

    // ---- theorems ----

    fn theorem(&mut self, name: &str, theories: &[String], block: &Block, line: usize) -> Result<TheoremInfo, Error> {
        let mut cx = Cx::default();
        if self.explain {
            self.trace.borrow_mut().push(format!("theorem {name}"));
        }
        let (result, concl) = self.block(block, &mut cx, name)?;
        if let Some(&i) = result.layers.last() {
            return Err(Error::new(block.result.line, format!("{} is still open", describe(&cx.stack[i]))));
        }
        let lemma = Lemma::new(cx.params.clone(), cx.premises.clone(), concl, &result.thm).map_err(|m| Error::new(line, m))?;
        // `in T...`: every premise is a member of one of the theories named.
        if !theories.is_empty() {
            let mut allowed: Vec<(String, String)> = Vec::new();
            for t in theories {
                match self.globals.get(t) {
                    Some(Global::Theory(infos)) => allowed.extend(infos.iter().map(|i| (i.origin.clone(), i.label.clone()))),
                    _ => return Err(Error::new(line, format!("`{t}` is not a theory"))),
                }
            }
            for p in &cx.premises {
                let (origin, label) = self.origin(p);
                if !allowed.contains(&(origin.clone(), label.clone())) {
                    return Err(Error::new(line, format!("`{origin}.{label}` is a premise, but not a member of {}", theories.join(" or "))));
                }
            }
        }
        if self.explain {
            let mut rests = Vec::new();
            for p in &cx.premises {
                let (origin, label) = self.origin(p);
                rests.push(format!("{origin}.{label}: {}", show(p)));
            }
            let rests = if rests.is_empty() { " nothing".to_string() } else { format!("\n    {}", rests.join("\n    ")) };
            self.trace.borrow_mut().push(format!("{name} rests on{rests}"));
        }
        Ok(TheoremInfo { lemma })
    }

    fn origin(&self, premise: &Formula) -> (String, String) {
        self.origins
            .borrow()
            .iter()
            .find(|(f, _, _)| f == premise)
            .map(|(_, o, l)| (o.clone(), l.clone()))
            .expect("every premise has an origin")
    }

    /// A block: assumptions, steps, then the line labeled `name`. Its labels are local, and
    /// its result must have closed every assumption the block opened. Variables it brought
    /// into scope stay in scope: a variable is in scope from its first occurrence on.
    fn block(&self, b: &Block, cx: &mut Cx, name: &str) -> Result<(Open, Formula), Error> {
        let start_depth = cx.stack.len();
        let start_lines = cx.lines.len();
        cx.blocks.push(start_lines);
        let res = self.block_body(b, cx, name, start_depth);
        cx.blocks.pop();
        cx.lines.truncate(start_lines);
        res
    }

    fn block_body(&self, b: &Block, cx: &mut Cx, name: &str, start_depth: usize) -> Result<(Open, Formula), Error> {
        for a in &b.assumes {
            self.assume(a, cx)?;
        }
        for s in &b.steps {
            match s {
                Step::Line(l) => {
                    let (o, _) = self.line(l, cx)?;
                    cx.lines.push(Labeled { label: l.label.clone(), open: o, hyp_index: None });
                }
                Step::Lemma { name: lemma, block, line } => {
                    self.claim_label(cx, lemma, *line)?;
                    let (o, _) = self.block(block, cx, lemma)?;
                    cx.lines.push(Labeled { label: lemma.clone(), open: o, hyp_index: None });
                }
            }
        }
        let (o, stated) = self.line(&b.result, cx)?;
        if let Some(&i) = o.layers.iter().filter(|&&i| i >= start_depth && matches!(cx.stack[i], Entry::Hyp(_))).last() {
            let line = b.result.line;
            return Err(Error::new(line, format!("`{name}` ends with {} still open", describe(&cx.stack[i]))));
        }
        Ok((o, stated))
    }

    /// Takes the lines recorded for `explain`.
    pub fn take_trace(&mut self) -> Vec<String> {
        std::mem::take(&mut *self.trace.borrow_mut())
    }

    /// Records a line's scope, open assumptions and formula.
    fn trace_line(&self, cx: &Cx, label: &str, o: &Open, stated: &Formula) {
        if !self.explain {
            return;
        }
        let vars = vars(&cx.ents(&o.layers)).join(" ");
        let hyps: Vec<String> = o
            .layers
            .iter()
            .filter(|&&i| matches!(cx.stack[i], Entry::Hyp(_)))
            .map(|&i| cx.lines.iter().find(|l| l.hyp_index == Some(i)).map_or("?".to_string(), |l| l.label.clone()))
            .collect();
        let indent = "  ".repeat(cx.blocks.len());
        self.trace.borrow_mut().push(format!("{indent}{label}: [{vars} | {}] {}", hyps.join(" "), show(stated)));
    }

    fn claim_label(&self, cx: &Cx, label: &str, line: usize) -> Result<(), Error> {
        if RULES.contains(&label) {
            return Err(Error::new(line, format!("`{label}` is a rule, so it can't be a label")));
        }
        let start = cx.blocks.last().copied().unwrap_or(0);
        if cx.lines[start..].iter().any(|l| l.label == label) {
            return Err(Error::new(line, format!("`{label}` is already a label in this block")));
        }
        Ok(())
    }

    /// Reads a formula inside a proof. Free variables not yet in scope enter it, in order of
    /// first occurrence, before whatever line the formula belongs to.
    fn proof_formula(&self, e: &FExpr, cx: &mut Cx) -> Result<Formula, Error> {
        let in_scope = cx.vars(cx.stack.len());
        let mut scope = Scope { params: &mut cx.params, grow: true, bound: Vec::new(), in_scope, new: Some(Vec::new()) };
        let f = self.formula(e, &mut scope)?;
        let new = scope.new.take().unwrap();
        // The formula's own order of first occurrence, not the order the reader met them.
        for x in free_in_order(&f) {
            if new.contains(&x) {
                cx.stack.push(Entry::Var(x));
            }
        }
        Ok(f)
    }

    /// An assumption is the line `A -> A`, under the variables `A` mentions, displayed with its
    /// antecedent folded.
    fn assume(&self, a: &Assume, cx: &mut Cx) -> Result<(), Error> {
        self.claim_label(cx, &a.label, a.line)?;
        let f = self.proof_formula(&a.formula, cx)?;
        let d = cx.stack.len();
        let mut layers: Vec<usize> = f.free_vars().iter().filter_map(|x| cx.var_index(x)).collect();
        layers.sort_unstable();
        let id = self.identity(&cx.ents(&layers), &f).map_err(|m| Error::new(a.line, m))?;
        cx.stack.push(Entry::Hyp(f.clone()));
        layers.push(d);
        let open = Open { thm: id, layers };
        cx.lines.push(Labeled { label: a.label.clone(), open: open.clone(), hyp_index: Some(d) });
        self.trace_line(cx, &a.label, &open, &f);
        Ok(())
    }

    /// A step or result: its justification, checked against its stated formula.
    fn line(&self, l: &Line, cx: &mut Cx) -> Result<(Open, Formula), Error> {
        self.claim_label(cx, &l.label, l.line)?;
        let want = self.proof_formula(&l.formula, cx)?;
        let o = self.justify(&l.just, cx, &want)?;
        let got = self.body(cx, &o).map_err(|m| Error::new(l.line, m))?;
        if got != want {
            return Err(Error::new(l.line, format!("this gives {}, not {}", self.pretty(cx, &got), show(&want))));
        }
        self.trace_line(cx, &l.label, &o, &want);
        Ok((o, want))
    }

    /// `f` for display: binders the shape rules named by stack position get the user's names.
    fn pretty(&self, cx: &Cx, f: &Formula) -> String {
        fn go(f: &Formula, cx: &Cx) -> Formula {
            match f {
                Formula::Absurd | Formula::Atom(..) => f.clone(),
                Formula::And(a, b) => and(go(a, cx), go(b, cx)),
                Formula::Or(a, b) => or(go(a, cx), go(b, cx)),
                Formula::Imp(a, b) => imp(go(a, cx), go(b, cx)),
                Formula::All(x, a) | Formula::Ex(x, a) => {
                    let name = x
                        .strip_prefix("_v")
                        .and_then(|i| i.parse::<usize>().ok())
                        .and_then(|i| match cx.stack.get(i) {
                            Some(Entry::Var(v)) if !a.is_free(v) => Some(v.clone()),
                            _ => None,
                        })
                        .unwrap_or_else(|| x.clone());
                    let body = go(&a.subst_vars(&[(x.clone(), name.clone())]), cx);
                    if matches!(f, Formula::All(..)) { all(&name, body) } else { ex(&name, body) }
                }
            }
        }
        show(&go(f, cx))
    }

    // ---- justifications ----

    fn justify(&self, j: &Just, cx: &mut Cx, want: &Formula) -> Result<Open, Error> {
        let line = j.line;
        match &j.head {
            Ref::Member { theory, member } => {
                let o = self.member_instance(theory, member, &j.targs, cx, line)?;
                self.apply_all(o, &j.args, cx, Some(want))
            }
            Ref::Name(h) => {
                if RULES.contains(&h.as_str()) {
                    if !j.targs.is_empty() {
                        return Err(Error::new(line, format!("`{h}` takes lines and variables, not templates")));
                    }
                    return self.rule(h, &j.args, cx, want, line);
                }
                if let Some(l) = cx.lookup(h) {
                    if !j.targs.is_empty() {
                        return Err(Error::new(line, format!("`{h}` is a line, so it takes no templates")));
                    }
                    let o = l.open.clone();
                    return self.apply_all(o, &j.args, cx, Some(want));
                }
                match self.globals.get(h) {
                    Some(Global::Theorem(info)) => {
                        let o = self.call(h, info, &j.targs, &j.args, cx, Some(want), line)?;
                        Ok(o)
                    }
                    Some(_) => Err(Error::new(line, format!("`{h}` is not a rule, a line, or a theorem"))),
                    None => Err(Error::new(line, format!("`{h}` is not a rule, a line here, or a theorem"))),
                }
            }
        }
    }

    /// A line named by an argument: a label, a theorem with nothing left to supply, a theory
    /// member, or an instance.
    fn arg_open(&self, a: &Arg, cx: &mut Cx) -> Result<Open, Error> {
        match a {
            Arg::Ident(n, line) => {
                if let Some(l) = cx.lookup(n) {
                    return Ok(l.open.clone());
                }
                match self.globals.get(n) {
                    Some(Global::Theorem(info)) => self.call(n, info, &[], &[], cx, None, *line),
                    _ if cx.var_index(n).is_some() => Err(Error::new(*line, format!("`{n}` is a variable, and a line is needed here"))),
                    _ => Err(Error::new(*line, format!("`{n}` is not a line here"))),
                }
            }
            Arg::Ref(Ref::Member { theory, member }, line) => self.member_instance(theory, member, &[], cx, *line),
            Arg::Ref(Ref::Name(n), line) => Err(Error::new(*line, format!("`{n}` can't be used here"))),
            Arg::Instance { head: Ref::Member { theory, member }, targs, line } => self.member_instance(theory, member, targs, cx, *line),
            Arg::Instance { head: Ref::Name(n), targs, line } => match self.globals.get(n) {
                Some(Global::Theorem(info)) => self.call(n, info, targs, &[], cx, None, *line),
                _ => Err(Error::new(*line, format!("`{n}` is not a theorem"))),
            },
        }
    }

    /// A variable named by an argument. A name not yet in scope enters it.
    fn arg_var(&self, a: &Arg, cx: &mut Cx) -> Result<String, Error> {
        match a {
            Arg::Ident(n, _) if cx.var_index(n).is_some() => Ok(n.clone()),
            Arg::Ident(n, _) => {
                cx.stack.push(Entry::Var(n.clone()));
                Ok(n.clone())
            }
            other => Err(Error::new(other.line(), "expected a variable")),
        }
    }

    /// A label of an open assumption, with its entry index.
    fn arg_assumption(&self, a: &Arg, cx: &Cx) -> Result<usize, Error> {
        match a {
            Arg::Ident(n, line) => match cx.lookup(n) {
                Some(Labeled { hyp_index: Some(i), .. }) => Ok(*i),
                Some(_) => Err(Error::new(*line, format!("`{n}` is a line, not an assumption"))),
                None => Err(Error::new(*line, format!("`{n}` is not an assumption here"))),
            },
            other => Err(Error::new(other.line(), "expected an assumption's label")),
        }
    }

    /// Applies arguments in turn: a variable instantiates a `forall`, a line is modus ponens.
    /// When a line meets a `forall`, the leading quantifiers are instantiated by matching the
    /// lines that follow, and the stated formula, against the antecedents.
    fn apply_all(&self, mut o: Open, args: &[Arg], cx: &mut Cx, want: Option<&Formula>) -> Result<Open, Error> {
        let mut i = 0;
        while i < args.len() {
            let a = &args[i];
            let is_var = matches!(a, Arg::Ident(n, _) if cx.lookup(n).is_none() && cx.var_index(n).is_some());
            if is_var {
                let Arg::Ident(y, line) = a else { unreachable!() };
                o = self.instantiate(cx, &o, y).map_err(|m| Error::new(*line, m))?;
                i += 1;
                continue;
            }
            // The run of line arguments from here.
            let mut lines = Vec::new();
            let mut j = i;
            while j < args.len() && !matches!(&args[j], Arg::Ident(n, _) if cx.lookup(n).is_none() && cx.var_index(n).is_some()) {
                lines.push(self.arg_open(&args[j], cx)?);
                j += 1;
            }
            let want = if j == args.len() { want } else { None };
            o = self.feed(o, &lines, &args[i..j], cx, want)?;
            i = j;
        }
        Ok(o)
    }

    /// Feeds `lines` to the antecedents of `o`. Leading `forall`s of `o` are first
    /// instantiated at the variables that make the antecedents match the lines, and what is
    /// left match the stated formula.
    fn feed(&self, mut o: Open, lines: &[Open], args: &[Arg], cx: &mut Cx, want: Option<&Formula>) -> Result<Open, Error> {
        let line = args.first().map_or(0, Arg::line);
        let err = |m: String| Error::new(line, m);
        let body = self.body(cx, &o).map_err(err)?;
        let mut metas = Vec::new();
        let mut cur = body.clone();
        while let Formula::All(x, b) = cur {
            metas.push(x);
            cur = *b;
        }
        if !metas.is_empty() && !lines.is_empty() {
            let meta_set: BTreeSet<String> = metas.iter().cloned().collect();
            let mut sol: HashMap<String, String> = HashMap::new();
            let mut rest = cur;
            for (k, l) in lines.iter().enumerate() {
                let Formula::Imp(a, b) = rest else {
                    return Err(Error::new(args[k].line(), format!("{} has no antecedent left for this line", show(&body))));
                };
                let lb = self.body(cx, l).map_err(err)?;
                if !match_vars(&a, &lb, &meta_set, &mut Vec::new(), &mut sol) {
                    return Err(Error::new(args[k].line(), format!("{} doesn't fit antecedent {} of {}", show(&lb), k + 1, show(&body))));
                }
                rest = *b;
            }
            if let Some(w) = want {
                let mut trial = sol.clone();
                if match_vars(&rest, w, &meta_set, &mut Vec::new(), &mut trial) {
                    sol = trial;
                }
            }
            for x in &metas {
                let Some(y) = sol.get(x) else {
                    return Err(err(format!("can't work out `{x}` in {}: instantiate it with `forall_e`", show(&body))));
                };
                o = self.instantiate(cx, &o, y).map_err(err)?;
            }
        }
        for (l, a) in lines.iter().zip(args) {
            o = self.apply_open(cx, &o, l).map_err(|m| Error::new(a.line(), m))?;
        }
        Ok(o)
    }

    /// `Theory.member templates`: the member's instance, as a premise. A template that
    /// mentions variables in scope makes the premise their closure, instantiated back.
    fn member_instance(&self, theory: &str, label: &str, targs: &[TArg], cx: &mut Cx, line: usize) -> Result<Open, Error> {
        let info = self.member(theory, label, line)?;
        let def = info.def.clone();
        let origin = info.origin.clone();
        if targs.len() != def.params.len() {
            return Err(Error::new(line, format!("`{theory}.{label}` takes {} template(s), got {}", def.params.len(), targs.len())));
        }
        let f = {
            let in_scope = cx.vars(cx.stack.len());
            let mut scope = Scope { params: &mut cx.params, grow: true, bound: Vec::new(), in_scope, new: Some(Vec::new()) };
            let f = self.expand(&def, targs, &[], line, &mut scope)?;
            for x in scope.new.take().unwrap() {
                cx.stack.push(Entry::Var(x));
            }
            f
        };
        // Close over the variables in scope the instance mentions, outermost first.
        let mut extras: Vec<(usize, String)> = f.free_vars().into_iter().map(|x| (cx.var_index(&x).unwrap(), x)).collect();
        extras.sort();
        let prefix: Vec<String> = extras.iter().map(|(_, x)| x.clone()).collect();
        let closed = f.close(&prefix);
        let thm = kernel::assume(&closed).map_err(|m| Error::new(line, m))?;
        {
            let mut origins = self.origins.borrow_mut();
            if !origins.iter().any(|(g, _, _)| *g == closed) {
                origins.push((closed.clone(), origin, label.to_string()));
            }
        }
        cx.add_premise(&closed);
        let mut o = Open { thm, layers: Vec::new() };
        for x in &prefix {
            o = self.instantiate(cx, &o, x).map_err(|m| Error::new(line, m))?;
        }
        Ok(o)
    }

    // ---- rules ----

    fn rule(&self, h: &str, args: &[Arg], cx: &mut Cx, want: &Formula, line: usize) -> Result<Open, Error> {
        let err = |m: String| Error::new(line, m);
        let need = |n: usize, what: &str| -> Result<(), Error> {
            if args.len() == n {
                Ok(())
            } else {
                Err(Error::new(line, format!("`{h}` takes {what}")))
            }
        };
        let at_least = |n: usize, what: &str| -> Result<(), Error> {
            if args.len() >= n {
                Ok(())
            } else {
                Err(Error::new(line, format!("`{h}` takes {what}")))
            }
        };
        match h {
            "imp_i" => {
                at_least(2, "the assumptions to close, then the line")?;
                let (last, hyps) = args.split_last().unwrap();
                let mut o = self.arg_open(last, cx)?;
                for a in hyps.iter().rev() {
                    let i = self.arg_assumption(a, cx)?;
                    o = self.close_at(cx, &o, i, false).map_err(|m| Error::new(a.line(), m))?;
                }
                Ok(o)
            }
            "forall_i" => {
                at_least(2, "the variables to close, then the line")?;
                let (last, xs) = args.split_last().unwrap();
                let mut o = self.arg_open(last, cx)?;
                for a in xs.iter().rev() {
                    let x = self.arg_var(a, cx)?;
                    let i = cx.var_index(&x).unwrap();
                    o = self.close_at(cx, &o, i, true).map_err(|m| Error::new(a.line(), m))?;
                }
                Ok(o)
            }
            "imp_e" => {
                at_least(2, "an implication, then the lines for its antecedents")?;
                let f = self.arg_open(&args[0], cx)?;
                self.apply_all(f, &args[1..], cx, Some(want))
            }
            "forall_e" => {
                at_least(2, "a `forall` line, then the variables")?;
                let mut o = self.arg_open(&args[0], cx)?;
                for a in &args[1..] {
                    let y = self.arg_var(a, cx)?;
                    o = self.instantiate(cx, &o, &y).map_err(|m| Error::new(a.line(), m))?;
                }
                Ok(o)
            }
            "and_i" => {
                need(2, "two lines")?;
                let a = self.arg_open(&args[0], cx)?;
                let b = self.arg_open(&args[1], cx)?;
                let (fa, fb) = (self.body(cx, &a).map_err(err)?, self.body(cx, &b).map_err(err)?);
                self.apply_axiom(cx, Axiom::AndI(fa, fb), &[a, b]).map_err(err)
            }
            "and_e1" | "and_e2" => {
                need(1, "one line, an `and`")?;
                let c = self.arg_open(&args[0], cx)?;
                let Formula::And(fa, fb) = self.body(cx, &c).map_err(err)? else {
                    return Err(err(format!("`{h}` needs an `and`, and {} isn't one", show(&self.body(cx, &c).map_err(err)?))));
                };
                let ax = if h == "and_e1" { Axiom::AndE1(*fa, *fb) } else { Axiom::AndE2(*fa, *fb) };
                self.apply_axiom(cx, ax, &[c]).map_err(err)
            }
            "or_i1" | "or_i2" => {
                need(1, "one line, the side being introduced")?;
                let a = self.arg_open(&args[0], cx)?;
                let fa = self.body(cx, &a).map_err(err)?;
                let Formula::Or(l, r) = want else {
                    return Err(err(format!("`{h}` gives an `or`, and the stated formula {} isn't one", show(want))));
                };
                let (l, r) = ((**l).clone(), (**r).clone());
                let side_ok = if h == "or_i1" { l == fa } else { r == fa };
                if !side_ok {
                    let side = if h == "or_i1" { "left" } else { "right" };
                    return Err(err(format!("`{h}` puts the line on the {side}, but the line is {} and the stated formula is {}", show(&fa), show(want))));
                }
                let ax = if h == "or_i1" { Axiom::OrI1(l, r) } else { Axiom::OrI2(l, r) };
                self.apply_axiom(cx, ax, &[a]).map_err(err)
            }
            "or_e" => {
                need(3, "an `or`, then a line for each side")?;
                let d = self.arg_open(&args[0], cx)?;
                let p = self.arg_open(&args[1], cx)?;
                let q = self.arg_open(&args[2], cx)?;
                let fd = self.body(cx, &d).map_err(err)?;
                let Formula::Or(a, b) = &fd else {
                    return Err(err(format!("`or_e` needs an `or`, and {} isn't one", show(&fd))));
                };
                let fp = self.body(cx, &p).map_err(err)?;
                let fq = self.body(cx, &q).map_err(err)?;
                let c = match (&fp, &fq) {
                    (Formula::Imp(pa, pc), Formula::Imp(qb, qc)) if **pa == **a && **qb == **b && pc == qc => (**pc).clone(),
                    _ => {
                        return Err(err(format!(
                            "`or_e` needs {} -> C and {} -> C, got {} and {}",
                            show(a),
                            show(b),
                            show(&fp),
                            show(&fq)
                        )))
                    }
                };
                let ax = Axiom::OrE((**a).clone(), (**b).clone(), c);
                self.apply_axiom(cx, ax, &[p, q, d]).map_err(err)
            }
            "absurd_e" => {
                need(1, "one line, `absurd`")?;
                let f = self.arg_open(&args[0], cx)?;
                if self.body(cx, &f).map_err(err)? != Formula::Absurd {
                    return Err(err("`absurd_e` needs a line that is `absurd`".into()));
                }
                self.apply_axiom(cx, Axiom::Efq(want.clone()), &[f]).map_err(err)
            }
            "exists_i" => {
                if args.is_empty() || args.len() > 2 {
                    return Err(err("`exists_i` takes the instance, and the witness variable when the formula doesn't show it".into()));
                }
                let l = self.arg_open(&args[0], cx)?;
                let fl = self.body(cx, &l).map_err(err)?;
                let Formula::Ex(x, a) = want else {
                    return Err(err(format!("`exists_i` gives an `exists`, and the stated formula {} isn't one", show(want))));
                };
                let a = (**a).clone();
                let y = if args.len() == 2 {
                    let y = self.arg_var(&args[1], cx)?;
                    if a.subst_vars(&[(x.clone(), y.clone())]) != fl {
                        return Err(err(format!("{} is not {} at `{y}`", show(&fl), show(want))));
                    }
                    y
                } else {
                    // The witness: a variable in scope with `a[y/x]` the line's formula.
                    let in_scope = cx.vars(cx.stack.len());
                    match in_scope.iter().rev().find(|y| a.subst_vars(&[(x.clone(), (*y).clone())]) == fl).cloned() {
                        Some(y) => y,
                        None if in_scope.is_empty() => {
                            return Err(err("`exists_i` needs a witness, and no variable is in scope".into()))
                        }
                        None => return Err(err(format!("{} is not {} at any variable in scope", show(&fl), show(want)))),
                    }
                };
                self.apply_axiom(cx, Axiom::ExI(y, x.clone(), a), &[l]).map_err(err)
            }
            "exists_e" => {
                need(3, "an `exists` line, the assumption that named its witness, and the line reached")?;
                let e = self.arg_open(&args[0], cx)?;
                let ih = self.arg_assumption(&args[1], cx)?;
                let c = self.arg_open(&args[2], cx)?;
                let Entry::Hyp(a_w) = cx.stack[ih].clone() else { unreachable!() };
                let fe = self.body(cx, &e).map_err(err)?;
                let Formula::Ex(x, a) = &fe else {
                    return Err(err(format!("`exists_e` needs an `exists`, and {} isn't one", show(&fe))));
                };
                // The witness: the variable in scope at which the `exists` is the assumption.
                let in_scope = cx.vars(cx.stack.len());
                let label = match &args[1] {
                    Arg::Ident(n, _) => n.clone(),
                    _ => "the assumption".into(),
                };
                let Some(w) = in_scope.iter().rev().find(|w| a.subst_vars(&[(x.clone(), (*w).clone())]) == a_w).cloned() else {
                    return Err(err(format!("`{label}` assumes {}, which isn't {} at any variable in scope", show(&a_w), show(&fe))));
                };
                let iw = cx.var_index(&w).unwrap();
                let c = self.close_at(cx, &c, ih, false).map_err(|m| Error::new(args[2].line(), m))?;
                let Formula::Imp(_, fc) = self.body(cx, &c).map_err(err)? else { unreachable!() };
                if fc.is_free(&w) {
                    return Err(err(format!("the line reached mentions the witness `{w}`: {}", show(&fc))));
                }
                let r = self.close_at(cx, &c, iw, true).map_err(err)?;
                if e.layers.contains(&iw) {
                    return Err(err(format!("the `exists` line depends on the witness `{w}`")));
                }
                let ax = Axiom::ExE(w.clone(), a_w, (*fc).clone());
                self.apply_axiom(cx, ax, &[r, e]).map_err(err)
            }
            _ => unreachable!("not a rule: {h}"),
        }
    }

    /// Closes the layer at `index`: it is pushed inward past the layers after it, one swap
    /// at a time, and then dropped. A line not under it yet is put under it first, which is
    /// a vacuous closing.
    fn close_at(&self, cx: &Cx, o: &Open, index: usize, var: bool) -> Result<Open, String> {
        match (&cx.stack[index], var) {
            (Entry::Var(_), true) | (Entry::Hyp(_), false) => {}
            (e, _) => return Err(format!("{} is in the way", describe(e))),
        }
        let o = if o.layers.contains(&index) { o.clone() } else { self.weaken(cx, o, &union(&o.layers, &[index]))? };
        let pos = o.layers.iter().position(|&i| i == index).unwrap();
        let mut entries = cx.ents(&o.layers);
        let mut thm = o.thm;
        for i in pos..entries.len() - 1 {
            thm = self.swap_inward(&entries[..i], &entries[i], &entries[i + 1], &thm)?;
            entries.swap(i, i + 1);
        }
        let layers = o.layers.iter().copied().filter(|&i| i != index).collect();
        Ok(Open { thm, layers })
    }

    /// `outer[a[b[c]]]` to `outer[b[a[c]]]`: QE1 for two variables, QE5 for a variable and an
    /// assumption, and a propositional swap for two assumptions. Pushing a variable past an
    /// assumption needs the variable not free in it.
    fn swap_inward(&self, outer: &[Entry], a: &Entry, b: &Entry, thm: &Thm) -> Result<Thm, String> {
        let n = outer.len();
        let mut e = outer.to_vec();
        e.push(b.clone());
        e.push(a.clone());
        match (a, b) {
            (Entry::Var(x), Entry::Var(y)) => {
                let t = self.weaken_thm(&e, thm, n, n + 2)?;
                let t = self.inst_under(&e, &t, x)?;
                self.inst_under(&e, &t, y)
            }
            (Entry::Var(x), Entry::Hyp(k)) => {
                if k.is_free(x) {
                    return Err(format!("`{x}` is free in the assumption {}", show(k)));
                }
                let t = self.weaken_thm(&e, thm, n, n + 2)?;
                let t = self.inst_under(&e, &t, x)?;
                let kk = self.identity(outer, k)?;
                let kk = self.weaken_thm(&e, &kk, n + 1, n + 2)?;
                self.mp(&e, &t, &kk)
            }
            (Entry::Hyp(h), Entry::Var(y)) => {
                let t = self.weaken_thm(&e, thm, n, n + 2)?;
                let hh = self.identity(&e[..n + 1], h)?;
                let t = self.mp(&e, &t, &hh)?;
                self.inst_under(&e, &t, y)
            }
            (Entry::Hyp(h), Entry::Hyp(k)) => {
                let t = self.weaken_thm(&e, thm, n, n + 2)?;
                let hh = self.identity(&e[..n + 1], h)?;
                let t = self.mp(&e, &t, &hh)?;
                let kk = self.identity(outer, k)?;
                let kk = self.weaken_thm(&e, &kk, n + 1, n + 2)?;
                self.mp(&e, &t, &kk)
            }
        }
    }

    /// A `forall` under `entries`, instantiated at the variable `y`, which one of them binds.
    fn inst_under(&self, entries: &[Entry], thm: &Thm, y: &str) -> Result<Thm, String> {
        let (x, a) = match unwrap(thm.concl(), entries)? {
            Formula::All(x, a) => (x, *a),
            other => return Err(format!("can't instantiate at `{y}`: {} doesn't start with `forall`", show(&other))),
        };
        let t = self.axiom_at(entries, Axiom::Inst(y.to_string(), x, a))?;
        self.mp(entries, &t, thm)
    }

    /// An axiom instance applied to lines, under the layers they and its formulas need.
    fn apply_axiom(&self, cx: &Cx, ax: Axiom, args: &[Open]) -> Result<Open, String> {
        let mut layers: Vec<usize> = axiom_free_vars(&ax).iter().filter_map(|x| cx.var_index(x)).collect();
        for a in args {
            layers = union(&layers, &a.layers);
        }
        let entries = cx.ents(&layers);
        let mut thm = self.axiom_at(&entries, ax)?;
        for a in args {
            let a = self.weaken(cx, a, &layers)?;
            thm = self.mp(&entries, &thm, &a.thm)?;
        }
        Ok(Open { thm, layers })
    }

    // ---- formulas ----

    fn formula(&self, e: &FExpr, scope: &mut Scope) -> Result<Formula, Error> {
        match e {
            FExpr::Absurd(_) => Ok(Formula::Absurd),
            FExpr::Not(a, _) => Ok(imp(self.formula(a, scope)?, Formula::Absurd)),
            FExpr::And(a, b, _) => Ok(and(self.formula(a, scope)?, self.formula(b, scope)?)),
            FExpr::Or(a, b, _) => Ok(or(self.formula(a, scope)?, self.formula(b, scope)?)),
            FExpr::Imp(a, b, _) => Ok(imp(self.formula(a, scope)?, self.formula(b, scope)?)),
            FExpr::Forall(xs, body, line) | FExpr::Exists(xs, body, line) => {
                for x in xs {
                    if RULES.contains(&x.as_str()) {
                        return Err(Error::new(*line, format!("`{x}` is a rule, not a variable")));
                    }
                    scope.bound.push(x.clone());
                }
                let b = self.formula(body, scope);
                let mut f = b?;
                for x in xs.iter().rev() {
                    scope.bound.pop();
                    f = if matches!(e, FExpr::Forall(..)) { all(x, f) } else { ex(x, f) };
                }
                Ok(f)
            }
            FExpr::Atom { name, args, line } => self.atom(name, args, *line, scope),
        }
    }

    fn individual(&self, a: &TArg, scope: &mut Scope) -> Result<String, Error> {
        match a {
            TArg::Var(x, line) => {
                if scope.bound.contains(x) || scope.in_scope.contains(x) {
                    return Ok(x.clone());
                }
                match &mut scope.new {
                    Some(new) => {
                        if !new.contains(x) {
                            new.push(x.clone());
                        }
                        Ok(x.clone())
                    }
                    None => Err(Error::new(*line, format!("`{x}` is free: bind it with `forall` or `exists`"))),
                }
            }
            TArg::Name(n, line) => Err(Error::new(*line, format!("expected an individual, and `{n}` is capitalized"))),
            TArg::Paren(f) => Err(Error::new(f.line(), "expected an individual: a lowercase variable name")),
        }
    }

    /// `Name targs`: a parameter, a definition, or a new parameter of the theorem.
    fn atom(&self, name: &str, args: &[TArg], line: usize, scope: &mut Scope) -> Result<Formula, Error> {
        if let Some(n) = scope.params.iter().find(|(p, _)| p == name).map(|(_, n)| *n) {
            if args.len() != n {
                return Err(takes(name, n, args.len(), line));
            }
            let vars = args.iter().map(|a| self.individual(a, scope)).collect::<Result<Vec<_>, _>>()?;
            return Ok(Formula::Atom(name.to_string(), vars));
        }
        match self.globals.get(name) {
            Some(Global::Prim(n)) => {
                if args.len() != *n {
                    return Err(takes(name, *n, args.len(), line));
                }
                let vars = args.iter().map(|a| self.individual(a, scope)).collect::<Result<Vec<_>, _>>()?;
                Ok(Formula::Atom(name.to_string(), vars))
            }
            Some(Global::Def(def)) => {
                let def = def.clone();
                if args.len() != def.params.len() {
                    return Err(takes(name, def.params.len(), args.len(), line));
                }
                self.expand(&def, args, &[], line, scope)
            }
            Some(Global::Theory(_)) => Err(Error::new(line, format!("`{name}` is a theory, not a statement"))),
            Some(Global::Theorem(_)) => unreachable!("theorems are lowercase"),
            None if scope.grow => {
                scope.params.push((name.to_string(), args.len()));
                let vars = args.iter().map(|a| self.individual(a, scope)).collect::<Result<Vec<_>, _>>()?;
                Ok(Formula::Atom(name.to_string(), vars))
            }
            None => Err(Error::new(line, format!("`{name}` is not defined"))),
        }
    }

    /// A definition expanded with `args` for its first parameters and `holes` for the rest,
    /// which are individuals.
    fn expand(&self, def: &Def, args: &[TArg], holes: &[String], line: usize, scope: &mut Scope) -> Result<Formula, Error> {
        let mut vars = Vec::new();
        let mut templates = Vec::new();
        for ((p, kind), a) in def.params.iter().zip(args) {
            match kind {
                Kind::Individual => vars.push((p.clone(), self.individual(a, scope)?)),
                Kind::Pred(n) => templates.push((p.clone(), self.template(a, *n, scope)?)),
            }
        }
        vars.extend(def.params[args.len()..].iter().map(|(p, _)| p.clone()).zip(holes.iter().cloned()));
        // Individuals first: templates may mention the caller's variables by the same names.
        def.body.subst_vars(&vars).subst_preds(&templates).map_err(|m| Error::new(line, m))
    }

    /// A predicate argument of arity `n`: for `n = 0` any formula, otherwise a predicate
    /// name with some leading arguments.
    fn template(&self, a: &TArg, n: usize, scope: &mut Scope) -> Result<Template, Error> {
        let (name, args, line): (&str, &[TArg], usize) = match a {
            TArg::Paren(f) => match &**f {
                FExpr::Atom { name, args, line } => (name, args, *line),
                other if n == 0 => return Ok(Template::statement(self.formula(other, scope)?)),
                other => return Err(Error::new(other.line(), format!("a {n}-place predicate is needed, and this is a compound formula"))),
            },
            TArg::Name(name, line) => (name, &[], *line),
            TArg::Var(v, line) => return Err(Error::new(*line, format!("`{v}` is lowercase, so it isn't a predicate"))),
        };
        let holes = hole_names(n);
        let wrong = |m: usize| {
            Error::new(line, format!("`{name}` given {} argument(s) leaves {}, but a {n}-place predicate is needed", args.len(), m))
        };
        let prim = match self.globals.get(name) {
            Some(Global::Prim(m)) => Some(*m),
            _ => None,
        };
        let body = if let Some(m) = scope.params.iter().find(|(p, _)| p == name).map(|(_, m)| *m).or(prim) {
            if args.len() > m || m - args.len() != n {
                return Err(wrong(m.saturating_sub(args.len())));
            }
            let mut vars = args.iter().map(|a| self.individual(a, scope)).collect::<Result<Vec<_>, _>>()?;
            vars.extend(holes.iter().cloned());
            Formula::Atom(name.to_string(), vars)
        } else {
            match self.globals.get(name) {
                Some(Global::Def(def)) => {
                    let def = def.clone();
                    let rest = &def.params[args.len().min(def.params.len())..];
                    if args.len() > def.params.len() || rest.len() != n || rest.iter().any(|(_, k)| *k != Kind::Individual) {
                        return Err(wrong(def.params.len().saturating_sub(args.len())));
                    }
                    self.expand(&def, args, &holes, line, scope)?
                }
                Some(Global::Prim(_)) => unreachable!("handled above"),
                Some(Global::Theory(_)) => return Err(Error::new(line, format!("`{name}` is a theory, not a predicate"))),
                Some(Global::Theorem(_)) => unreachable!(),
                None if scope.grow && args.is_empty() => {
                    // A new parameter of the theorem, of the arity the template needs.
                    scope.params.push((name.to_string(), n));
                    Formula::Atom(name.to_string(), holes.clone())
                }
                None if scope.grow => {
                    let m = scope.params.iter().find(|(p, _)| p == name).map(|(_, m)| *m).unwrap_or(args.len() + n);
                    if !scope.params.iter().any(|(p, _)| p == name) {
                        scope.params.push((name.to_string(), m));
                    }
                    let mut vars = args.iter().map(|a| self.individual(a, scope)).collect::<Result<Vec<_>, _>>()?;
                    vars.extend(holes.iter().cloned());
                    Formula::Atom(name.to_string(), vars)
                }
                None => return Err(Error::new(line, format!("`{name}` is not defined"))),
            }
        };
        Template::new(holes, body).map_err(|m| Error::new(line, m))
    }

    // ---- reasoning under the stack ----

    fn body(&self, cx: &Cx, o: &Open) -> Result<Formula, String> {
        unwrap(o.thm.concl(), &cx.ents(&o.layers))
    }

    // Reasoning under any stack goes through two rules per *shape* of stack (the sequence
    // of variable and assumption layers), each proved once as a checked proof and then used
    // by substitution:
    //   mp:   from  layers[A -> B]  and  layers[A],  get  layers[B]
    //   lift: from  forall (all variables) T,         get  layers[T]
    // Each is proved from the rules for the shape one layer shorter, so every use costs
    // one substitution instead of work exponential in the number of layers.

    /// An axiom instance under `stack`.
    fn axiom_at(&self, stack: &[Entry], ax: Axiom) -> Result<Thm, String> {
        self.lift(stack, &kernel::axiom(ax, &vars(stack))?)
    }

    /// From a theorem closed over `stack`'s variables, the same under `stack`: the lift
    /// rule, or nothing to do when there are no assumptions.
    fn lift(&self, stack: &[Entry], closed: &Thm) -> Result<Thm, String> {
        if !stack.iter().any(|e| matches!(e, Entry::Hyp(_))) {
            return Ok(closed.clone());
        }
        let body = unwrap(closed.concl(), &var_entries(stack))?;
        self.use_shape_rule(stack, Rule::Lift, &[body], &[closed])
    }

    /// Modus ponens under `stack`: `f` proves `A -> B` there, `a` proves `A`.
    fn mp(&self, stack: &[Entry], f: &Thm, a: &Thm) -> Result<Thm, String> {
        if stack.is_empty() {
            return kernel::mp(a, f);
        }
        let fb = unwrap(f.concl(), stack)?;
        let ab = unwrap(a.concl(), stack)?;
        let Formula::Imp(p, q) = &fb else {
            return Err(format!("{} is not an implication", show(&fb)));
        };
        if **p != ab {
            return Err(format!("{} needs {}, but got {}", show(&fb), show(p), show(&ab)));
        }
        self.use_shape_rule(stack, Rule::Mp, &[(**p).clone(), (**q).clone()], &[f, a])
    }

    /// Applies `rule` for `stack`'s shape. Its parameters are the assumptions' predicates,
    /// then the formulas `fs`, each abstracted over the stack's variables.
    fn use_shape_rule(&self, stack: &[Entry], rule: Rule, fs: &[Formula], ev: &[&Thm]) -> Result<Thm, String> {
        let lemma = self.shape_rule(rule, &shape(stack))?;
        let vs = vars(stack);
        let mut ts = Vec::new();
        for (i, e) in stack.iter().enumerate() {
            if let Entry::Hyp(h) = e {
                ts.push(abstract_over(h, &vars(&stack[..i]))?);
            }
        }
        for f in fs {
            ts.push(abstract_over(f, &vs)?);
        }
        // The templates mention only the stack's variables, which are their holes.
        lemma.apply(&ts, &[], ev)
    }

    /// `rule` for a shape, proved on first use.
    fn shape_rule(&self, rule: Rule, shape: &str) -> Result<Rc<Lemma>, String> {
        let key = (rule, shape.to_string());
        if let Some(l) = self.rules.borrow().get(&key) {
            return Ok(l.clone());
        }
        // An abstract stack of this shape: variables `_v...`; assumptions `#H...` applied to
        // the variables before them. Neither kind of name can be written by a user.
        let mut stack = Vec::new();
        let mut vs = Vec::new();
        let mut params = Vec::new();
        for (i, c) in shape.chars().enumerate() {
            if c == 'V' {
                let v = format!("_v{i}");
                vs.push(v.clone());
                stack.push(Entry::Var(v));
            } else {
                let h = format!("#H{i}");
                params.push((h.clone(), vs.len()));
                stack.push(Entry::Hyp(Formula::Atom(h, vs.clone())));
            }
        }
        let k = vs.len();
        let atom = |p: &str| Formula::Atom(p.to_string(), vs.clone());
        let (inner, last) = stack.split_at(stack.len() - 1);
        let lemma = match rule {
            Rule::Mp => {
                params.push(("#A".into(), k));
                params.push(("#B".into(), k));
                let (a, b) = (atom("#A"), atom("#B"));
                let p1 = wrap(&stack, imp(a.clone(), b.clone()));
                let p2 = wrap(&stack, a.clone());
                let f = kernel::assume(&p1)?;
                let x = kernel::assume(&p2)?;
                let ax = match &last[0] {
                    Entry::Var(y) => Axiom::Dist(y.clone(), a, b.clone()),
                    Entry::Hyp(h) => Axiom::Imp2(h.clone(), a, b.clone()),
                };
                let t = self.axiom_at(inner, ax)?;
                let t = self.mp(inner, &t, &f)?;
                let t = self.mp(inner, &t, &x)?;
                Lemma::new(params, vec![p1, p2], wrap(&stack, b), &t)?
            }
            Rule::Lift => {
                params.push(("#T".into(), k));
                let t = atom("#T");
                let hyp = t.clone().close(&vs);
                let p = kernel::assume(&hyp)?;
                // Under the shorter shape: its own lift, with the last layer folded into T.
                let proved = match &last[0] {
                    Entry::Var(_) => self.lift(inner, &p)?,
                    Entry::Hyp(h) => {
                        let under = self.lift(inner, &p)?;
                        let kk = self.lift(inner, &kernel::axiom(Axiom::Imp1(t.clone(), h.clone()), &vs)?)?;
                        self.mp(inner, &kk, &under)?
                    }
                };
                Lemma::new(params, vec![hyp], wrap(&stack, t), &proved)?
            }
        };
        let lemma = Rc::new(lemma);
        self.rules.borrow_mut().insert(key, lemma.clone());
        Ok(lemma)
    }

    /// The same line under more layers, `target`, which include its own: `vac` for a variable,
    /// `imp1` for an assumption, each inserted at its place.
    fn weaken(&self, cx: &Cx, o: &Open, target: &[usize]) -> Result<Open, String> {
        let mut cur = o.layers.clone();
        let mut thm = o.thm.clone();
        for &k in target {
            if cur.contains(&k) {
                continue;
            }
            let pos = cur.partition_point(|&i| i < k);
            let outer = cx.ents(&cur[..pos]);
            let phi = unwrap(thm.concl(), &outer)?;
            let ax = match &cx.stack[k] {
                Entry::Var(y) => Axiom::Vac(y.clone(), phi),
                Entry::Hyp(h) => Axiom::Imp1(phi, h.clone()),
            };
            let t = self.axiom_at(&outer, ax)?;
            thm = self.mp(&outer, &t, &thm)?;
            cur.insert(pos, k);
        }
        Ok(Open { thm, layers: cur })
    }

    /// A theorem under `stack[..from]`, moved under `stack[..to]`.
    fn weaken_thm(&self, stack: &[Entry], thm: &Thm, from: usize, to: usize) -> Result<Thm, String> {
        let mut thm = thm.clone();
        for d in from..to {
            let phi = unwrap(thm.concl(), &stack[..d])?;
            let ax = match &stack[d] {
                Entry::Var(y) => Axiom::Vac(y.clone(), phi),
                Entry::Hyp(h) => Axiom::Imp1(phi, h.clone()),
            };
            let t = self.axiom_at(&stack[..d], ax)?;
            thm = self.mp(&stack[..d], &t, &thm)?;
        }
        Ok(thm)
    }

    /// `A -> A` under `stack`.
    fn identity(&self, stack: &[Entry], a: &Formula) -> Result<Thm, String> {
        let aa = imp(a.clone(), a.clone());
        let s = self.axiom_at(stack, Axiom::Imp2(a.clone(), aa.clone(), a.clone()))?;
        let k = self.axiom_at(stack, Axiom::Imp1(a.clone(), aa))?;
        let t = self.mp(stack, &s, &k)?;
        let k2 = self.axiom_at(stack, Axiom::Imp1(a.clone(), a.clone()))?;
        self.mp(stack, &t, &k2)
    }

    /// A `forall` line instantiated at the variable `y`.
    fn instantiate(&self, cx: &Cx, o: &Open, y: &str) -> Result<Open, String> {
        let iy = cx.var_index(y).ok_or_else(|| format!("`{y}` is not a variable in scope"))?;
        let layers = union(&o.layers, &[iy]);
        let o = self.weaken(cx, o, &layers)?;
        let thm = self.inst_under(&cx.ents(&layers), &o.thm, y)?;
        Ok(Open { thm, layers })
    }

    /// Modus ponens between two lines under whatever layers they need.
    fn apply_open(&self, cx: &Cx, f: &Open, a: &Open) -> Result<Open, String> {
        let layers = union(&f.layers, &a.layers);
        let f = self.weaken(cx, f, &layers)?;
        let a = self.weaken(cx, a, &layers)?;
        Ok(Open { thm: self.mp(&cx.ents(&layers), &f.thm, &a.thm)?, layers })
    }

    // ---- citing theorems ----

    /// `t templates lines`: the theorem's instance, with lines fed to its leading
    /// antecedents. Parameters not given as templates are inferred from the lines, or from
    /// the stated formula.
    fn call(&self, h: &str, info: &TheoremInfo, targs: &[TArg], args: &[Arg], cx: &mut Cx, want: Option<&Formula>, line: usize) -> Result<Open, Error> {
        let err = |m: String| Error::new(line, m);
        let lemma = &info.lemma;
        let params = lemma.params();
        if targs.len() > params.len() {
            return Err(err(format!("`{h}` takes {} template(s)", params.len())));
        }
        let mut sol: Vec<Option<Template>> = vec![None; params.len()];
        {
            let in_scope = cx.vars(cx.stack.len());
            let mut scope = Scope { params: &mut cx.params, grow: true, bound: Vec::new(), in_scope, new: Some(Vec::new()) };
            for (i, a) in targs.iter().enumerate() {
                sol[i] = Some(self.template(a, params[i].1, &mut scope)?);
            }
            for x in scope.new.take().unwrap() {
                cx.stack.push(Entry::Var(x));
            }
        }
        let mut given = Vec::new();
        for a in args {
            given.push(self.arg_open(a, cx)?);
        }
        // The antecedents the lines are fed to, under the theorem's leading quantifiers.
        let mut ants = Vec::new();
        let mut rest = lemma.concl();
        let mut binders = Vec::new();
        while let Formula::All(x, b) = rest {
            binders.push(x.clone());
            rest = b;
        }
        for _ in 0..given.len() {
            match rest {
                Formula::Imp(p, q) => {
                    ants.push(p.as_ref());
                    rest = q;
                }
                _ => return Err(err(format!("`{h}` has {} antecedent(s), and {} line(s) were given", ants.len(), given.len()))),
            }
        }
        if sol.iter().any(Option::is_none) {
            let index: HashMap<&str, usize> = params.iter().enumerate().map(|(i, (p, _))| (p.as_str(), i)).collect();
            let outer: BTreeSet<String> = cx.vars(cx.stack.len()).into_iter().collect();
            let mut targets: Vec<(&Formula, Formula)> = Vec::new();
            for (p, o) in ants.iter().zip(&given) {
                targets.push((p, self.body(cx, o).map_err(err)?));
            }
            if let Some(w) = want {
                targets.push((rest, w.clone()));
            }
            // The theorem's leading binders stand for whatever variables the lines have there,
            // so a solution may mention them as if they were in scope.
            let bound: BTreeSet<String> = binders.iter().cloned().collect();
            let outer: BTreeSet<String> = outer.union(&bound).cloned().collect();
            for (pat, b) in &targets {
                // A match that fails partway leaves nothing behind.
                let mut trial = sol.clone();
                if hom(pat, b, &index, &outer, &mut Vec::new(), &mut trial) {
                    sol = trial;
                }
            }
        }
        let mut templates = Vec::new();
        for ((p, _), t) in params.iter().zip(sol) {
            match t {
                Some(t) => templates.push(t),
                None => return Err(err(format!("can't work out `{p}` for `{h}`: pass it as a template"))),
            }
        }
        // The instance is closed over the variables its templates mention, outermost first,
        // and instantiated back at them, like a theory member.
        let mut extras: Vec<(usize, String)> = templates
            .iter()
            .flat_map(Template::extras)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .map(|x| (cx.var_index(&x).expect("template variables are in scope"), x))
            .collect();
        extras.sort();
        let prefix: Vec<String> = extras.into_iter().map(|(_, x)| x).collect();
        // The theorem's premises, instantiated the same way and closed over the same prefix,
        // which is what the kernel will ask for. Each keeps the origin of the premise it came from.
        let map: Vec<(String, Template)> = params.iter().map(|(p, _)| p.clone()).zip(templates.iter().cloned()).collect();
        let mut hyp_thms = Vec::new();
        for hyp in lemma.hyps() {
            let inst = hyp.subst_preds(&map).map_err(err)?.close(&prefix);
            if inst != *hyp {
                let (origin, label) = self.origin(hyp);
                let mut origins = self.origins.borrow_mut();
                if !origins.iter().any(|(g, _, _)| *g == inst) {
                    origins.push((inst.clone(), origin, label));
                }
            }
            hyp_thms.push(kernel::assume(&inst).map_err(err)?);
            cx.add_premise(&inst);
        }
        let refs: Vec<&Thm> = hyp_thms.iter().collect();
        let thm = lemma.apply(&templates, &prefix, &refs).map_err(|m| err(format!("{h}: {m}")))?;
        let mut o = Open { thm, layers: Vec::new() };
        for x in &prefix {
            o = self.instantiate(cx, &o, x).map_err(err)?;
        }
        self.feed(o, &given, args, cx, want)
    }
}

/// The formulas an axiom instance is built from.
fn axiom_formulas(ax: &Axiom) -> Vec<&Formula> {
    match ax {
        Axiom::Imp1(a, b) | Axiom::AndI(a, b) | Axiom::AndE1(a, b) | Axiom::AndE2(a, b) | Axiom::OrI1(a, b) | Axiom::OrI2(a, b) => vec![a, b],
        Axiom::Imp2(a, b, c) | Axiom::OrE(a, b, c) => vec![a, b, c],
        Axiom::Efq(a) | Axiom::Vac(_, a) | Axiom::Inst(_, _, a) | Axiom::ExI(_, _, a) => vec![a],
        Axiom::Dist(_, a, b) | Axiom::ExE(_, a, b) => vec![a, b],
    }
}

/// The argument counts `name` is applied to somewhere in `e`.
fn applied_arities(e: &FExpr, name: &str, out: &mut BTreeSet<usize>) {
    match e {
        FExpr::Absurd(_) => {}
        FExpr::Atom { name: n, args, .. } => {
            if n == name {
                out.insert(args.len());
            }
            for a in args {
                if let TArg::Paren(f) = a {
                    applied_arities(f, name, out);
                }
                if let TArg::Name(n, _) = a {
                    if n == name {
                        out.insert(0);
                    }
                }
            }
        }
        FExpr::Not(a, _) | FExpr::Forall(_, a, _) | FExpr::Exists(_, a, _) => applied_arities(a, name, out),
        FExpr::And(a, b, _) | FExpr::Or(a, b, _) | FExpr::Imp(a, b, _) => {
            applied_arities(a, name, out);
            applied_arities(b, name, out);
        }
    }
}

/// Matches `pat` against `tgt`, solving the variables in `metas` as the variables of `tgt`
/// they stand against. Binders are paired through `env`; a solution may not be a variable
/// bound inside `tgt`.
fn match_vars(
    pat: &Formula,
    tgt: &Formula,
    metas: &BTreeSet<String>,
    env: &mut Vec<(String, String)>,
    sol: &mut HashMap<String, String>,
) -> bool {
    fn var(x: &String, y: &String, metas: &BTreeSet<String>, env: &[(String, String)], sol: &mut HashMap<String, String>) -> bool {
        if let Some(i) = env.iter().rposition(|(p, _)| p == x) {
            return env[i].1 == *y && !env[i + 1..].iter().any(|(_, t)| t == y);
        }
        if env.iter().any(|(_, t)| t == y) {
            return false;
        }
        if metas.contains(x) {
            return match sol.get(x) {
                Some(z) => z == y,
                None => {
                    sol.insert(x.clone(), y.clone());
                    true
                }
            };
        }
        x == y
    }
    match (pat, tgt) {
        (Formula::Atom(p, xs), Formula::Atom(q, ys)) => {
            p == q && xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| var(x, y, metas, env, sol))
        }
        (Formula::Absurd, Formula::Absurd) => true,
        (Formula::And(a, b), Formula::And(c, d)) | (Formula::Or(a, b), Formula::Or(c, d)) | (Formula::Imp(a, b), Formula::Imp(c, d)) => {
            match_vars(a, c, metas, env, sol) && match_vars(b, d, metas, env, sol)
        }
        (Formula::All(x, a), Formula::All(y, b)) | (Formula::Ex(x, a), Formula::Ex(y, b)) => {
            env.push((x.clone(), y.clone()));
            let ok = match_vars(a, b, metas, env, sol);
            env.pop();
            ok
        }
        _ => false,
    }
}

// ---- inferring a theorem's predicate arguments ----

/// Matches an antecedent against a line's formula, solving predicate parameters applied to
/// distinct bound variables. `env` pairs the antecedent's binders with the formula's; `outer`
/// are variables in scope a solution may mention.
fn hom(
    pat: &Formula,
    tgt: &Formula,
    params: &HashMap<&str, usize>,
    outer: &BTreeSet<String>,
    env: &mut Vec<(String, String)>,
    sol: &mut [Option<Template>],
) -> bool {
    // The formula's binder for the antecedent's bound variable, unless an inner binder of the
    // formula reuses its name.
    let image = |x: &String, env: &[(String, String)]| {
        let i = env.iter().rposition(|(p, _)| p == x)?;
        let t = &env[i].1;
        (!env[i + 1..].iter().any(|(_, u)| u == t)).then(|| t.clone())
    };
    match (pat, tgt) {
        (Formula::Atom(p, pargs), _) if params.contains_key(p.as_str()) => {
            let Some(args) = pargs.iter().map(|a| image(a, env)).collect::<Option<Vec<_>>>() else { return false };
            let i = params[p.as_str()];
            match &sol[i] {
                Some(t) => t.apply(&args) == *tgt,
                None => {
                    let distinct: BTreeSet<&String> = args.iter().collect();
                    let ok = |v: &String| args.contains(v) || (outer.contains(v) && !env.iter().any(|(_, t)| t == v));
                    if distinct.len() != args.len() || !tgt.free_vars().iter().all(ok) {
                        return false;
                    }
                    let holes = hole_names(args.len());
                    let s: Vec<(String, String)> = args.into_iter().zip(holes.iter().cloned()).collect();
                    sol[i] = Template::new(holes, tgt.subst_vars(&s)).ok();
                    sol[i].is_some()
                }
            }
        }
        (Formula::Atom(p, xs), Formula::Atom(q, ys)) => {
            p == q && xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| image(x, env).as_ref() == Some(y))
        }
        (Formula::Absurd, Formula::Absurd) => true,
        (Formula::And(a, b), Formula::And(c, d)) | (Formula::Or(a, b), Formula::Or(c, d)) | (Formula::Imp(a, b), Formula::Imp(c, d)) => {
            hom(a, c, params, outer, env, sol) && hom(b, d, params, outer, env, sol)
        }
        (Formula::All(x, a), Formula::All(y, b)) | (Formula::Ex(x, a), Formula::Ex(y, b)) => {
            env.push((x.clone(), y.clone()));
            let ok = hom(a, b, params, outer, env, sol);
            env.pop();
            ok
        }
        _ => false,
    }
}
