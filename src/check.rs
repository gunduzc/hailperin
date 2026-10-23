//! Checks a file: definitions, primitives and proofs, in order.
//!
//! Nothing here is trusted. Every theorem comes from the kernel; this module only decides
//! which kernel functions to call, by reading formulas, matching axiom shapes and
//! inferring predicate arguments.
//!
//! Inside `forall`, `assume` and `obtain` blocks, the checker keeps a stack of the block
//! variables and assumptions in scope. A theorem made inside is still closed: its outer
//! layers are those entries (`forall x $ …` for a variable, `imp A …` for an assumption).
//! Modus ponens under the layers uses `dist` and `imp2`; leaving a block is free.

use crate::kernel::{self, Axiom, Lemma, Thm};
use crate::parse::{Block, Expr, Item, ParamDecl, Part, Step};
use crate::syntax::{all, and, ex, fresh, hole_names, imp, or, Formula, Template};
use crate::Error;
use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap};

const CONNECTIVES: &[&str] = &["absurd", "not", "and", "or", "imp", "forall", "exists"];
const AXIOMS: &[&str] = &[
    "imp1", "imp2", "and_i", "and_e1", "and_e2", "or_i1", "or_i2", "or_e", "efq", "dist", "vac", "inst",
    "ex_i", "ex_e",
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    Individual,
    Pred(usize),
}

struct Def {
    params: Vec<(String, Kind)>,
    body: Formula,
}

enum Global {
    Prim(usize),
    Def(Def),
    /// A named set of premises: `given` parts, expanded where used.
    Set(Vec<Part>),
    Proof(ProofInfo),
}

/// A checked proof, with where each parameter and premise came from.
struct ProofInfo {
    lemma: Lemma,
    params: Vec<Slot>,
    premises: Vec<Slot>,
}

/// A parameter or premise's name, and the sets it came in through.
#[derive(Clone)]
struct Slot {
    name: String,
    sets: Vec<String>,
}

#[derive(Default)]
pub struct Checker {
    globals: HashMap<String, Global>,
    /// Rules for reasoning under blocks, proved once per shape (see `shape_rule`).
    rules: RefCell<HashMap<String, Lemma>>,
}

/// A block variable or an assumption in scope.
#[derive(Clone, Debug)]
enum Entry {
    Var(String),
    Hyp(Formula),
}

/// A theorem whose conclusion is the first `depth` entries wrapped around a body.
#[derive(Clone)]
struct Open {
    thm: Thm,
    depth: usize,
}

/// A proof being checked: its signature so far, and what's in scope.
struct Proving {
    params: Vec<(String, usize)>,
    premises: Vec<Formula>,
    param_slots: Vec<Slot>,
    premise_slots: Vec<Slot>,
    /// The sets of premises already included.
    sets: BTreeSet<String>,
    cx: Cx,
}

impl Default for Proving {
    fn default() -> Self {
        let cx = Cx { preds: HashMap::new(), stack: Vec::new(), ev: Vec::new(), names: BTreeSet::new() };
        Proving {
            params: Vec::new(),
            premises: Vec::new(),
            param_slots: Vec::new(),
            premise_slots: Vec::new(),
            sets: BTreeSet::new(),
            cx,
        }
    }
}

/// Names visible while reading a formula.
struct Scope<'a> {
    preds: &'a HashMap<String, usize>,
    bound: Vec<String>,
    /// Free individual names are allowed (formula arguments in evidence; closed over later).
    allow_free: bool,
}

/// Everything in scope inside one proof.
struct Cx {
    preds: HashMap<String, usize>,
    stack: Vec<Entry>,
    ev: Vec<(String, Open)>,
    names: BTreeSet<String>,
}

impl Cx {
    fn lookup(&self, name: &str) -> Option<&Open> {
        self.ev.iter().rev().find(|(n, _)| n == name).map(|(_, e)| e)
    }

    fn vars(&self, depth: usize) -> Vec<String> {
        vars(&self.stack[..depth])
    }

    fn var_index(&self, name: &str) -> Option<usize> {
        self.stack.iter().position(|e| matches!(e, Entry::Var(v) if v == name))
    }

    fn scope(&self, allow_free: bool) -> Scope<'_> {
        Scope { preds: &self.preds, bound: self.vars(self.stack.len()), allow_free }
    }
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
    let mut cur = f.clone();
    for e in entries {
        cur = match (e, cur) {
            (Entry::Var(y), Formula::All(z, b)) => {
                if z == *y {
                    *b
                } else {
                    b.subst_vars(&[(z, y.clone())])
                }
            }
            (Entry::Hyp(h), Formula::Imp(p, b)) if *p == *h => *b,
            (_, other) => return Err(format!("{other} doesn't have the shape of the current block")),
        };
    }
    Ok(cur)
}

/// `entries` wrapped around `body`: `forall` for a variable, `imp` for an assumption.
fn wrap(entries: &[Entry], body: Formula) -> Formula {
    entries.iter().rev().fold(body, |acc, e| match e {
        Entry::Var(v) => all(v, acc),
        Entry::Hyp(h) => imp(h.clone(), acc),
    })
}

/// `V` for each variable layer and `H` for each assumption.
fn shape(entries: &[Entry]) -> String {
    entries.iter().map(|e| if matches!(e, Entry::Var(_)) { 'V' } else { 'H' }).collect()
}

/// `f` as a predicate of `vars`, which become its holes.
fn abstract_over(f: &Formula, vars: &[String]) -> Template {
    let holes = hole_names(vars.len());
    let s: Vec<(String, String)> = vars.iter().cloned().zip(holes.iter().cloned()).collect();
    Template { body: f.subst_vars(&s), holes }
}

fn upper(name: &str) -> bool {
    name.chars().next().is_some_and(char::is_uppercase)
}

fn reserved(name: &str) -> bool {
    CONNECTIVES.contains(&name) || AXIOMS.contains(&name) || name == "mp"
}

/// Arguments that are formulas or predicates rather than evidence.
fn formula_like(e: &Expr) -> bool {
    match e.spine().0 {
        Expr::Name(n, _) => upper(n) || CONNECTIVES.contains(&n.as_str()),
        _ => false,
    }
}

/// The depth that covers every block variable free in `fs`.
fn var_depth<'a>(cx: &Cx, fs: impl IntoIterator<Item = &'a Formula>) -> usize {
    fs.into_iter().flat_map(|f| f.free_vars()).filter_map(|x| cx.var_index(&x)).map(|i| i + 1).max().unwrap_or(0)
}

/// `want` with its first `n` `forall`s removed, their variables renamed to `names`.
fn strip_foralls(want: &Formula, names: &[String]) -> Option<Formula> {
    let mut cur = want.clone();
    for y in names {
        cur = match cur {
            Formula::All(z, b) if z == *y => *b,
            Formula::All(z, b) => b.subst_vars(&[(z, y.clone())]),
            _ => return None,
        };
    }
    Some(cur)
}

impl Checker {
    /// Checks one item; returns the name and conclusion of a proof.
    pub fn item(&mut self, item: &Item) -> Result<Option<(String, Formula)>, Error> {
        match item {
            Item::Let { name, params, body, line } => {
                self.new_global(name, *line, true)?;
                let g = match body {
                    None => self.primitive(params)?,
                    Some(body) => self.definition(params, body)?,
                };
                self.globals.insert(name.clone(), g);
                Ok(None)
            }
            Item::Set { name, parts, line } => {
                self.new_global(name, *line, true)?;
                // Check the premises now, as the start of a proof.
                self.givens(parts).map_err(|e| Error::new(e.line, format!("{name}: {}", e.msg)))?;
                self.globals.insert(name.clone(), Global::Set(parts.clone()));
                Ok(None)
            }
            Item::Proof { name, parts, line } => {
                self.new_global(name, *line, false)?;
                let info = self.proof(parts, *line).map_err(|e| Error::new(e.line, format!("{name}: {}", e.msg)))?;
                let concl = info.lemma.concl().clone();
                self.globals.insert(name.clone(), Global::Proof(info));
                Ok(Some((name.clone(), concl)))
            }
        }
    }

    fn new_global(&self, name: &str, line: usize, uppercase: bool) -> Result<(), Error> {
        if reserved(name) {
            return Err(Error::new(line, format!("`{name}` is built in")));
        }
        if self.globals.contains_key(name) {
            return Err(Error::new(line, format!("`{name}` is already defined")));
        }
        if uppercase != upper(name) {
            let want = if uppercase { "uppercase (it's a statement or predicate)" } else { "lowercase (it's a proof)" };
            return Err(Error::new(line, format!("`{name}` should be {want}")));
        }
        Ok(())
    }

    fn primitive(&self, params: &[ParamDecl]) -> Result<Global, Error> {
        for p in params {
            if upper(&p.name) || p.arity.is_some() {
                return Err(Error::new(p.line, "a primitive's parameters are individuals: lowercase names"));
            }
        }
        distinct(params.iter().map(|p| (&p.name, p.line)))?;
        Ok(Global::Prim(params.len()))
    }

    fn definition(&self, params: &[ParamDecl], body: &Expr) -> Result<Global, Error> {
        distinct(params.iter().map(|p| (&p.name, p.line)))?;
        let kinds = param_kinds(params, body)?;
        let mut preds = HashMap::new();
        let mut bound = Vec::new();
        for (name, kind) in &kinds {
            self.local_name(name, body.line())?;
            match kind {
                Kind::Individual => bound.push(name.clone()),
                Kind::Pred(n) => {
                    preds.insert(name.clone(), *n);
                }
            }
        }
        let mut scope = Scope { preds: &preds, bound, allow_free: false };
        let body = self.formula(body, &mut scope)?;
        Ok(Global::Def(Def { params: kinds, body }))
    }

    fn local_name(&self, name: &str, line: usize) -> Result<(), Error> {
        if reserved(name) || self.globals.contains_key(name) {
            return Err(Error::new(line, format!("`{name}` is already defined")));
        }
        Ok(())
    }

    /// Reserves a name inside a proof: no shadowing, and the right case.
    fn claim(&self, cx: &mut Cx, name: &str, line: usize, uppercase: bool) -> Result<(), Error> {
        self.local_name(name, line)?;
        if !cx.names.insert(name.to_string()) {
            return Err(Error::new(line, format!("`{name}` is already used in this proof")));
        }
        if uppercase != upper(name) {
            let want = if uppercase { "uppercase" } else { "lowercase" };
            return Err(Error::new(line, format!("`{name}` should be {want}")));
        }
        Ok(())
    }

    /// Checks the `given`s of a set of premises.
    fn givens(&self, parts: &[Part]) -> Result<(), Error> {
        let mut st = Proving::default();
        for part in parts {
            match part {
                Part::Have(_) | Part::Shows { .. } => unreachable!("a set has only `given`s"),
                _ => {
                    self.part(part, &mut st, false, &[])?;
                }
            }
        }
        Ok(())
    }

    fn proof(&self, parts: &[Part], line: usize) -> Result<ProofInfo, Error> {
        let mut st = Proving::default();
        for (i, part) in parts.iter().enumerate() {
            if let Some(lemma) = self.part(part, &mut st, i + 1 == parts.len(), &[])? {
                return Ok(ProofInfo { lemma, params: st.param_slots, premises: st.premise_slots });
            }
        }
        Err(Error::new(line, "a proof needs a `shows`"))
    }

    /// One part of a proof, which came in through the sets `origin`; the lemma when it's
    /// the `shows`.
    fn part(&self, part: &Part, st: &mut Proving, last: bool, origin: &[String]) -> Result<Option<Lemma>, Error> {
        if let Part::All { set, line } = part {
            let Some(Global::Set(parts)) = self.globals.get(set) else {
                return Err(Error::new(*line, format!("`{set}` is not a set of premises")));
            };
            if !st.sets.insert(set.clone()) {
                // Already included through another set: its items came in through these too.
                for s in st.param_slots.iter_mut().chain(&mut st.premise_slots) {
                    if s.sets.contains(set) {
                        s.sets.extend(origin.iter().filter(|o| !s.sets.contains(o)).cloned().collect::<Vec<_>>());
                    }
                }
                return Ok(None);
            }
            let mut inner = origin.to_vec();
            inner.push(set.clone());
            for p in parts {
                // A clash inside the set is reported where the proof includes it.
                self.part(p, st, false, &inner).map_err(|e| if origin.is_empty() { Error::new(*line, e.msg) } else { e })?;
            }
            return Ok(None);
        }
        let slot = |name: &String| Slot { name: name.clone(), sets: origin.to_vec() };
        let Proving { params, premises, param_slots, premise_slots, cx, .. } = st;
        match part {
            Part::All { .. } => unreachable!("handled above"),
            Part::Param { name, arity, line } => {
                self.claim(cx, name, *line, true)?;
                cx.preds.insert(name.clone(), *arity);
                params.push((name.clone(), *arity));
                param_slots.push(slot(name));
            }
            Part::Premise { name, stmt, line } => {
                self.claim(cx, name, *line, false)?;
                let f = self.formula(stmt, &mut cx.scope(false))?;
                let thm = kernel::assume(&f).map_err(|m| Error::new(*line, m))?;
                premises.push(f);
                premise_slots.push(slot(name));
                cx.ev.push((name.clone(), Open { thm, depth: 0 }));
            }
            Part::Have(step) => self.have(step, cx)?,
            Part::Shows { stmt, by, line } => {
                if !last {
                    return Err(Error::new(*line, "`shows` must be the last part of a proof"));
                }
                let want = self.formula(stmt, &mut cx.scope(false))?;
                let o = self.justify(by, cx, Some(&want), *line)?;
                let lemma = Lemma::new(std::mem::take(params), std::mem::take(premises), want, &o.thm);
                return lemma.map(Some).map_err(|m| Error::new(*line, m));
            }
        }
        Ok(None)
    }

    fn have(&self, step: &Step, cx: &mut Cx) -> Result<(), Error> {
        let want = step.stmt.as_ref().map(|s| self.formula(s, &mut cx.scope(false))).transpose()?;
        let o = self.justify(&step.by, cx, want.as_ref(), step.line)?;
        self.claim(cx, &step.name, step.line, false)?;
        cx.ev.push((step.name.clone(), o));
        Ok(())
    }

    /// Evidence, checked against the stated formula if there is one. It stays at its own
    /// depth, so a step that doesn't use an assumption doesn't depend on it.
    fn justify(&self, by: &Expr, cx: &mut Cx, want: Option<&Formula>, line: usize) -> Result<Open, Error> {
        let o = self.evidence(by, cx, want)?;
        if let Some(w) = want {
            let got = self.body(cx, &o).map_err(|m| Error::new(line, m))?;
            if got != *w {
                return Err(Error::new(line, format!("this proves {got}, not {w}")));
            }
        }
        Ok(o)
    }

    // ---- formulas ----

    fn formula(&self, e: &Expr, scope: &mut Scope) -> Result<Formula, Error> {
        let (head, args) = e.spine();
        let (h, line) = match head {
            Expr::Name(h, line) => (h.as_str(), *line),
            Expr::Hole(line) => return Err(Error::new(*line, "`_` is only allowed on the right of `|>`")),
            other => return Err(Error::new(other.line(), "a block is evidence, not a formula")),
        };
        let arity = |n: usize| {
            if args.len() == n {
                Ok(())
            } else {
                Err(Error::new(line, format!("`{h}` takes {n} argument(s), got {}", args.len())))
            }
        };
        match h {
            "absurd" => {
                arity(0)?;
                Ok(Formula::Absurd)
            }
            "not" => {
                arity(1)?;
                Ok(imp(self.formula(args[0], scope)?, Formula::Absurd))
            }
            "and" | "or" | "imp" => {
                if args.len() < 2 {
                    return Err(Error::new(line, format!("`{h}` takes at least 2 arguments")));
                }
                let fs = args.iter().map(|a| self.formula(a, scope)).collect::<Result<Vec<_>, _>>()?;
                let join = match h {
                    "and" => and,
                    "or" => or,
                    _ => imp,
                };
                Ok(fs.into_iter().rev().reduce(|acc, f| join(f, acc)).unwrap())
            }
            "forall" | "exists" => {
                arity(2)?;
                let x = match args[0] {
                    Expr::Name(x, _) if !upper(x) && !reserved(x) => x.clone(),
                    other => return Err(Error::new(other.line(), "a quantifier binds a lowercase variable name")),
                };
                scope.bound.push(x.clone());
                let body = self.formula(args[1], scope);
                scope.bound.pop();
                let body = body?;
                Ok(if h == "forall" { all(&x, body) } else { ex(&x, body) })
            }
            _ if !upper(h) => Err(Error::new(line, format!("`{h}` is lowercase, so it isn't a statement or predicate"))),
            _ => self.predicate_use(h, &args, line, scope),
        }
    }

    fn individual(&self, e: &Expr, scope: &Scope) -> Result<String, Error> {
        match e {
            Expr::Name(x, line) if !upper(x) && !reserved(x) => {
                if scope.allow_free || scope.bound.contains(x) {
                    Ok(x.clone())
                } else {
                    Err(Error::new(*line, format!("`{x}` is free: bind it with `forall` or `exists`")))
                }
            }
            other => Err(Error::new(other.line(), "expected an individual: a lowercase variable name")),
        }
    }

    /// `P x y`: a predicate parameter, a primitive or a definition, applied.
    fn predicate_use(&self, h: &str, args: &[&Expr], line: usize, scope: &mut Scope) -> Result<Formula, Error> {
        let n = match (scope.preds.get(h), self.globals.get(h)) {
            (Some(n), _) | (None, Some(Global::Prim(n))) => *n,
            (None, Some(Global::Def(def))) => return self.expand(h, def, args, line, scope),
            (None, Some(Global::Proof(..))) => return Err(Error::new(line, format!("`{h}` is a proof, not a statement"))),
            (None, Some(Global::Set(_))) => return Err(Error::new(line, format!("`{h}` is a set of premises, not a statement"))),
            (None, None) => return Err(Error::new(line, format!("`{h}` is not defined"))),
        };
        if args.len() != n {
            return Err(Error::new(line, format!("`{h}` takes {n} argument(s), got {}", args.len())));
        }
        let vars = args.iter().map(|a| self.individual(a, scope)).collect::<Result<Vec<_>, _>>()?;
        Ok(Formula::Atom(h.to_string(), vars))
    }

    /// A definition with all its arguments, expanded.
    fn expand(&self, h: &str, def: &Def, args: &[&Expr], line: usize, scope: &mut Scope) -> Result<Formula, Error> {
        if args.len() != def.params.len() {
            return Err(Error::new(line, format!("`{h}` takes {} argument(s), got {}", def.params.len(), args.len())));
        }
        let mut vars = Vec::new();
        let mut templates = Vec::new();
        for ((p, kind), a) in def.params.iter().zip(args) {
            match kind {
                Kind::Individual => vars.push((p.clone(), self.individual(a, scope)?)),
                Kind::Pred(n) => templates.push((p.clone(), self.template(a, *n, scope)?)),
            }
        }
        // Individuals first: templates may mention the caller's variables by the same names.
        def.body
            .subst_vars(&vars)
            .subst_preds(&templates)
            .map_err(|m| Error::new(line, m))
    }

    /// A predicate argument of arity `n`: for `n = 0` any formula, otherwise a predicate
    /// name with some leading arguments.
    fn template(&self, e: &Expr, n: usize, scope: &mut Scope) -> Result<Template, Error> {
        if n == 0 {
            return Ok(Template { holes: Vec::new(), body: self.formula(e, scope)? });
        }
        let (head, args) = e.spine();
        let Expr::Name(h, line) = head else {
            return Err(Error::new(e.line(), "expected a predicate name"));
        };
        if !upper(h) {
            let msg = match h.as_str() {
                "absurd" => format!("`absurd` is a statement, but a {n}-place predicate is needed"),
                _ if CONNECTIVES.contains(&h.as_str()) => {
                    format!("`{h}` can't be a {n}-place predicate argument; give it a name with `let`")
                }
                _ if reserved(h) => format!("`{h}` is built in, not a predicate"),
                _ if matches!(self.globals.get(h.as_str()), Some(Global::Proof(..))) => {
                    format!("`{h}` is a proof, not a predicate")
                }
                _ => format!("`{h}` is lowercase, so it isn't a predicate"),
            };
            return Err(Error::new(*line, msg));
        }
        let holes = hole_names(n);
        let wrong = |m: usize| {
            Error::new(*line, format!("`{h}` given {} argument(s) leaves {}, but a {n}-place predicate is needed", args.len(), m))
        };
        let m = match (scope.preds.get(h.as_str()), self.globals.get(h.as_str())) {
            (Some(m), _) | (None, Some(Global::Prim(m))) => *m,
            (None, Some(Global::Def(def))) => {
                let rest = &def.params[args.len().min(def.params.len())..];
                if args.len() > def.params.len() || rest.len() != n || rest.iter().any(|(_, k)| *k != Kind::Individual) {
                    return Err(wrong(def.params.len().saturating_sub(args.len())));
                }
                let mut vars = Vec::new();
                let mut templates = Vec::new();
                for ((p, kind), a) in def.params.iter().zip(&args) {
                    match kind {
                        Kind::Individual => vars.push((p.clone(), self.individual(a, scope)?)),
                        Kind::Pred(k) => templates.push((p.clone(), self.template(a, *k, scope)?)),
                    }
                }
                vars.extend(rest.iter().map(|(p, _)| p.clone()).zip(holes.iter().cloned()));
                let body = def.body.subst_vars(&vars).subst_preds(&templates).map_err(|m| Error::new(*line, m))?;
                return Ok(Template { holes, body });
            }
            (None, Some(Global::Proof(..))) => return Err(Error::new(*line, format!("`{h}` is a proof, not a predicate"))),
            (None, Some(Global::Set(_))) => return Err(Error::new(*line, format!("`{h}` is a set of premises, not a predicate"))),
            (None, None) => return Err(Error::new(*line, format!("`{h}` is not defined"))),
        };
        if args.len() > m || m - args.len() != n {
            return Err(wrong(m.saturating_sub(args.len())));
        }
        let mut vars = args.iter().map(|a| self.individual(a, scope)).collect::<Result<Vec<_>, _>>()?;
        vars.extend(holes.iter().cloned());
        Ok(Template { holes, body: Formula::Atom(h.clone(), vars) })
    }

    // ---- reasoning under the block stack ----

    fn body(&self, cx: &Cx, o: &Open) -> Result<Formula, String> {
        unwrap(o.thm.concl(), &cx.stack[..o.depth])
    }

    /// The axiom instance under the first `d` entries, with `inner` `forall`s inside them.
    fn lift(&self, cx: &Cx, ax: Axiom, d: usize, inner: &[String]) -> Result<Thm, String> {
        self.lift_s(&cx.stack[..d], ax, inner)
    }

    /// Modus ponens under the first `d` entries: `f` proves `imp A B` there, `a` proves `A`.
    fn mp_at(&self, cx: &Cx, f: &Thm, a: &Thm, d: usize) -> Result<Thm, String> {
        self.mp_s(&cx.stack[..d], f, a)
    }

    // Reasoning under any stack goes through two rules per *shape* of stack (the sequence
    // of variable and assumption layers), each proved once as a checked proof and then used
    // by substitution:
    //   mp:   from  layers[imp A B]  and  layers[A],  get  layers[B]
    //   lift: from  forall (all variables) T,          get  layers[T]
    // Each is proved from the rules for the shape one layer shorter, so every use costs
    // one substitution instead of work exponential in the number of layers.

    fn lift_s(&self, stack: &[Entry], ax: Axiom, inner: &[String]) -> Result<Thm, String> {
        let mut prefix = vars(stack);
        prefix.extend(inner.iter().cloned());
        let closed = kernel::axiom(ax, &prefix)?;
        if !stack.iter().any(|e| matches!(e, Entry::Hyp(_))) {
            return Ok(closed);
        }
        let body = strip_foralls(closed.concl(), &vars(stack)).ok_or("internal: closure has the wrong shape")?;
        self.use_shape_rule(stack, "lift", &[body], &[&closed])
    }

    fn mp_s(&self, stack: &[Entry], f: &Thm, a: &Thm) -> Result<Thm, String> {
        if stack.is_empty() {
            return kernel::mp(a, f);
        }
        let fb = unwrap(f.concl(), stack)?;
        let ab = unwrap(a.concl(), stack)?;
        let Formula::Imp(p, q) = &fb else {
            return Err(format!("{fb} is not an implication"));
        };
        if **p != ab {
            return Err(format!("{fb} needs {p}, but got {ab}"));
        }
        self.use_shape_rule(stack, "mp", &[(**p).clone(), (**q).clone()], &[f, a])
    }

    /// Applies the rule `kind` for `stack`'s shape. Its parameters are the assumptions'
    /// predicates, then the formulas `fs`, each abstracted over the stack's variables.
    fn use_shape_rule(&self, stack: &[Entry], kind: &str, fs: &[Formula], ev: &[&Thm]) -> Result<Thm, String> {
        let lemma = self.shape_rule(kind, &shape(stack))?;
        let vs = vars(stack);
        let mut ts = Vec::new();
        for (i, e) in stack.iter().enumerate() {
            if let Entry::Hyp(h) = e {
                ts.push(abstract_over(h, &vars(&stack[..i])));
            }
        }
        ts.extend(fs.iter().map(|f| abstract_over(f, &vs)));
        lemma.apply(&ts, None, ev)
    }

    /// The rule `kind` for a shape, proved on first use.
    fn shape_rule(&self, kind: &str, shape: &str) -> Result<Lemma, String> {
        let key = format!("{kind}:{shape}");
        if let Some(l) = self.rules.borrow().get(&key) {
            return Ok(l.clone());
        }
        // An abstract stack of this shape: variables `_v…`; assumptions `#H…` applied to
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
        let lemma = match kind {
            "mp" => {
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
                let t = self.lift_s(inner, ax, &[])?;
                let t = self.mp_s(inner, &t, &f)?;
                let t = self.mp_s(inner, &t, &x)?;
                Lemma::new(params, vec![p1, p2], wrap(&stack, b), &t)?
            }
            _ => {
                params.push(("#T".into(), k));
                let t = atom("#T");
                let premise = t.clone().close(&vs);
                let p = kernel::assume(&premise)?;
                // Under the shorter shape: its own lift, with the last layer folded into T.
                let proved = match &last[0] {
                    Entry::Var(y) => self.lift_closed(inner, &p, all(y, t.clone()))?,
                    Entry::Hyp(h) => {
                        let under = self.lift_closed(inner, &p, t.clone())?;
                        let kk = kernel::axiom(Axiom::Imp1(t.clone(), h.clone()), &vs)?;
                        let kk = self.lift_closed(inner, &kk, imp(t.clone(), imp(h.clone(), t.clone())))?;
                        self.mp_s(inner, &kk, &under)?
                    }
                };
                Lemma::new(params, vec![premise], wrap(&stack, t), &proved)?
            }
        };
        self.rules.borrow_mut().insert(key, lemma.clone());
        Ok(lemma)
    }

    /// From `forall (stack's variables) body`, `stack[body]`: the lift rule, or nothing to
    /// do when there are no assumptions.
    fn lift_closed(&self, stack: &[Entry], closed: &Thm, body: Formula) -> Result<Thm, String> {
        if !stack.iter().any(|e| matches!(e, Entry::Hyp(_))) {
            return Ok(closed.clone());
        }
        self.use_shape_rule(stack, "lift", &[body], &[closed])
    }

    /// The same theorem under more entries: `vac` for a variable, `imp1` for an assumption.
    fn weaken(&self, cx: &Cx, o: &Open, to: usize) -> Result<Open, String> {
        let thm = self.weaken_s(&cx.stack, &o.thm, o.depth, to)?;
        Ok(Open { thm, depth: to.max(o.depth) })
    }

    /// A theorem under `stack[..from]`, moved under `stack[..to]`.
    fn weaken_s(&self, stack: &[Entry], thm: &Thm, from: usize, to: usize) -> Result<Thm, String> {
        let mut thm = thm.clone();
        for d in from..to {
            let phi = unwrap(thm.concl(), &stack[..d])?;
            let ax = match &stack[d] {
                Entry::Var(y) => Axiom::Vac(y.clone(), phi),
                Entry::Hyp(h) => Axiom::Imp1(phi, h.clone()),
            };
            let t = self.lift_s(&stack[..d], ax, &[])?;
            thm = self.mp_s(&stack[..d], &t, &thm)?;
        }
        Ok(thm)
    }

    /// `imp A A` under the first `d` entries.
    fn identity(&self, cx: &Cx, a: &Formula, d: usize) -> Result<Thm, String> {
        let aa = imp(a.clone(), a.clone());
        let s = self.lift(cx, Axiom::Imp2(a.clone(), aa.clone(), a.clone()), d, &[])?;
        let k = self.lift(cx, Axiom::Imp1(a.clone(), aa), d, &[])?;
        let t = self.mp_at(cx, &s, &k, d)?;
        let k2 = self.lift(cx, Axiom::Imp1(a.clone(), a.clone()), d, &[])?;
        self.mp_at(cx, &t, &k2, d)
    }

    /// `h y`: a `forall` instantiated with a block variable.
    fn instantiate(&self, cx: &Cx, o: &Open, y: &str) -> Result<Open, String> {
        let iy = cx.var_index(y).ok_or_else(|| format!("`{y}` is not a block variable"))?;
        let d = o.depth.max(iy + 1);
        let o = self.weaken(cx, o, d)?;
        let Formula::All(x, a) = self.body(cx, &o)? else {
            return Err(format!("can't apply to `{y}`: {} doesn't start with `forall`", self.body(cx, &o)?));
        };
        let t = self.lift(cx, Axiom::Inst(y.to_string(), x, *a), d, &[])?;
        Ok(Open { thm: self.mp_at(cx, &t, &o.thm, d)?, depth: d })
    }

    /// Modus ponens between two pieces of evidence at whatever depth they need.
    fn apply_open(&self, cx: &Cx, f: &Open, a: &Open) -> Result<Open, String> {
        let d = f.depth.max(a.depth);
        let f = self.weaken(cx, f, d)?;
        let a = self.weaken(cx, a, d)?;
        Ok(Open { thm: self.mp_at(cx, &f.thm, &a.thm, d)?, depth: d })
    }

    // ---- evidence ----

    fn is_individual(&self, e: &Expr, cx: &Cx) -> bool {
        matches!(e, Expr::Name(n, _) if cx.lookup(n).is_none() && cx.var_index(n).is_some())
    }

    fn evidence(&self, e: &Expr, cx: &mut Cx, want: Option<&Formula>) -> Result<Open, Error> {
        let (head, args) = e.spine();
        let (h, line) = match head {
            Expr::Name(h, line) => (h.clone(), *line),
            Expr::Hole(line) => return Err(Error::new(*line, "`_` is only allowed on the right of `|>`")),
            block => {
                let want = if args.is_empty() { want } else { None };
                let o = self.block(block, cx, want)?;
                return self.apply_all(o, &args, cx);
            }
        };
        let err = |m: String| Error::new(line, m);
        let split = args.iter().position(|a| !formula_like(a)).unwrap_or(args.len());
        let (formal, rest) = args.split_at(split);
        if let Some(bad) = rest.iter().find(|a| formula_like(a)) {
            return Err(Error::new(bad.line(), "formula arguments must come before evidence arguments"));
        }
        if let Some(o) = cx.lookup(&h).cloned() {
            if !formal.is_empty() {
                return Err(err(format!("`{h}` is a theorem; it takes only evidence and individuals")));
            }
            return self.apply_all(o, rest, cx);
        }
        if h == "mp" {
            if !formal.is_empty() || rest.len() < 2 {
                return Err(err("`mp` takes two pieces of evidence: `mp a f`".into()));
            }
            let a = self.evidence(rest[0], cx, None)?;
            let f = self.evidence(rest[1], cx, None)?;
            let o = self.apply_open(cx, &f, &a).map_err(err)?;
            return self.apply_all(o, &rest[2..], cx);
        }
        if AXIOMS.contains(&h.as_str()) {
            return self.axiom(&h, formal, rest, cx, want, line);
        }
        match self.globals.get(&h) {
            Some(Global::Proof(info)) => {
                // `p S` passes the caller's parameters and premises that `p` got from set `S`
                // (directly or through other sets), by name.
                let mut passed = BTreeSet::new();
                let mut formal = formal;
                while let Some(Expr::Name(n, _)) = formal.first() {
                    if !info.params.iter().chain(&info.premises).any(|s| s.sets.contains(n)) {
                        break;
                    }
                    passed.insert(n.clone());
                    formal = &formal[1..];
                }
                let from_set = |s: &Slot| s.sets.iter().any(|x| passed.contains(x));
                let lemma = &info.lemma;
                let mut pre_t = Vec::new();
                for (s, (_, n)) in info.params.iter().zip(lemma.params()) {
                    pre_t.push(if !from_set(s) {
                        None
                    } else if cx.preds.get(&s.name) == Some(n) {
                        let holes = hole_names(*n);
                        Some(Template { body: Formula::Atom(s.name.clone(), holes.clone()), holes })
                    } else {
                        return Err(err(format!("passing that set needs a parameter `{}` with {n} argument(s) here", s.name)));
                    });
                }
                let mut pre_e = Vec::new();
                for s in &info.premises {
                    pre_e.push(if !from_set(s) {
                        None
                    } else {
                        match cx.lookup(&s.name) {
                            Some(e) => Some(e.clone()),
                            None => return Err(err(format!("passing that set needs evidence named `{}` here", s.name))),
                        }
                    });
                }
                self.call(&h, lemma, pre_t, pre_e, formal, rest, cx, line)
            }
            Some(_) => Err(err(format!("`{h}` is a statement or predicate, not evidence"))),
            None => Err(err(format!("`{h}` is not defined"))),
        }
    }

    /// Applies each argument in turn: an individual instantiates a `forall`; evidence is
    /// modus ponens.
    fn apply_all(&self, mut o: Open, args: &[&Expr], cx: &mut Cx) -> Result<Open, Error> {
        for a in args {
            o = if self.is_individual(a, cx) {
                let Expr::Name(y, _) = a else { unreachable!() };
                self.instantiate(cx, &o, y).map_err(|m| Error::new(a.line(), m))?
            } else {
                let x = self.evidence(a, cx, None)?;
                self.apply_open(cx, &o, &x).map_err(|m| Error::new(a.line(), m))?
            };
        }
        Ok(o)
    }

    // Proofs are applied to closed formulas. Under blocks, a call is closed over
    // the block *variables* it needs (with any other free names after them), done by the
    // kernel, and the result is then lifted back under the assumptions in between. Evidence
    // passed to a proof must not itself depend on an assumption.

    /// The depth the call needs: at least `min`, and down to every block variable the
    /// templates mention.
    fn depth_for(&self, cx: &Cx, ts: &[Template], min: usize) -> usize {
        let mut d = min;
        for t in ts {
            for x in t.extras() {
                if let Some(i) = cx.var_index(&x) {
                    d = d.max(i + 1);
                }
            }
        }
        d
    }

    /// The block variables of `stack[..d]`, as a stack of their own.
    fn var_stack(cx: &Cx, d: usize) -> Vec<Entry> {
        cx.stack[..d].iter().filter(|e| matches!(e, Entry::Var(_))).cloned().collect()
    }

    /// The prefix for a call at depth `d`: its block variables, then the templates' other
    /// free names.
    fn call_prefix(&self, cx: &Cx, ts: &[Template], d: usize) -> Vec<String> {
        let mut extras = BTreeSet::new();
        for t in ts {
            extras.extend(t.extras());
        }
        let mut prefix = cx.vars(d);
        prefix.extend(extras.into_iter().filter(|x| cx.var_index(x).is_none()));
        prefix
    }

    /// A theorem closed over `stack[..d]`'s variables, put back under `stack[..d]`.
    fn reopen(&self, cx: &Cx, thm: &Thm, d: usize) -> Result<Open, String> {
        let body = unwrap(thm.concl(), &Self::var_stack(cx, d))?;
        Ok(Open { thm: self.lift_closed(&cx.stack[..d], thm, body)?, depth: d })
    }

    fn block(&self, e: &Expr, cx: &mut Cx, want: Option<&Formula>) -> Result<Open, Error> {
        let line = e.line();
        let err = |m: String| Error::new(line, m);
        let d = cx.stack.len();
        let saved = cx.ev.len();
        // Names introduced inside the block are free again afterwards.
        let saved_names = cx.names.clone();
        let o = match e {
            Expr::Forall { vars, body, .. } => {
                for v in vars {
                    self.claim(cx, v, line, false)?;
                    cx.stack.push(Entry::Var(v.clone()));
                }
                let inner = want.and_then(|w| strip_foralls(w, vars));
                let r = self.run(body, cx, inner.as_ref())?;
                Open { thm: r.thm, depth: d }
            }
            Expr::Assume { name, hyp, body, .. } => {
                self.claim(cx, name, line, false)?;
                let a = self.formula(hyp, &mut cx.scope(false))?;
                let id = self.identity(cx, &a, d).map_err(err)?;
                cx.stack.push(Entry::Hyp(a.clone()));
                cx.ev.push((name.clone(), Open { thm: id, depth: d + 1 }));
                let inner = match want {
                    Some(Formula::Imp(p, q)) if **p == a => Some((**q).clone()),
                    _ => None,
                };
                let r = self.run(body, cx, inner.as_ref())?;
                Open { thm: r.thm, depth: d }
            }
            Expr::Obtain { var, name, from, body, .. } => {
                let ex_ev = self.evidence(from, cx, None)?;
                let ex_ev = self.weaken(cx, &ex_ev, d).map_err(err)?;
                let Formula::Ex(x0, a0) = self.body(cx, &ex_ev).map_err(err)? else {
                    return Err(err(format!("`obtain` needs evidence for an `exists`, not {}", self.body(cx, &ex_ev).map_err(err)?)));
                };
                self.claim(cx, var, line, false)?;
                self.claim(cx, name, line, false)?;
                let a = a0.subst_vars(&[(x0, var.clone())]);
                cx.stack.push(Entry::Var(var.clone()));
                let id = self.identity(cx, &a, d + 1).map_err(err)?;
                cx.stack.push(Entry::Hyp(a.clone()));
                cx.ev.push((name.clone(), Open { thm: id, depth: d + 2 }));
                let r = self.run(body, cx, want)?;
                let c = unwrap(r.thm.concl(), &cx.stack).map_err(err)?;
                if c.is_free(var) {
                    return Err(err(format!("the result of `obtain` can't mention `{var}`: {c}")));
                }
                cx.stack.truncate(d);
                cx.ev.truncate(saved);
                cx.names = saved_names;
                // r: forall var $ imp A C.  ex_e: imp (forall var $ imp A C) (exists var A) C.
                let t = self.lift(cx, Axiom::ExE(var.clone(), a, c), d, &[]).map_err(err)?;
                let t = self.mp_at(cx, &t, &r.thm, d).map_err(err)?;
                let thm = self.mp_at(cx, &t, &ex_ev.thm, d).map_err(err)?;
                return Ok(Open { thm, depth: d });
            }
            _ => unreachable!("not a block"),
        };
        cx.stack.truncate(d);
        cx.ev.truncate(saved);
        cx.names = saved_names;
        Ok(o)
    }

    /// A block's steps and result, at the full current depth.
    fn run(&self, body: &Block, cx: &mut Cx, want: Option<&Formula>) -> Result<Open, Error> {
        for s in &body.steps {
            self.have(s, cx)?;
        }
        let stated = body.stmt.as_ref().map(|s| self.formula(s, &mut cx.scope(false))).transpose()?;
        let line = body.result.line();
        let o = self.justify(&body.result, cx, stated.as_ref().or(want), line)?;
        self.weaken(cx, &o, cx.stack.len()).map_err(|m| Error::new(line, m))
    }

    fn axiom(&self, h: &str, formal: &[&Expr], rest: &[&Expr], cx: &mut Cx, want: Option<&Formula>, line: usize) -> Result<Open, Error> {
        let err = |m: String| Error::new(line, m);
        let (pat, nf, nv) = pattern(h);
        if formal.len() > nf {
            return Err(err(format!("`{h}` takes at most {nf} formula argument(s)")));
        }
        let mut m = Match { f: vec![None; nf], v: vec![None; nv], deferred: Vec::new() };
        let mut scope = cx.scope(true);
        for (i, a) in formal.iter().enumerate() {
            m.f[i] = Some(self.formula(a, &mut scope)?);
        }
        // An instance sits under only the block variables its letters mention.
        let min = var_depth(cx, m.f.iter().flatten());
        let mut ants = Vec::new();
        let mut r = &pat;
        while let Pat::Imp(a, b) = r {
            ants.push(a.as_ref());
            r = b;
        }

        if !rest.is_empty() && !self.is_individual(rest[0], cx) {
            // Evidence feeds the instance's antecedents, at the depth they all need.
            let n = ants.len().min(rest.len());
            if n == 0 {
                return Err(err(format!("`{h}` can't be applied to evidence directly")));
            }
            let mut ev = Vec::new();
            for a in &rest[..n] {
                ev.push(self.evidence(a, cx, None)?);
            }
            for (i, (p, o)) in ants.iter().zip(&ev).enumerate() {
                let b = self.body(cx, o).map_err(err)?;
                if !m.go(p, &b) {
                    return Err(Error::new(rest[i].line(), format!("{b} doesn't fit premise {} of `{h}`", i + 1)));
                }
            }
            // A stated formula for the result fixes letters the evidence leaves open.
            if let Some(w) = want.filter(|_| rest.len() == n) {
                let mut with_want = m.clone();
                if with_want.go(consequent(&pat, n), w) {
                    m = with_want;
                }
            }
            if !m.finish() {
                return Err(err(format!("the evidence doesn't fit `{h}`")));
            }
            let mut d = ev.iter().map(|o| o.depth).fold(min, usize::max);
            // `inst` and `ex_i` of a variable that doesn't occur still need one in scope.
            let mut fallback = None;
            if nv == 2 && m.v[1].is_none() {
                if let Some(i) = cx.stack.iter().position(|e| matches!(e, Entry::Var(_))) {
                    d = d.max(i + 1);
                    fallback = cx.vars(i + 1).pop();
                }
            }
            let ev = ev.iter().map(|o| self.weaken(cx, o, d)).collect::<Result<Vec<_>, _>>().map_err(err)?;
            let mut thm = self.lift(cx, build(h, &m, fallback.as_deref()).map_err(err)?, d, &[]).map_err(err)?;
            for (o, a) in ev.iter().zip(rest) {
                thm = self.mp_at(cx, &thm, &o.thm, d).map_err(|m| Error::new(a.line(), m))?;
            }
            return self.apply_all(Open { thm, depth: d }, &rest[n..], cx);
        }

        // All letters given and nothing to close: the instance is fixed, unless a letter
        // mentions a variable that only a stated `forall` can close over.
        let mut fixed = None;
        if formal.len() == nf && nv == 0 {
            match self.lift(cx, build(h, &m, None).map_err(err)?, min, &[]) {
                Ok(thm) => return self.apply_all(Open { thm, depth: min }, rest, cx),
                Err(e) => fixed = Some(e),
            }
        }

        // Otherwise the letters come from the stated formula, whose leading `forall`s may be
        // an inner closure prefix.
        let Some(w) = want.filter(|_| rest.is_empty()) else {
            let e = fixed.unwrap_or_else(|| format!("can't work out the letters of `{h}`: pass them, or state the step's formula"));
            return Err(err(e));
        };
        // The shallowest depth that works; deeper ones offer more variables for `inst` and
        // `ex_i` to instantiate when the instantiated variable doesn't occur.
        for d in min.max(var_depth(cx, [w]))..=cx.stack.len() {
            let mut inner = Vec::new();
            let mut target = w;
            loop {
                let mut try_m = m.clone();
                if try_m.go(&pat, target) && try_m.finish() {
                    let mut prefix = cx.vars(d);
                    prefix.extend(inner.iter().cloned());
                    if let Ok(ax) = build(h, &try_m, prefix.last().map(String::as_str)) {
                        if let Ok(thm) = self.lift(cx, ax, d, &inner) {
                            if unwrap(thm.concl(), &cx.stack[..d]).ok().as_ref() == Some(w) {
                                return Ok(Open { thm, depth: d });
                            }
                        }
                    }
                }
                match target {
                    Formula::All(x, body) => {
                        inner.push(x.clone());
                        target = body;
                    }
                    _ => break,
                }
            }
        }
        Err(err(format!("{w} is not an instance of `{h}`")))
    }

    /// A call of a checked proof: predicate arguments, then evidence for each premise.
    #[allow(clippy::too_many_arguments)]
    fn call(
        &self,
        h: &str,
        lemma: &Lemma,
        mut sol: Vec<Option<Template>>,
        pre_e: Vec<Option<Open>>,
        formal: &[&Expr],
        rest: &[&Expr],
        cx: &mut Cx,
        line: usize,
    ) -> Result<Open, Error> {
        let err = |m: String| Error::new(line, m);
        let params = lemma.params();
        let premises = lemma.premises();
        // Arguments fill the parameters and premises not already passed through a set.
        let open_params: Vec<usize> = (0..params.len()).filter(|&i| sol[i].is_none()).collect();
        if formal.len() > open_params.len() {
            return Err(err(format!("`{h}` takes {} predicate argument(s)", open_params.len())));
        }
        let wanted = pre_e.iter().filter(|e| e.is_none()).count();
        if rest.len() < wanted {
            return Err(err(format!("`{h}` needs {wanted} piece(s) of evidence, got {}", rest.len())));
        }
        {
            let mut scope = cx.scope(true);
            for (&i, a) in open_params.iter().zip(formal) {
                sol[i] = Some(self.template(a, params[i].1, &mut scope)?);
            }
        }
        let mut supplied = rest[..wanted].iter();
        let mut given = Vec::new();
        for e in pre_e {
            given.push(match e {
                Some(e) => e,
                None => self.evidence(supplied.next().unwrap(), cx, None)?,
            });
        }
        // Evidence must not depend on an assumption: then it closes over variables alone.
        let mut d0 = 0;
        for o in &given {
            if cx.stack[..o.depth].iter().any(|e| matches!(e, Entry::Hyp(_))) {
                return Err(err(format!("`{h}` can't be applied to evidence that depends on an `assume` or `obtain`")));
            }
            d0 = d0.max(o.depth);
        }
        let explicit: Vec<Template> = sol.iter().flatten().cloned().collect();
        let d = self.depth_for(cx, &explicit, d0);
        let vstack = Self::var_stack(cx, d);
        // At its own depth, the evidence sits under variables only.
        let mut thms = Vec::new();
        for o in &given {
            thms.push(self.weaken_s(&vstack, &o.thm, o.depth, vstack.len()).map_err(err)?);
        }
        let non_block: Vec<String> = explicit.iter().flat_map(|t| t.extras()).filter(|x| cx.var_index(x).is_none()).collect();
        if sol.iter().any(Option::is_none) {
            if !non_block.is_empty() {
                return Err(err("with free variables in a predicate argument, give every predicate argument".into()));
            }
            let index: HashMap<&str, usize> = params.iter().enumerate().map(|(i, (p, _))| (p.as_str(), i)).collect();
            let outer: BTreeSet<String> = vars(&vstack).into_iter().collect();
            for (pat, t) in premises.iter().zip(&thms) {
                let b = unwrap(t.concl(), &vstack).map_err(err)?;
                // A match that fails partway leaves nothing behind.
                let mut trial = sol.clone();
                if hom(pat, &b, &index, &outer, &mut Vec::new(), &mut trial) {
                    sol = trial;
                }
            }
        }
        let mut templates = Vec::new();
        for ((p, _), t) in params.iter().zip(sol) {
            match t {
                Some(t) => templates.push(t),
                None => return Err(err(format!("can't work out `{p}` for `{h}`; pass it explicitly"))),
            }
        }
        let prefix = self.call_prefix(cx, &templates, d);
        let args: Vec<&Thm> = thms.iter().collect();
        let thm = lemma.apply(&templates, Some(&prefix), &args).map_err(|m| err(format!("{h}: {m}")))?;
        let o = self.reopen(cx, &thm, d).map_err(err)?;
        self.apply_all(o, &rest[wanted..], cx)
    }
}

/// Every name appears once.
fn distinct<'a>(names: impl Iterator<Item = (&'a String, usize)>) -> Result<(), Error> {
    let mut seen = BTreeSet::new();
    for (n, line) in names {
        if !seen.insert(n) {
            return Err(Error::new(line, format!("parameter `{n}` appears twice")));
        }
    }
    Ok(())
}

/// Kinds of `let` parameters: lowercase names are individuals; uppercase names
/// are predicates, with the arity given by `(P x)` or by how the body applies them.
fn param_kinds(params: &[ParamDecl], body: &Expr) -> Result<Vec<(String, Kind)>, Error> {
    params
        .iter()
        .map(|p| {
            if !upper(&p.name) {
                if p.arity.is_some() {
                    return Err(Error::new(p.line, format!("`{}` is lowercase, so it's an individual and has no arity", p.name)));
                }
                return Ok((p.name.clone(), Kind::Individual));
            }
            if let Some(n) = p.arity {
                return Ok((p.name.clone(), Kind::Pred(n)));
            }
            let mut uses = BTreeSet::new();
            applied_arities(body, &p.name, &mut uses);
            match uses.len() {
                0 => Ok((p.name.clone(), Kind::Pred(0))),
                1 => Ok((p.name.clone(), Kind::Pred(*uses.iter().next().unwrap()))),
                _ => Err(Error::new(p.line, format!("`{}` is applied to different numbers of arguments", p.name))),
            }
        })
        .collect()
}

/// The argument counts `name` is applied to as a head somewhere in `e`.
fn applied_arities(e: &Expr, name: &str, out: &mut BTreeSet<usize>) {
    if let Expr::App(..) = e {
        let (head, args) = e.spine();
        if matches!(head, Expr::Name(n, _) if n == name) {
            out.insert(args.len());
        }
        for a in args {
            applied_arities(a, name, out);
        }
    }
}

// ---- axiom shapes ----

/// An axiom's instance with metavariables: formulas `Meta`, binder variables by index.
#[derive(Clone, Debug)]
enum Pat {
    Meta(usize),
    Absurd,
    And(Box<Pat>, Box<Pat>),
    Or(Box<Pat>, Box<Pat>),
    Imp(Box<Pat>, Box<Pat>),
    All(usize, Box<Pat>),
    Ex(usize, Box<Pat>),
    /// Formula meta with variable meta `.1` put for variable meta `.2`.
    Subst(usize, usize, usize),
}

/// The shape of each axiom, with its numbers of formula and variable metavariables.
fn pattern(name: &str) -> (Pat, usize, usize) {
    use Pat::*;
    let b = Box::new;
    let i = |x, y| Imp(b(x), b(y));
    let (a, bb, c) = (Meta(0), Meta(1), Meta(2));
    match name {
        "imp1" => (i(a.clone(), i(bb, a)), 2, 0),
        "imp2" => (i(i(a.clone(), i(bb.clone(), c.clone())), i(i(a.clone(), bb), i(a, c))), 3, 0),
        "and_i" => (i(a.clone(), i(bb.clone(), And(b(a), b(bb)))), 2, 0),
        "and_e1" => (i(And(b(a.clone()), b(bb)), a), 2, 0),
        "and_e2" => (i(And(b(a), b(bb.clone())), bb), 2, 0),
        "or_i1" => (i(a.clone(), Or(b(a), b(bb))), 2, 0),
        "or_i2" => (i(bb.clone(), Or(b(a), b(bb))), 2, 0),
        "or_e" => (i(i(a.clone(), c.clone()), i(i(bb.clone(), c.clone()), i(Or(b(a), b(bb)), c))), 3, 0),
        "efq" => (i(Absurd, a), 1, 0),
        "dist" => (i(All(0, b(i(a.clone(), bb.clone()))), i(All(0, b(a)), All(0, b(bb)))), 2, 1),
        "vac" => (i(a.clone(), All(0, b(a))), 1, 1),
        "inst" => (i(All(0, b(a)), Subst(0, 1, 0)), 1, 2),
        "ex_i" => (i(Subst(0, 1, 0), Ex(0, b(a))), 1, 2),
        "ex_e" => (i(All(0, b(i(a.clone(), bb.clone()))), i(Ex(0, b(a)), bb)), 2, 1),
        _ => unreachable!("not an axiom: {name}"),
    }
}

#[derive(Clone)]
struct Match {
    f: Vec<Option<Formula>>,
    v: Vec<Option<String>>,
    deferred: Vec<(usize, usize, usize, Formula)>,
}

impl Match {
    fn go(&mut self, p: &Pat, t: &Formula) -> bool {
        match (p, t) {
            (Pat::Meta(i), _) => match &self.f[*i] {
                Some(g) => g == t,
                None => {
                    self.f[*i] = Some(t.clone());
                    true
                }
            },
            (Pat::Absurd, Formula::Absurd) => true,
            (Pat::And(a, b), Formula::And(c, d)) | (Pat::Or(a, b), Formula::Or(c, d)) | (Pat::Imp(a, b), Formula::Imp(c, d)) => {
                self.go(a, c) && self.go(b, d)
            }
            (Pat::All(v, a), Formula::All(w, b)) | (Pat::Ex(v, a), Formula::Ex(w, b)) => match self.v[*v].clone() {
                None => {
                    self.v[*v] = Some(w.clone());
                    self.go(a, b)
                }
                Some(name) if name == *w => self.go(a, b),
                // Same binder under another name: rename the target's, if that can't capture.
                Some(name) => !b.is_free(&name) && self.go(a, &b.subst_vars(&[(w.clone(), name)])),
            },
            (Pat::Subst(a, y, x), _) => {
                self.deferred.push((*a, *y, *x, t.clone()));
                true
            }
            _ => false,
        }
    }

    /// Checks the substitutions, working out the substituted variable where it's missing.
    fn finish(&mut self) -> bool {
        for (a, y, x, t) in std::mem::take(&mut self.deferred) {
            let (Some(f), Some(xv)) = (self.f[a].clone(), self.v[x].clone()) else { return false };
            if self.v[y].is_none() {
                self.v[y] = find_var(&f, &t, &xv);
            }
            if let Some(yv) = &self.v[y] {
                if f.subst_vars(&[(xv, yv.clone())]) != t {
                    return false;
                }
            } else if f != t {
                return false;
            }
        }
        true
    }
}

/// `p` without its first `n` antecedents.
fn consequent(mut p: &Pat, n: usize) -> &Pat {
    for _ in 0..n {
        if let Pat::Imp(_, b) = p {
            p = b;
        }
    }
    p
}

/// The variable in `t` where `a` has a free `x`.
fn find_var(a: &Formula, t: &Formula, x: &str) -> Option<String> {
    match (a, t) {
        (Formula::Atom(_, xs), Formula::Atom(_, ys)) => xs.iter().zip(ys).find(|(v, _)| *v == x).map(|(_, y)| y.clone()),
        (Formula::And(a1, a2), Formula::And(t1, t2)) | (Formula::Or(a1, a2), Formula::Or(t1, t2)) | (Formula::Imp(a1, a2), Formula::Imp(t1, t2)) => {
            find_var(a1, t1, x).or_else(|| find_var(a2, t2, x))
        }
        (Formula::All(v, a1), Formula::All(_, t1)) | (Formula::Ex(v, a1), Formula::Ex(_, t1)) if v != x => find_var(a1, t1, x),
        _ => None,
    }
}

/// The axiom for a completed match. Unmatched binder variables get fresh names, except the
/// instantiated variable of `inst` and `ex_i`, which must be one the prefix binds.
fn build(h: &str, m: &Match, bound_fallback: Option<&str>) -> Result<Axiom, String> {
    let letters = ["A", "B", "C"];
    let f = |i: usize| {
        m.f[i].clone().ok_or_else(|| format!("can't work out `{}` for `{h}`: pass it, or state the step's formula", letters[i]))
    };
    let mut avoid: BTreeSet<String> = m.f.iter().flatten().flat_map(|g| g.free_vars()).collect();
    let mut v = |i: usize| {
        m.v[i].clone().unwrap_or_else(|| {
            let x = fresh("x", &avoid);
            avoid.insert(x.clone());
            x
        })
    };
    let target = |m: &Match| {
        m.v[1].clone().or(bound_fallback.map(str::to_string)).ok_or_else(|| match h {
            "ex_i" => "`ex_i` needs a witness, and no individual is in scope".to_string(),
            _ => format!("can't work out which variable `{h}` instantiates: apply the evidence to it, as in `h x`"),
        })
    };
    Ok(match h {
        "imp1" => Axiom::Imp1(f(0)?, f(1)?),
        "imp2" => Axiom::Imp2(f(0)?, f(1)?, f(2)?),
        "and_i" => Axiom::AndI(f(0)?, f(1)?),
        "and_e1" => Axiom::AndE1(f(0)?, f(1)?),
        "and_e2" => Axiom::AndE2(f(0)?, f(1)?),
        "or_i1" => Axiom::OrI1(f(0)?, f(1)?),
        "or_i2" => Axiom::OrI2(f(0)?, f(1)?),
        "or_e" => Axiom::OrE(f(0)?, f(1)?, f(2)?),
        "efq" => Axiom::Efq(f(0)?),
        "dist" => Axiom::Dist(v(0), f(0)?, f(1)?),
        "vac" => Axiom::Vac(v(0), f(0)?),
        "inst" => Axiom::Inst(target(m)?, v(0), f(0)?),
        "ex_i" => Axiom::ExI(target(m)?, v(0), f(0)?),
        "ex_e" => Axiom::ExE(v(0), f(0)?, f(1)?),
        _ => unreachable!("not an axiom: {h}"),
    })
}

// ---- inferring a proof's predicate arguments ----

/// Matches a premise against a theorem's body, solving predicate parameters applied to
/// distinct bound variables. `env` pairs the premise's binders with the body's; `outer`
/// are block variables a solution may mention.
fn hom(
    pat: &Formula,
    tgt: &Formula,
    params: &HashMap<&str, usize>,
    outer: &BTreeSet<String>,
    env: &mut Vec<(String, String)>,
    sol: &mut [Option<Template>],
) -> bool {
    // The body's binder for a premise's bound variable, unless an inner binder of the body
    // reuses its name.
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
                Some(t) => {
                    let s: Vec<(String, String)> = t.holes.iter().cloned().zip(args).collect();
                    t.body.subst_vars(&s) == *tgt
                }
                None => {
                    let distinct: BTreeSet<&String> = args.iter().collect();
                    let ok = |v: &String| args.contains(v) || (outer.contains(v) && !env.iter().any(|(_, t)| t == v));
                    if distinct.len() != args.len() || !tgt.free_vars().iter().all(ok) {
                        return false;
                    }
                    let holes = hole_names(args.len());
                    let s: Vec<(String, String)> = args.into_iter().zip(holes.iter().cloned()).collect();
                    sol[i] = Some(Template { body: tgt.subst_vars(&s), holes });
                    true
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
