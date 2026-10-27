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
//! `imp2`. A block's `therefore` closes the layers the block opened, innermost first, which
//! is free, since the kernel theorem doesn't change. A line that isn't under a layer yet is
//! put under it first, by weakening.

use crate::kernel::formula::{absurd, all, and, atom, ex, fresh, hole_names, imp, or, Formula, Name, Node, Template};
use crate::kernel::{self, Axiom, Lemma, Thm};
use crate::parse::{Arg, Assume, Block, FExpr, Item, Just, Line, Param, Step, TArg, Therefore};
use crate::print::show;
use crate::Error;
use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;

/// The rules, and `auto`, which is reserved for a tool that fills lines in: the checker
/// refuses it, so a file that still says `auto` is unfinished.
pub const RULES: &[&str] = &["imp_e", "and_i", "and_e", "or_i", "or_e", "absurd_e", "forall_e", "exists_i", "exists_e", "reit", "auto"];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    Individual,
    Pred(usize),
}

/// A definition: parameters and a body.
struct Def {
    params: Vec<(String, Kind)>,
    body: Formula,
}

struct TheoremInfo {
    lemma: Lemma,
}

enum Global {
    /// A declared predicate, with its arity.
    Prim(usize),
    Def(Rc<Def>),
    Theorem(TheoremInfo),
}

#[derive(Default)]
pub struct Checker {
    globals: HashMap<String, Global>,
    /// Rules for reasoning under layers, stated per shape and variable names (see `shape_rule`).
    rules: RefCell<HashMap<(Rule, String), Rc<Lemma>>>,
    /// Their proofs, made once per shape.
    proofs: RefCell<HashMap<(Rule, String), Rc<Thm>>>,
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
    Var(Name),
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
    /// The labels of lemmas that have closed, with the lemma each belonged to, for messages.
    closed: Vec<(String, String)>,
}

impl Cx {
    fn lookup(&self, label: &str) -> Option<&Labeled> {
        self.lines.iter().rev().find(|l| l.label == label)
    }

    fn var_index(&self, name: &str) -> Option<usize> {
        self.stack.iter().position(|e| matches!(e, Entry::Var(v) if &**v == name))
    }

    /// The variable named `name`, as the stack knows it.
    fn var(&self, name: &str) -> Option<Name> {
        self.stack.iter().find_map(|e| match e {
            Entry::Var(v) if &**v == name => Some(v.clone()),
            _ => None,
        })
    }

    fn vars(&self, depth: usize) -> Vec<Name> {
        vars(&self.stack[..depth])
    }

    /// The entries at `layers`.
    fn ents(&self, layers: &[usize]) -> Vec<Entry> {
        layers.iter().map(|&i| self.stack[i].clone()).collect()
    }

}

/// Names visible while reading a formula.
struct Scope<'a> {
    /// The theorem's parameters, or a definition's.
    params: &'a [(String, usize)],
    /// Variables bound by quantifiers around the point being read.
    bound: Vec<Name>,
    /// Variables in scope in the proof.
    in_scope: Vec<Name>,
    /// Whether the formula is inside a proof, where `variable` can declare a name.
    in_proof: bool,
}

fn vars(entries: &[Entry]) -> Vec<Name> {
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
    let mut s: Vec<(Name, Name)> = Vec::new();
    let mut cur = f;
    for e in entries {
        cur = match (e, cur.node()) {
            (Entry::Var(y), Node::All(z, b)) => {
                s.retain(|(v, _)| v != z);
                if z != y {
                    s.push((z.clone(), y.clone()));
                }
                b
            }
            (Entry::Hyp(h), Node::Imp(p, b)) if p.subst_vars(&s) == *h => b,
            _ => return Err(format!("{} doesn't have the shape of the current block", show(&cur.subst_vars(&s)))),
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

/// A template whose holes are `vars` themselves, so applying it to them changes nothing.
fn abstract_over(f: &Formula, vars: &[Name]) -> Result<Template, String> {
    Template::new(vars.to_vec(), f.clone())
}

/// A stack's shape: the variables by name, `#` for an assumption. Names can't contain either.
fn shape(entries: &[Entry]) -> String {
    let parts: Vec<&str> = entries.iter().map(|e| match e { Entry::Var(v) => v, Entry::Hyp(_) => "#" }).collect();
    parts.join(" ")
}

pub fn upper(name: &str) -> bool {
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
fn axiom_free_vars(ax: &Axiom) -> BTreeSet<Name> {
    let mut fv: BTreeSet<Name> = axiom_formulas(ax).into_iter().flat_map(|f| f.free_vars().iter().cloned()).collect();
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

/// Placeholder names for messages: `x y z w`, then `x1 y1 ...`, avoiding `taken`.
fn placeholders(n: usize, taken: &BTreeSet<Name>) -> Vec<Name> {
    let mut out = Vec::new();
    let mut round = 0;
    while out.len() < n {
        for base in ["x", "y", "z", "w"] {
            if out.len() == n {
                break;
            }
            let name: Name = if round == 0 { base.into() } else { format!("{base}{round}").as_str().into() };
            if !taken.contains(&name) {
                out.push(name);
            }
        }
        round += 1;
    }
    out
}

/// A template shown as `P x = body`, with its holes named.
fn show_reading(p: &str, t: &Template) -> String {
    let body = t.body();
    let holes = t.holes();
    let names = placeholders(holes.len(), &body.free_vars().iter().cloned().collect());
    let s: Vec<(Name, Name)> = holes.iter().cloned().zip(names.iter().cloned()).collect();
    let head: Vec<&str> = std::iter::once(p).chain(names.iter().map(|n| &**n)).collect();
    format!("{} = {}", head.join(" "), show(&body.subst_vars(&s)))
}

/// The error for an uppercase name nothing declares.
fn not_declared(name: &str, arity: usize) -> String {
    let holes = placeholders(arity, &BTreeSet::new());
    let decl: Vec<&str> = std::iter::once(name).chain(holes.iter().map(|h| &**h)).collect();
    format!("`{name}` is not declared: add `predicate {}` before this, or to the theorem", decl.join(" "))
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
            Item::Predicate { name, holes, line } => {
                self.new_global(name, *line)?;
                self.globals.insert(name.clone(), Global::Prim(holes.len()));
                Ok(None)
            }
            Item::Define { name, params, body, line } => {
                self.new_global(name, *line)?;
                let def = self.definition(params, body)?;
                // Messages print an instance by name, unless the definition only renames an atom.
                let individuals = def.params.iter().all(|(_, k)| matches!(k, Kind::Individual));
                if individuals && !matches!(def.body.node(), Node::Atom(..)) {
                    let params = def.params.iter().map(|(p, _)| Name::from(p.as_str())).collect();
                    crate::print::add_fold(crate::print::Fold { name: name.clone(), params, body: def.body.clone() });
                }
                self.globals.insert(name.clone(), Global::Def(Rc::new(def)));
                Ok(None)
            }
            Item::Theorem { name, block, line } => {
                self.new_global(name, *line)?;
                let info = self.theorem(name, block, *line).map_err(|e| Error::new(e.line, format!("{name}: {}", e.msg)))?;
                let concl = info.lemma.concl().clone();
                self.globals.insert(name.clone(), Global::Theorem(info));
                Ok(Some((name.clone(), concl)))
            }
        }
    }

    fn new_global(&self, name: &str, line: usize) -> Result<(), Error> {
        if RULES.contains(&name) {
            return Err(Error::new(line, format!("`{name}` is a rule, so it can't be a theorem's name")));
        }
        if self.globals.contains_key(name) {
            return Err(Error::new(line, format!("`{name}` is already defined")));
        }
        Ok(())
    }

    // ---- definitions ----

    /// `define Name params = body`. Uppercase parameters are predicates or statements, with the
    /// arity their placeholders fix; lowercase ones are individuals.
    fn definition(&self, params: &[Param], body: &FExpr) -> Result<Def, Error> {
        let preds = self.params(params)?;
        let mut kinds = Vec::new();
        let mut bound = Vec::new();
        for p in params {
            if upper(&p.name) {
                kinds.push((p.name.clone(), Kind::Pred(p.holes.len())));
            } else {
                kinds.push((p.name.clone(), Kind::Individual));
                bound.push(Name::from(p.name.as_str()));
            }
        }
        let mut scope = Scope { params: &preds, bound, in_scope: Vec::new(), in_proof: false };
        let body = self.formula(body, &mut scope)?;
        Ok(Def { params: kinds, body })
    }

    /// Declared parameters, checked for repeats and clashes: the predicates among them with
    /// their arities.
    fn params(&self, params: &[Param]) -> Result<Vec<(String, usize)>, Error> {
        let mut seen = BTreeSet::new();
        let mut preds = Vec::new();
        for p in params {
            if !seen.insert(&p.name) {
                return Err(Error::new(p.line, format!("parameter `{}` appears twice", p.name)));
            }
            if RULES.contains(&p.name.as_str()) || self.globals.contains_key(&p.name) {
                return Err(Error::new(p.line, format!("`{}` is already defined, so it can't be a parameter", p.name)));
            }
            if upper(&p.name) {
                preds.push((p.name.clone(), p.holes.len()));
            }
        }
        Ok(preds)
    }

    // ---- theorems ----

    fn theorem(&mut self, name: &str, block: &Block, line: usize) -> Result<TheoremInfo, Error> {
        let mut cx = Cx::default();
        cx.params = self.params(&block.predicates)?;
        if self.explain {
            self.trace.borrow_mut().push(format!("theorem {name}"));
        }
        let (result, concl) = self.block(block, &mut cx, name, true)?;
        if let Some(&i) = result.layers.last() {
            return Err(Error::new(block.therefore.line, format!("{} is still open", describe(&cx.stack[i]))));
        }
        // No hypotheses: every theorem is a logical validity, and the kernel checks it.
        let lemma = Lemma::new(cx.params.clone(), Vec::new(), concl, &result.thm).map_err(|m| Error::new(line, m))?;
        Ok(TheoremInfo { lemma })
    }

    /// A block: its declarations, its steps, then `therefore`, which closes everything the
    /// block opened. Its labels, variables and assumptions are local.
    fn block(&self, b: &Block, cx: &mut Cx, name: &str, theorem: bool) -> Result<(Open, Formula), Error> {
        let start_depth = cx.stack.len();
        let start_lines = cx.lines.len();
        cx.blocks.push(start_lines);
        let res = self.block_body(b, cx, name, start_depth, theorem);
        cx.blocks.pop();
        if !theorem {
            let gone: Vec<(String, String)> = cx.lines[start_lines..].iter().map(|l| (l.label.clone(), name.to_string())).collect();
            cx.closed.extend(gone);
        }
        cx.lines.truncate(start_lines);
        cx.stack.truncate(start_depth);
        res
    }

    fn block_body(&self, b: &Block, cx: &mut Cx, name: &str, start_depth: usize, theorem: bool) -> Result<(Open, Formula), Error> {
        for (x, line) in &b.variables {
            if cx.var_index(x).is_some() {
                return Err(Error::new(*line, format!("`{x}` is already a variable in scope")));
            }
            if cx.lookup(x).is_some() {
                return Err(Error::new(*line, format!("`{x}` is a label here, so it can't be a variable")));
            }
            if RULES.contains(&x.as_str()) {
                return Err(Error::new(*line, format!("`{x}` is a rule, so it can't be a variable")));
            }
            if self.globals.contains_key(x) {
                return Err(Error::new(*line, format!("`{x}` is a theorem, so it can't be a variable")));
            }
            cx.stack.push(Entry::Var(x.as_str().into()));
        }
        for p in &b.predicates {
            for h in &p.holes {
                if cx.var_index(h).is_some() || cx.lookup(h).is_some() || self.globals.contains_key(h) {
                    return Err(Error::new(p.line, format!("`{h}` is a name here, so it can't be a placeholder of `{}`", p.name)));
                }
            }
        }
        if !theorem {
            if let Some(p) = b.predicates.first() {
                return Err(Error::new(p.line, "a theorem's predicates are declared in the theorem, not in a lemma"));
            }
        }
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
                    let (o, _) = self.block(block, cx, lemma, false)?;
                    cx.lines.push(Labeled { label: lemma.clone(), open: o, hyp_index: None });
                }
            }
        }
        self.therefore(&b.therefore, cx, name, start_depth)
    }

    /// `therefore F`: `F` is the line right above, closed over the layers the block opened, in
    /// reverse order of opening.
    fn therefore(&self, t: &Therefore, cx: &mut Cx, name: &str, start_depth: usize) -> Result<(Open, Formula), Error> {
        let line = t.line;
        let start = *cx.blocks.last().expect("inside a block");
        let Some((label, above)) = cx.lines[start..].last().map(|l| (l.label.clone(), l.open.clone())) else {
            return Err(Error::new(line, format!("`therefore` closes the line right above it, and `{name}` has none")));
        };
        // The line under every layer the block opened, outermost first, then each closed,
        // innermost first.
        let block: Vec<usize> = (start_depth..cx.stack.len()).collect();
        // An assumption the line is weakened under brings the layers of the variables it mentions.
        let mut target = union(&above.layers, &block);
        let mentioned: Vec<usize> = target
            .iter()
            .filter_map(|&i| if let Entry::Hyp(h) = &cx.stack[i] { Some(h.free_vars().iter().filter_map(|x| cx.var_index(x)).collect::<Vec<_>>()) } else { None })
            .flatten()
            .collect();
        target = union(&target, &mentioned);
        let mut o = self.weaken(cx, &above, &target).map_err(|m| Error::new(line, m))?;
        for &i in block.iter().rev() {
            let var = matches!(cx.stack[i], Entry::Var(_));
            o = self.close_at(cx, &o, i, var).map_err(|m| Error::new(line, m))?;
        }
        let want = self.proof_formula(&t.formula, cx)?;
        let got = self.body(cx, &o).map_err(|m| Error::new(line, m))?;
        if got != want {
            // What the block opened, by name: variables, and assumptions by their labels.
            let opened: Vec<String> = (start_depth..cx.stack.len())
                .map(|i| match &cx.stack[i] {
                    Entry::Var(x) => format!("`{x}`"),
                    Entry::Hyp(h) => cx.lines.iter().find(|l| l.hyp_index == Some(i)).map_or_else(|| show(h), |l| format!("`{}`", l.label)),
                })
                .collect();
            let over = match opened.split_last() {
                None => String::new(),
                Some((last, [])) => format!(", closed over {last},"),
                Some((last, rest)) => format!(", closed over {} and {last},", rest.join(", ")),
            };
            return Err(Error::new(line, format!("`{label}`{over} gives {}, not {}", show(&got), show(&want))));
        }
        self.trace_line(cx, name, &o, &want);
        Ok((o, want))
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
        if cx.var_index(label).is_some() {
            return Err(Error::new(line, format!("`{label}` is a variable in scope, so it can't be a label")));
        }
        if self.globals.contains_key(label) {
            return Err(Error::new(line, format!("`{label}` is a theorem, so it can't be a label")));
        }
        if cx.lines.iter().any(|l| l.label == label) {
            return Err(Error::new(line, format!("`{label}` is already a label in scope")));
        }
        Ok(())
    }

    /// Reads a formula inside a proof. Its free variables must be in scope.
    fn proof_formula(&self, e: &FExpr, cx: &mut Cx) -> Result<Formula, Error> {
        let in_scope = cx.vars(cx.stack.len());
        let mut scope = Scope { params: &cx.params, bound: Vec::new(), in_scope, in_proof: true };
        self.formula(e, &mut scope)
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
            return Err(Error::new(l.line, format!("this gives {}, not {}", show(&got), show(&want))));
        }
        self.trace_line(cx, &l.label, &o, &want);
        Ok((o, want))
    }

    /// `f` for display: binders the shape rules named by stack position get the user's names.
    // ---- justifications ----

    /// Every justification starts with a rule.
    fn justify(&self, j: &Just, cx: &mut Cx, want: &Formula) -> Result<Open, Error> {
        let (h, line) = (&j.rule, j.line);
        if !RULES.contains(&h.as_str()) {
            if cx.lookup(h).is_none() && !matches!(self.globals.get(h), Some(Global::Theorem(_))) {
                return Err(Error::new(line, format!("`{h}` is not a rule, a line here, or a theorem{}", self.did_you_mean(h, cx))));
            }
            return Err(Error::new(line, format!("`by` names a rule first: `imp_e {h} ...` applies `{h}`, `reit {h}` restates it")));
        }
        if h == "auto" {
            return Err(Error::new(line, "`auto` marks a line for a tool to fill in, and this line is still unfilled"));
        }
        self.rule(h, &j.args, cx, want, line)
    }

    /// The fact at the head of `imp_e` or `reit`, applied to the arguments after it: a line, a
    /// theorem, or a theorem's instance. A theorem's predicates are read off the lines and the
    /// stated formula.
    fn apply_head(&self, head: &Arg, args: &[Arg], cx: &mut Cx, want: &Formula) -> Result<Open, Error> {
        let theorem = |n: &str| match self.globals.get(n) {
            Some(Global::Theorem(info)) => Some(info),
            _ => None,
        };
        // A theorem takes the lines up to the first variable, and the rest are applied to its
        // result, as to any line.
        let lines = args.iter().position(|a| matches!(a, Arg::Ident(n, _) if cx.lookup(n).is_none() && cx.var_index(n).is_some()));
        let (first, rest) = args.split_at(lines.unwrap_or(args.len()));
        let cite = |n: &str, info, targs: &[TArg], line: usize, cx: &mut Cx| -> Result<Open, Error> {
            let o = self.call(n, info, targs, first, cx, if rest.is_empty() { Some(want) } else { None }, line)?;
            if rest.is_empty() {
                Ok(o)
            } else {
                self.apply_all(o, rest, cx, Some(want))
            }
        };
        match head {
            Arg::Ident(n, line) if cx.lookup(n).is_none() => match theorem(n) {
                Some(info) => cite(n, info, &[], *line, cx),
                None => self.apply_all(self.arg_open(head, cx)?, args, cx, Some(want)),
            },
            Arg::Instance { head: n, targs, line } => match theorem(n) {
                Some(info) => cite(n, info, targs, *line, cx),
                None => Err(Error::new(*line, format!("`{n}` is not a theorem"))),
            },
            _ => {
                let o = self.arg_open(head, cx)?;
                self.apply_all(o, args, cx, Some(want))
            }
        }
    }

    /// `: did you mean `x`?` for a misspelled name, from the rules, the lines in scope and the
    /// theorems, or nothing when no name is close.
    fn did_you_mean(&self, n: &str, cx: &Cx) -> String {
        let lines = cx.lines.iter().map(|l| l.label.as_str());
        let theorems = self.globals.iter().filter(|(_, g)| matches!(g, Global::Theorem(_))).map(|(t, _)| t.as_str());
        let mut near: Vec<&str> = RULES.iter().copied().chain(lines).chain(theorems).filter(|c| close(n, c)).collect();
        near.sort_unstable();
        near.dedup();
        match near.as_slice() {
            [] => String::new(),
            [one] => format!(": did you mean `{one}`?"),
            many => format!(": did you mean one of {}?", many.iter().map(|c| format!("`{c}`")).collect::<Vec<_>>().join(", ")),
        }
    }

    /// A line named by an argument: a label, a theorem with nothing left to supply, or a
    /// theorem's instance.
    fn arg_open(&self, a: &Arg, cx: &mut Cx) -> Result<Open, Error> {
        match a {
            Arg::Ident(n, line) => {
                if let Some(l) = cx.lookup(n) {
                    return Ok(l.open.clone());
                }
                match self.globals.get(n) {
                    Some(Global::Theorem(info)) => self.call(n, info, &[], &[], cx, None, *line),
                    _ if cx.var_index(n).is_some() => Err(Error::new(*line, format!("`{n}` is a variable, and a line is needed here"))),
                    _ => match cx.closed.iter().rev().find(|(l, _)| l == n) {
                        Some((_, lemma)) => Err(Error::new(*line, format!("`{n}` was a line of lemma `{lemma}`, which has closed"))),
                        None => Err(Error::new(*line, format!("`{n}` is not a line or a theorem here{}", self.did_you_mean(n, cx)))),
                    },
                }
            }
            Arg::Instance { head: n, targs, line } => match self.globals.get(n) {
                Some(Global::Theorem(info)) => self.call(n, info, targs, &[], cx, None, *line),
                _ => Err(Error::new(*line, format!("`{n}` is not a theorem"))),
            },
        }
    }

    /// A variable named by an argument. It must be in scope: no rule brings a variable in.
    fn arg_var(&self, a: &Arg, cx: &Cx) -> Result<Name, Error> {
        match a {
            Arg::Ident(n, line) => match cx.var(n) {
                Some(v) => Ok(v),
                None if cx.lookup(n).is_some() => Err(Error::new(*line, format!("`{n}` is a line, and a variable is needed here"))),
                None => Err(Error::new(*line, format!("`{n}` is not a variable in scope: declare it with `variable {n}` in this block"))),
            },
            other => Err(Error::new(other.line(), "a variable is needed here, not a theorem's instance")),
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
                let y = cx.var(y).expect("checked above");
                o = self.instantiate(cx, &o, &y).map_err(|m| Error::new(*line, m))?;
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

    /// Feeds `lines` to the antecedents of `o`. Whenever `forall`s come next, they are
    /// instantiated at the variables that make the antecedents up to the next `forall` match
    /// the lines, and, after the last line, what is left match the stated formula. So
    /// `imp_e t q a` works for `t : Q -> forall x. A x -> B x`.
    fn feed(&self, mut o: Open, lines: &[Open], args: &[Arg], cx: &mut Cx, want: Option<&Formula>) -> Result<Open, Error> {
        let mut k = 0;
        while k < lines.len() {
            let line = args[k].line();
            let err = |m: String| Error::new(line, m);
            let body = self.body(cx, &o).map_err(err)?;
            let mut metas: Vec<Name> = Vec::new();
            let mut cur = &body;
            while let Node::All(x, b) = cur.node() {
                metas.push(x.clone());
                cur = b;
            }
            if metas.is_empty() {
                o = self.apply_open(cx, &o, &lines[k]).map_err(err)?;
                k += 1;
                continue;
            }
            let meta_set: BTreeSet<Name> = metas.iter().cloned().collect();
            let mut sol: HashMap<Name, Name> = HashMap::new();
            let mut rest = cur;
            let mut j = k;
            while j < lines.len() {
                let Node::Imp(a, b) = rest.node() else {
                    if j == k {
                        return Err(Error::new(args[j].line(), format!("{} has no antecedent left for this line", show(&body))));
                    }
                    break;
                };
                let lb = self.body(cx, &lines[j]).map_err(err)?;
                if !match_vars(a, &lb, &meta_set, &mut Vec::new(), &mut sol) {
                    return Err(Error::new(args[j].line(), format!("{} doesn't fit antecedent {} of {}", show(&lb), j - k + 1, show(&body))));
                }
                rest = b;
                j += 1;
                if matches!(rest.node(), Node::All(..)) {
                    break;
                }
            }
            if let (true, Some(w)) = (j == lines.len(), want) {
                let mut trial = sol.clone();
                if match_vars(rest, w, &meta_set, &mut Vec::new(), &mut trial) {
                    sol = trial;
                }
            }
            for x in &metas {
                let Some(y) = sol.get(x) else {
                    return Err(err(format!("can't work out `{x}` in {}: instantiate it with `forall_e`", show(&body))));
                };
                o = self.instantiate(cx, &o, y).map_err(err)?;
            }
            for (l, a) in lines[k..j].iter().zip(&args[k..j]) {
                o = self.apply_open(cx, &o, l).map_err(|m| Error::new(a.line(), m))?;
            }
            k = j;
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
            "imp_e" => {
                at_least(2, "an implication, then the lines for its antecedents")?;
                if let Arg::Ident(n, l) = &args[0] {
                    if let Some(head) = cx.lookup(n) {
                        let f = self.body(cx, &head.open.clone()).map_err(err)?;
                        if !matches!(f.node(), Node::Imp(..) | Node::All(..)) {
                            return Err(Error::new(*l, format!("`{n}` is {}, which is not an implication: `imp_e` takes the implication first, then its antecedents", show(&f))));
                        }
                    }
                }
                self.apply_head(&args[0], &args[1..], cx, want)
            }
            "reit" => {
                need(1, "one fact, restated: the same formula up to definitions and bound names")?;
                self.apply_head(&args[0], &[], cx, want)
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
                at_least(2, "two or more lines, nested to the right like the formula")?;
                let opens = args.iter().map(|a| self.arg_open(a, cx)).collect::<Result<Vec<_>, _>>()?;
                let (last, rest) = opens.split_last().unwrap();
                let mut cur = last.clone();
                for a in rest.iter().rev() {
                    let (fa, fc) = (self.body(cx, a).map_err(err)?, self.body(cx, &cur).map_err(err)?);
                    cur = self.apply_axiom(cx, Axiom::AndI(fa, fc), &[a.clone(), cur]).map_err(err)?;
                }
                Ok(cur)
            }
            "and_e" => {
                need(1, "one line, an `and`: the stated formula says which conjunct")?;
                let c = self.arg_open(&args[0], cx)?;
                let fc = self.body(cx, &c).map_err(err)?;
                if !matches!(fc.node(), Node::And(..)) {
                    return Err(err(format!("`and_e` needs an `and`, and {} isn't one", show(&fc))));
                }
                // The path to the stated formula in the tree of `and`s: left or right at each node.
                fn path(f: &Formula, want: &Formula, out: &mut Vec<bool>) -> bool {
                    if f == want {
                        return true;
                    }
                    if let Node::And(a, b) = f.node() {
                        out.push(true);
                        if path(a, want, out) {
                            return true;
                        }
                        out.pop();
                        out.push(false);
                        if path(b, want, out) {
                            return true;
                        }
                        out.pop();
                    }
                    false
                }
                let mut steps = Vec::new();
                if !path(&fc, want, &mut steps) {
                    return Err(err(format!("{} is not a conjunct of {}", show(want), show(&fc))));
                }
                let mut o = c;
                let mut cur = fc;
                for left in steps {
                    let Node::And(a, b) = cur.node() else { unreachable!() };
                    let (a, b) = (a.clone(), b.clone());
                    let ax = if left { Axiom::AndE1(a.clone(), b.clone()) } else { Axiom::AndE2(a.clone(), b.clone()) };
                    o = self.apply_axiom(cx, ax, &[o]).map_err(err)?;
                    cur = if left { a } else { b };
                }
                Ok(o)
            }
            "or_i" => {
                need(1, "one line, the alternative being introduced: the stated formula says where")?;
                let a = self.arg_open(&args[0], cx)?;
                let fa = self.body(cx, &a).map_err(err)?;
                if !matches!(want.node(), Node::Or(..)) {
                    return Err(err(format!("`or_i` gives an `or`, and the stated formula {} isn't one", show(want))));
                }
                // The path from the stated formula down to the line in the tree of `or`s.
                fn path(f: &Formula, line: &Formula, out: &mut Vec<bool>) -> bool {
                    if f == line {
                        return true;
                    }
                    if let Node::Or(l, r) = f.node() {
                        out.push(true);
                        if path(l, line, out) {
                            return true;
                        }
                        out.pop();
                        out.push(false);
                        if path(r, line, out) {
                            return true;
                        }
                        out.pop();
                    }
                    false
                }
                let mut steps = Vec::new();
                if !path(want, &fa, &mut steps) {
                    return Err(err(format!("{} is not an alternative of {}", show(&fa), show(want))));
                }
                // Build upward from the line: the node at each step, innermost first.
                let mut nodes: Vec<(bool, Formula, Formula)> = Vec::new();
                let mut cur = want.clone();
                for &left in &steps {
                    let Node::Or(l, r) = cur.node() else { unreachable!() };
                    nodes.push((left, l.clone(), r.clone()));
                    cur = if left { l.clone() } else { r.clone() };
                }
                let mut o = a;
                for (left, l, r) in nodes.into_iter().rev() {
                    let ax = if left { Axiom::OrI1(l, r) } else { Axiom::OrI2(l, r) };
                    o = self.apply_axiom(cx, ax, &[o]).map_err(err)?;
                }
                Ok(o)
            }
            "or_e" => {
                at_least(3, "an `or`, then a line for each alternative")?;
                let d = self.arg_open(&args[0], cx)?;
                let cases = args[1..].iter().map(|a| self.arg_open(a, cx)).collect::<Result<Vec<_>, _>>()?;
                let fd = self.body(cx, &d).map_err(err)?;
                // The alternatives: the `or` nests to the right, and the last case takes what is left.
                let mut alts: Vec<Formula> = Vec::new();
                let mut rest = fd.clone();
                for _ in 1..cases.len() {
                    let Node::Or(a, b) = rest.node() else {
                        return Err(err(format!("`or_e` was given {} cases, and {} has fewer alternatives", cases.len(), show(&fd))));
                    };
                    alts.push(a.clone());
                    rest = b.clone();
                }
                alts.push(rest);
                let mut c: Option<Formula> = None;
                for (alt, case) in alts.iter().zip(&cases) {
                    let fc = self.body(cx, case).map_err(err)?;
                    match fc.node() {
                        Node::Imp(a, k) if a == alt && c.as_ref().is_none_or(|c| c == k) => c = Some(k.clone()),
                        _ => return Err(err(format!("`or_e` needs {} -> C for each alternative, got {}", show(alt), show(&fc)))),
                    }
                }
                let c = c.expect("at least two cases");
                // From the right: (A_n -> C), then (A_(n-1) or rest) -> C, ..., then C from the `or`.
                let mut inner = cases.last().unwrap().clone();
                let mut rest_f = alts.last().unwrap().clone();
                for i in (0..alts.len() - 1).rev() {
                    let ax = Axiom::OrE(alts[i].clone(), rest_f.clone(), c.clone());
                    if i == 0 {
                        return self.apply_axiom(cx, ax, &[cases[0].clone(), inner, d]).map_err(err);
                    }
                    inner = self.apply_axiom(cx, ax, &[cases[i].clone(), inner]).map_err(err)?;
                    rest_f = or(alts[i].clone(), rest_f);
                }
                unreachable!()
            }
            "absurd_e" => {
                need(1, "one line, `absurd`")?;
                let f = self.arg_open(&args[0], cx)?;
                let ff = self.body(cx, &f).map_err(err)?;
                if ff != absurd() {
                    return Err(err(format!("`absurd_e` needs a line that is `absurd`, and {} isn't", show(&ff))));
                }
                self.apply_axiom(cx, Axiom::Efq(want.clone()), &[f]).map_err(err)
            }
            "exists_i" => {
                need(1, "one line, the instance")?;
                let l = self.arg_open(&args[0], cx)?;
                let fl = self.body(cx, &l).map_err(err)?;
                // All the leading binders of the stated formula, each with a witness in scope.
                let mut binders: Vec<Name> = Vec::new();
                let mut cur = want;
                while let Node::Ex(x, a) = cur.node() {
                    binders.push(x.clone());
                    cur = a;
                }
                if binders.is_empty() {
                    return Err(err(format!("`exists_i` gives an `exists`, and the stated formula {} isn't one", show(want))));
                }
                let innermost = cur.clone();
                let in_scope = cx.vars(cx.stack.len());
                if in_scope.is_empty() {
                    return Err(err("`exists_i` needs a witness, and no variable is in scope".into()));
                }
                // As many leading binders as the line accounts for: the line may itself begin
                // with the inner `exists`. The most binders that fit win.
                let mut found: Option<(Vec<Name>, Vec<(Name, Name)>, Formula)> = None;
                for k in (1..=binders.len()).rev() {
                    let mut a = innermost.clone();
                    for x in binders[k..].iter().rev() {
                        a = ex(x, a);
                    }
                    let metas: BTreeSet<Name> = binders[..k].iter().cloned().collect();
                    let mut sol: HashMap<Name, Name> = HashMap::new();
                    if !match_vars(&a, &fl, &metas, &mut Vec::new(), &mut sol) {
                        continue;
                    }
                    // A binder the body doesn't mention may stand at any variable in scope.
                    let ys: Vec<Name> = binders[..k].iter().map(|x| sol.get(x).cloned().unwrap_or_else(|| in_scope.last().unwrap().clone())).collect();
                    let pairs: Vec<(Name, Name)> = binders[..k].iter().cloned().zip(ys.iter().cloned()).collect();
                    if a.subst_vars(&pairs) == fl && ys.iter().all(|y| cx.var_index(y).is_some()) {
                        found = Some((ys, pairs, a));
                        break;
                    }
                }
                let Some((ys, pairs, a)) = found else {
                    return Err(err(format!("{} is not {} at any variables in scope", show(&fl), show(want))));
                };
                let mut binders: Vec<Name> = binders[..ys.len()].to_vec();
                // A binder named like an outer binder's witness would capture it as the instance
                // is built, so it is renamed apart first. The result is the same up to bound names.
                let (mut a, mut pairs) = (a, pairs);
                for j in 1..binders.len() {
                    if ys[..j].contains(&binders[j]) {
                        let mut taken: BTreeSet<&str> = ys.iter().chain(&binders).chain(&in_scope).map(|n| &**n).collect();
                        taken.extend(a.free_vars().iter().map(|n| &**n));
                        let nb = fresh(&binders[j], &taken);
                        a = a.subst_vars(&[(binders[j].clone(), nb.clone())]);
                        pairs[j].0 = nb.clone();
                        binders[j] = nb;
                    }
                }
                // Innermost binder first: a[y/x] -> exists x. a, with the outer witnesses in place.
                let mut o = l;
                for k in (0..binders.len()).rev() {
                    let mut body = a.subst_vars(&pairs[..k]);
                    for x in binders[k + 1..].iter().rev() {
                        body = ex(x, body);
                    }
                    o = self.apply_axiom(cx, Axiom::ExI(ys[k].clone(), binders[k].clone(), body), &[o]).map_err(err)?;
                }
                Ok(o)
            }
            "exists_e" => {
                need(2, "an `exists` line, and a line `forall w. A -> C` with `w` not free in `C`")?;
                let e = self.arg_open(&args[0], cx)?;
                let g = self.arg_open(&args[1], cx)?;
                let fe = self.body(cx, &e).map_err(err)?;
                let mut xs: Vec<Name> = Vec::new();
                let mut cur = &fe;
                while let Node::Ex(x, a) = cur.node() {
                    xs.push(x.clone());
                    cur = a;
                }
                if xs.is_empty() {
                    let first = match &args[0] {
                        Arg::Ident(n, _) => format!("`{n}`"),
                        Arg::Instance { head, .. } => format!("the instance of `{head}`"),
                    };
                    return Err(err(format!("{first} is {}, which is not an `exists`: `exists_e` takes the `exists` first, then the lemma", show(&fe))));
                }
                let innermost = cur.clone();
                // The witness line: one `forall` per binder it eliminates, then `A -> C`. It may
                // eliminate fewer binders than the `exists` has; the rest stay in `A`.
                let fg = self.body(cx, &g).map_err(err)?;
                let mut ws: Vec<Name> = Vec::new();
                let mut cur = &fg;
                while ws.len() < xs.len() {
                    match cur.node() {
                        Node::All(w, body) => {
                            ws.push(w.clone());
                            cur = body;
                        }
                        _ => break,
                    }
                }
                let Node::Imp(a_w, c) = cur.node() else {
                    let want_shape = xs.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(" ");
                    return Err(err(format!("`exists_e` needs `forall {want_shape}. A -> C`, and {} isn't one", show(&fg))));
                };
                let (a_w, c) = (a_w.clone(), c.clone());
                let mut a = innermost;
                for x in xs[ws.len()..].iter().rev() {
                    a = ex(x, a);
                }
                let xs: Vec<Name> = xs[..ws.len()].to_vec();
                let pairs: Vec<(Name, Name)> = xs.iter().cloned().zip(ws.iter().cloned()).collect();
                if a.subst_vars(&pairs) != a_w {
                    return Err(err(format!("the witness line assumes {}, which isn't {} at `{}`", show(&a_w), show(&fe), ws.iter().map(|w| w.to_string()).collect::<Vec<_>>().join(" "))));
                }
                if let Some(w) = ws.iter().find(|w| c.is_free(w)) {
                    return Err(err(format!("the conclusion mentions the witness `{w}`: {}", show(&c))));
                }
                // Inner binders first: under `forall w1 .. w(k-1)`, the axiom turns
                // `forall wk. B -> C` into `(exists wk. B) -> C`, until one binder is left.
                let mut thm = g.thm.clone();
                for k in (1..ws.len()).rev() {
                    let mut entries = cx.ents(&g.layers);
                    entries.extend(ws[..k].iter().map(|w| Entry::Var(w.clone())));
                    let mut b = a_w.clone();
                    for x in ws[k + 1..].iter().rev() {
                        b = ex(x, b);
                    }
                    let t = self.axiom_at(&entries, Axiom::ExE(ws[k].clone(), b, c.clone())).map_err(err)?;
                    thm = self.mp(&entries, &t, &thm).map_err(err)?;
                }
                let g1 = Open { thm, layers: g.layers.clone() };
                let mut b = a_w;
                for x in ws[1..].iter().rev() {
                    b = ex(x, b);
                }
                let ax = Axiom::ExE(ws[0].clone(), b, c);
                self.apply_axiom(cx, ax, &[g1, e]).map_err(err)
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
    fn inst_under(&self, entries: &[Entry], thm: &Thm, y: &Name) -> Result<Thm, String> {
        let body = unwrap(thm.concl(), entries)?;
        let (x, a) = match body.node() {
            Node::All(x, a) => (x.clone(), a.clone()),
            _ => return Err(format!("can't instantiate at `{y}`: {} doesn't start with `forall`", show(&body))),
        };
        let t = self.axiom_at(entries, Axiom::Inst(y.clone(), x, a))?;
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
            FExpr::Absurd(_) => Ok(absurd()),
            FExpr::Not(a, _) => Ok(imp(self.formula(a, scope)?, absurd())),
            FExpr::And(a, b, _) => Ok(and(self.formula(a, scope)?, self.formula(b, scope)?)),
            FExpr::Or(a, b, _) => Ok(or(self.formula(a, scope)?, self.formula(b, scope)?)),
            FExpr::Imp(a, b, _) => Ok(imp(self.formula(a, scope)?, self.formula(b, scope)?)),
            FExpr::Forall(xs, body, line) | FExpr::Exists(xs, body, line) => {
                let names: Vec<Name> = xs.iter().map(|x| Name::from(x.as_str())).collect();
                for (x, name) in xs.iter().zip(&names) {
                    if RULES.contains(&x.as_str()) {
                        return Err(Error::new(*line, format!("`{x}` is a rule, not a variable")));
                    }
                    scope.bound.push(name.clone());
                }
                let mut f = self.formula(body, scope)?;
                for name in names.iter().rev() {
                    scope.bound.pop();
                    f = if matches!(e, FExpr::Forall(..)) { all(name, f) } else { ex(name, f) };
                }
                Ok(f)
            }
            FExpr::Atom { name, args, line } => self.atom(name, args, *line, scope),
        }
    }

    fn individual(&self, a: &TArg, scope: &mut Scope) -> Result<Name, Error> {
        match a {
            TArg::Var(x, line) => {
                let known = scope.bound.iter().rev().chain(&scope.in_scope).find(|v| ***v == **x);
                match known {
                    Some(v) => Ok(v.clone()),
                    None if scope.in_proof => Err(Error::new(*line, format!("`{x}` is not in scope: declare it with `variable {x}`, or bind it"))),
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
            return Ok(atom(name, &vars));
        }
        match self.globals.get(name) {
            Some(Global::Prim(n)) => {
                if args.len() != *n {
                    return Err(takes(name, *n, args.len(), line));
                }
                let vars = args.iter().map(|a| self.individual(a, scope)).collect::<Result<Vec<_>, _>>()?;
                Ok(atom(name, &vars))
            }
            Some(Global::Def(def)) => {
                let def = def.clone();
                if args.len() != def.params.len() {
                    return Err(takes(name, def.params.len(), args.len(), line));
                }
                self.expand(&def, args, &[], line, scope)
            }
            Some(Global::Theorem(_)) => unreachable!("theorems are lowercase"),
            None => Err(Error::new(line, not_declared(name, args.len()))),
        }
    }

    /// A definition expanded with `args` for its first parameters and `holes` for the rest,
    /// which are individuals.
    fn expand(&self, def: &Def, args: &[TArg], holes: &[Name], line: usize, scope: &mut Scope) -> Result<Formula, Error> {
        let mut vars: Vec<(Name, Name)> = Vec::new();
        let mut templates = Vec::new();
        for ((p, kind), a) in def.params.iter().zip(args) {
            match kind {
                Kind::Individual => vars.push((p.as_str().into(), self.individual(a, scope)?)),
                Kind::Pred(n) => templates.push((p.clone(), self.template(a, *n, scope)?)),
            }
        }
        vars.extend(def.params[args.len()..].iter().map(|(p, _)| Name::from(p.as_str())).zip(holes.iter().cloned()));
        // Individuals first: templates may mention the caller's variables by the same names.
        let map: Vec<(&str, &Template)> = templates.iter().map(|(p, t)| (p.as_str(), t)).collect();
        def.body.subst_vars(&vars).subst_preds(&map).map_err(|m| Error::new(line, m))
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
            atom(name, &vars)
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
                Some(Global::Theorem(_)) => unreachable!(),
                None => return Err(Error::new(line, not_declared(name, args.len() + n))),
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
        // The shape is checked here, so a mismatch is reported in the file's syntax.
        let (fb, ab) = if stack.is_empty() { (f.concl().clone(), a.concl().clone()) } else { (unwrap(f.concl(), stack)?, unwrap(a.concl(), stack)?) };
        let Node::Imp(p, q) = fb.node() else {
            return Err(format!("{} is not an implication", show(&fb)));
        };
        if *p != ab {
            return Err(format!("{} needs {}, but got {}", show(&fb), show(p), show(&ab)));
        }
        if stack.is_empty() {
            return kernel::mp(a, f);
        }
        self.use_shape_rule(stack, Rule::Mp, &[p.clone(), q.clone()], &[f, a])
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
        lemma.apply(&ts.iter().collect::<Vec<_>>(), &[], ev)
    }

    /// `rule` for a shape, proved on first use.
    fn shape_rule(&self, rule: Rule, shape: &str) -> Result<Rc<Lemma>, String> {
        let key = (rule, shape.to_string());
        if let Some(l) = self.rules.borrow().get(&key) {
            return Ok(l.clone());
        }
        // The rule is proved once per shape, with the variables `_v...`, and restated for
        // each set of names. A restatement is alpha-equivalent, so the kernel accepts the
        // same proof for it.
        let names: Vec<&str> = shape.split(' ').collect();
        let canonical: Vec<String> = names.iter().enumerate().map(|(i, n)| if *n == "#" { "#".to_string() } else { format!("_v{i}") }).collect();
        let proof = self.shape_proof(rule, &canonical.join(" "))?;
        let (_, params, hyps, concl) = Self::shape_statement(rule, &names);
        let lemma = Rc::new(Lemma::new(params, hyps, concl, &proof)?);
        self.rules.borrow_mut().insert(key, lemma.clone());
        Ok(lemma)
    }

    /// An abstract stack of this shape: its variables, and assumptions `#H...` applied to the
    /// variables before them. A user can't write `#`, so the parameters clash with nothing.
    /// With it, the rule's parameters, hypotheses and conclusion.
    fn shape_statement(rule: Rule, names: &[&str]) -> (Vec<Entry>, Vec<(String, usize)>, Vec<Formula>, Formula) {
        let mut stack = Vec::new();
        let mut vs = Vec::new();
        let mut params = Vec::new();
        for (i, c) in names.iter().enumerate() {
            if *c != "#" {
                let name: Name = (*c).into();
                vs.push(name.clone());
                stack.push(Entry::Var(name));
            } else {
                let h = format!("#H{i}");
                params.push((h.clone(), vs.len()));
                stack.push(Entry::Hyp(atom(&h, &vs)));
            }
        }
        let k = vs.len();
        let at = |p: &str| atom(p, &vs);
        match rule {
            Rule::Mp => {
                params.push(("#A".into(), k));
                params.push(("#B".into(), k));
                let (a, b) = (at("#A"), at("#B"));
                let hyps = vec![wrap(&stack, imp(a.clone(), b.clone())), wrap(&stack, a)];
                let concl = wrap(&stack, b);
                (stack, params, hyps, concl)
            }
            Rule::Lift => {
                params.push(("#T".into(), k));
                let t = at("#T");
                let hyps = vec![t.clone().close(&vs)];
                let concl = wrap(&stack, t);
                (stack, params, hyps, concl)
            }
        }
    }

    /// The proof of `rule` for a shape, from the rules for the shape one layer shorter.
    fn shape_proof(&self, rule: Rule, shape: &str) -> Result<Rc<Thm>, String> {
        let key = (rule, shape.to_string());
        if let Some(t) = self.proofs.borrow().get(&key) {
            return Ok(t.clone());
        }
        let names: Vec<&str> = shape.split(' ').collect();
        let (stack, _, hyps, _) = Self::shape_statement(rule, &names);
        let vs = vars(&stack);
        let at = |p: &str| atom(p, &vs);
        let (inner, last) = stack.split_at(stack.len() - 1);
        let proof = match rule {
            Rule::Mp => {
                let (a, b) = (at("#A"), at("#B"));
                let f = kernel::assume(&hyps[0])?;
                let x = kernel::assume(&hyps[1])?;
                let ax = match &last[0] {
                    Entry::Var(y) => Axiom::Dist(y.clone(), a, b),
                    Entry::Hyp(h) => Axiom::Imp2(h.clone(), a, b),
                };
                let t = self.axiom_at(inner, ax)?;
                let t = self.mp(inner, &t, &f)?;
                self.mp(inner, &t, &x)?
            }
            Rule::Lift => {
                let t = at("#T");
                let p = kernel::assume(&hyps[0])?;
                // Under the shorter shape: its own lift, with the last layer folded into T.
                match &last[0] {
                    Entry::Var(_) => self.lift(inner, &p)?,
                    Entry::Hyp(h) => {
                        let under = self.lift(inner, &p)?;
                        let kk = self.lift(inner, &kernel::axiom(Axiom::Imp1(t, h.clone()), &vs)?)?;
                        self.mp(inner, &kk, &under)?
                    }
                }
            }
        };
        let proof = Rc::new(proof);
        self.proofs.borrow_mut().insert(key, proof.clone());
        Ok(proof)
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
    fn instantiate(&self, cx: &Cx, o: &Open, y: &Name) -> Result<Open, String> {
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
            let mut scope = Scope { params: &cx.params, bound: Vec::new(), in_scope, in_proof: true };
            for (i, a) in targs.iter().enumerate() {
                sol[i] = Some(self.template(a, params[i].1, &mut scope)?);
            }
        }
        let mut given = Vec::new();
        for a in args {
            given.push(self.arg_open(a, cx)?);
        }
        // The antecedents the lines are fed to, under the quantifiers before each of them.
        let mut ants = Vec::new();
        let mut rest = lemma.concl();
        let mut binders: Vec<Name> = Vec::new();
        for _ in 0..given.len() {
            while let Node::All(x, b) = rest.node() {
                binders.push(x.clone());
                rest = b;
            }
            match rest.node() {
                Node::Imp(p, q) => {
                    ants.push(p);
                    rest = q;
                }
                _ => return Err(err(format!("`{h}` has {} antecedent(s), and {} line(s) were given", ants.len(), given.len()))),
            }
        }
        // Parameters not given as templates are read off the lines and the stated formula:
        // accepted when exactly one reading fits.
        if sol.iter().any(Option::is_none) {
            let index: HashMap<&str, usize> = params.iter().enumerate().map(|(i, (p, _))| (p.as_str(), i)).collect();
            let real: BTreeSet<Name> = cx.vars(cx.stack.len()).into_iter().collect();
            let outer = real.clone();
            let mut targets: Vec<(&Formula, Formula)> = Vec::new();
            for (p, o) in ants.iter().zip(&given) {
                targets.push((p, self.body(cx, o).map_err(err)?));
            }
            if let Some(w) = want {
                targets.push((rest, w.clone()));
            }
            // The theorem's leading binders stand for whatever variables the lines have there,
            // so a solution may mention them as if they were in scope.
            let bound: BTreeSet<Name> = binders.iter().cloned().collect();
            let outer: BTreeSet<Name> = outer.union(&bound).cloned().collect();
            let mut ties: Vec<(Name, Name)> = Vec::new();
            for (pat, b) in &targets {
                tie(pat, b, &index, &bound, &mut Vec::new(), &mut ties);
            }
            let mut sols = vec![sol.clone()];
            for (pat, b) in &targets {
                let mut next = Vec::new();
                for s in &sols {
                    next.extend(homs(pat, b, &index, &outer, &real, &bound, &ties, &mut Vec::new(), s.clone()));
                }
                // Two readings that agree on every template are one reading.
                let mut unique: Vec<Vec<Option<Template>>> = Vec::new();
                for s in next {
                    let same = |t: &Vec<Option<Template>>| {
                        t.iter().zip(&s).all(|(a, b)| match (a, b) {
                            (Some(a), Some(b)) => a.body() == b.body(),
                            (None, None) => true,
                            _ => false,
                        })
                    };
                    if !unique.iter().any(same) {
                        unique.push(s);
                    }
                }
                sols = unique;
            }
            let complete: Vec<&Vec<Option<Template>>> = sols.iter().filter(|s| s.iter().all(Option::is_some)).collect();
            let missing: Vec<&str> = params.iter().zip(&sol).filter(|(_, t)| t.is_none()).map(|((p, _), _)| p.as_str()).collect();
            match complete.len() {
                1 => sol = complete[0].clone(),
                0 => return Err(err(format!("can't work out {} for `{h}`: pass a template", missing.iter().map(|p| format!("`{p}`")).collect::<Vec<_>>().join(", ")))),
                _ => {
                    let readings: Vec<String> = complete
                        .iter()
                        .map(|s| {
                            params
                                .iter()
                                .zip(s.iter())
                                .filter(|((p, _), _)| missing.contains(&p.as_str()))
                                .map(|((p, _), t)| show_reading(p, t.as_ref().unwrap()))
                                .collect::<Vec<_>>()
                                .join(", ")
                        })
                        .collect();
                    return Err(err(format!("`{h}` has more than one reading here: {}. Pass a template", readings.join(" or "))));
                }
            }
        }
        let templates: Vec<Template> = sol.into_iter().map(|t| t.expect("every template was solved")).collect();
        // The instance is closed over the variables its templates mention, outermost first,
        // and instantiated back at them.
        let mut extras: Vec<(usize, Name)> = templates
            .iter()
            .flat_map(Template::extras)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .map(|x| (cx.var_index(x).expect("template variables are in scope"), x.clone()))
            .collect();
        extras.sort();
        let prefix: Vec<Name> = extras.into_iter().map(|(_, x)| x).collect();
        // A theorem has no hypotheses, so the kernel needs no evidence to instantiate it.
        let thm = lemma.apply(&templates.iter().collect::<Vec<_>>(), &prefix, &[]).map_err(|m| err(format!("{h}: {m}")))?;
        let mut o = Open { thm, layers: Vec::new() };
        for x in &prefix {
            o = self.instantiate(cx, &o, x).map_err(err)?;
        }
        self.feed(o, &given, args, cx, want)
    }
}

/// Whether `b` is a likely misspelling of `a`: one edit, or two for longer names, where an edit
/// is a letter added, dropped or changed, or two neighbours swapped. One-letter names are all
/// one edit apart, so they get no suggestion.
fn close(a: &str, b: &str) -> bool {
    let (a, b): (Vec<char>, Vec<char>) = (a.chars().collect(), b.chars().collect());
    let mut d = vec![vec![0; b.len() + 1]; a.len() + 1];
    for (i, row) in d.iter_mut().enumerate() {
        row[0] = i;
    }
    for j in 0..=b.len() {
        d[0][j] = j;
    }
    for i in 1..=a.len() {
        for j in 1..=b.len() {
            d[i][j] = (d[i - 1][j] + 1).min(d[i][j - 1] + 1).min(d[i - 1][j - 1] + usize::from(a[i - 1] != b[j - 1]));
            if i > 1 && j > 1 && a[i - 1] == b[j - 2] && a[i - 2] == b[j - 1] {
                d[i][j] = d[i][j].min(d[i - 2][j - 2] + 1);
            }
        }
    }
    let n = d[a.len()][b.len()];
    a.len() > 1 && n > 0 && n <= if a.len() > 5 { 2 } else { 1 }
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

/// Matches `pat` against `tgt`, solving the variables in `metas` as the variables of `tgt`
/// they stand against. Binders are paired through `env`; a solution may not be a variable
/// bound inside `tgt`.
pub(crate) fn match_vars(
    pat: &Formula,
    tgt: &Formula,
    metas: &BTreeSet<Name>,
    env: &mut Vec<(Name, Name)>,
    sol: &mut HashMap<Name, Name>,
) -> bool {
    fn var(x: &Name, y: &Name, metas: &BTreeSet<Name>, env: &[(Name, Name)], sol: &mut HashMap<Name, Name>) -> bool {
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
    match (pat.node(), tgt.node()) {
        (Node::Atom(p, xs), Node::Atom(q, ys)) => {
            p == q && xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| var(x, y, metas, env, sol))
        }
        (Node::Absurd, Node::Absurd) => true,
        (Node::And(a, b), Node::And(c, d)) | (Node::Or(a, b), Node::Or(c, d)) | (Node::Imp(a, b), Node::Imp(c, d)) => {
            match_vars(a, c, metas, env, sol) && match_vars(b, d, metas, env, sol)
        }
        (Node::All(x, a), Node::All(y, b)) | (Node::Ex(x, a), Node::Ex(y, b)) => {
            env.push((x.clone(), y.clone()));
            let ok = match_vars(a, b, metas, env, sol);
            env.pop();
            ok
        }
        _ => false,
    }
}

// ---- inferring a theorem's predicate arguments ----

/// Every solution of matching an antecedent against a line's formula, extending `sol`: each
/// predicate parameter applied to distinct bound variables gets a template. `env` pairs the
/// antecedent's binders with the formula's; `outer` are variables in scope a template may
/// mention. A parameter's argument may occur in the formula both through the hole and on its
/// own, so there can be several readings; all are returned, and the caller insists on one.
fn homs(
    pat: &Formula,
    tgt: &Formula,
    params: &HashMap<&str, usize>,
    outer: &BTreeSet<Name>,
    real: &BTreeSet<Name>,
    loose: &BTreeSet<Name>,
    ties: &[(Name, Name)],
    env: &mut Vec<(Name, Name)>,
    sol: Vec<Option<Template>>,
) -> Vec<Vec<Option<Template>>> {
    // The formula's binder for the antecedent's bound variable, unless an inner binder of the
    // formula reuses its name. A loose variable, one of the theorem's leading binders, is the
    // variable it was tied to, or itself when nothing tied it.
    let image = |x: &Name, env: &[(Name, Name)]| {
        let Some(i) = env.iter().rposition(|(p, _)| p == x) else {
            return loose.contains(x).then(|| ties.iter().find(|(a, _)| a == x).map_or(x.clone(), |(_, b)| b.clone()));
        };
        let t = &env[i].1;
        (!env[i + 1..].iter().any(|(_, u)| u == t)).then(|| t.clone())
    };
    match (pat.node(), tgt.node()) {
        (Node::Atom(p, pargs), _) if params.contains_key(&**p) => {
            // A loose binder nothing has tied, occurring only here, may stand for any variable
            // in scope that the formula mentions: one reading per choice, each of which must
            // use its hole, since a reading that ignores it would leave the binder unsolved.
            if let Some(x) = pargs.iter().find(|a| loose.contains(*a) && !env.iter().any(|(q, _)| q == *a) && !ties.iter().any(|(q, _)| q == *a)) {
                let mut out = Vec::new();
                let hole_of = pargs.iter().position(|a| a == x).unwrap();
                for v in tgt.free_vars().iter().filter(|v| real.contains(*v)) {
                    let mut ties2 = ties.to_vec();
                    ties2.push((x.clone(), v.clone()));
                    for s in homs(pat, tgt, params, outer, real, loose, &ties2, env, sol.clone()) {
                        let i = params[&**p];
                        let used = s[i].as_ref().is_some_and(|t| t.body().is_free(&hole_names(pargs.len())[hole_of]));
                        if used {
                            out.push(s);
                        }
                    }
                }
                return out;
            }
            let Some(args) = pargs.iter().map(|a| image(a, env)).collect::<Option<Vec<_>>>() else { return Vec::new() };
            let i = params[&**p];
            match &sol[i] {
                Some(t) => {
                    if t.apply(&args) == *tgt {
                        vec![sol]
                    } else {
                        Vec::new()
                    }
                }
                None => {
                    let distinct: BTreeSet<&Name> = args.iter().collect();
                    let ok = |v: &Name| args.contains(v) || (outer.contains(v) && !env.iter().any(|(_, t)| t == v));
                    if distinct.len() != args.len() || !tgt.free_vars().iter().all(ok) {
                        return Vec::new();
                    }
                    let holes = hole_names(args.len());
                    // An argument may also stand for itself only if it is a variable in scope
                    // outside the formula, not one the formula or the theorem binds.
                    let keep: Vec<bool> = args.iter().map(|a| real.contains(a) && !env.iter().any(|(_, t)| t == a)).collect();
                    let mut out = Vec::new();
                    for body in abstractions(tgt, &args, &holes, &keep) {
                        if let Ok(t) = Template::new(holes.clone(), body) {
                            let mut s = sol.clone();
                            s[i] = Some(t);
                            out.push(s);
                        }
                    }
                    out
                }
            }
        }
        (Node::Atom(p, xs), Node::Atom(q, ys)) => {
            // A loose binder matches whatever variable stands against it.
            let fits = |x: &Name, y: &Name| {
                if loose.contains(x) && !env.iter().any(|(p, _)| p == x) && !ties.iter().any(|(a, _)| a == x) {
                    return true;
                }
                image(x, env).as_ref() == Some(y)
            };
            if p == q && xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| fits(x, y)) {
                vec![sol]
            } else {
                Vec::new()
            }
        }
        (Node::Absurd, Node::Absurd) => vec![sol],
        (Node::And(a, b), Node::And(c, d)) | (Node::Or(a, b), Node::Or(c, d)) | (Node::Imp(a, b), Node::Imp(c, d)) => {
            let mut out = Vec::new();
            for s in homs(a, c, params, outer, real, loose, ties, env, sol) {
                out.extend(homs(b, d, params, outer, real, loose, ties, env, s));
            }
            out
        }
        (Node::All(x, a), Node::All(y, b)) | (Node::Ex(x, a), Node::Ex(y, b)) => {
            env.push((x.clone(), y.clone()));
            let out = homs(a, b, params, outer, real, loose, ties, env, sol);
            env.pop();
            out
        }
        _ => Vec::new(),
    }
}

/// Ties the theorem's loose binders to the variables that stand against them in a target,
/// by walking both formulas in parallel. Parameter atoms are skipped: they are what the
/// readings are about. A binder tied two ways is left untied.
fn tie(pat: &Formula, tgt: &Formula, params: &HashMap<&str, usize>, loose: &BTreeSet<Name>, env: &mut Vec<(Name, Name)>, ties: &mut Vec<(Name, Name)>) {
    match (pat.node(), tgt.node()) {
        (Node::Atom(p, _), _) if params.contains_key(&**p) => {}
        (Node::Atom(p, xs), Node::Atom(q, ys)) if p == q && xs.len() == ys.len() => {
            for (x, y) in xs.iter().zip(ys) {
                if loose.contains(x) && !env.iter().any(|(a, _)| a == x) && !env.iter().any(|(_, b)| b == y) {
                    match ties.iter().position(|(a, _)| a == x) {
                        Some(i) if ties[i].1 != *y => {
                            ties.remove(i);
                        }
                        Some(_) => {}
                        None => ties.push((x.clone(), y.clone())),
                    }
                }
            }
        }
        (Node::And(a, b), Node::And(c, d)) | (Node::Or(a, b), Node::Or(c, d)) | (Node::Imp(a, b), Node::Imp(c, d)) => {
            tie(a, c, params, loose, env, ties);
            tie(b, d, params, loose, env, ties);
        }
        (Node::All(x, a), Node::All(y, b)) | (Node::Ex(x, a), Node::Ex(y, b)) => {
            env.push((x.clone(), y.clone()));
            tie(a, b, params, loose, env, ties);
            env.pop();
        }
        _ => {}
    }
}

/// Every way to read `f` as a template body over `holes`: each free occurrence of an argument
/// variable either becomes its hole or stays. The reading with every occurrence a hole comes
/// first.
fn abstractions(f: &Formula, args: &[Name], holes: &[Name], keep: &[bool]) -> Vec<Formula> {
    fn go(f: &Formula, args: &[Name], holes: &[Name], keep: &[bool], bound: &mut Vec<Name>) -> Vec<Formula> {
        match f.node() {
            Node::Absurd => vec![f.clone()],
            Node::Atom(p, xs) => {
                let mut outs: Vec<Vec<Name>> = vec![Vec::new()];
                for x in xs {
                    let choices: Vec<Name> = match args.iter().position(|a| a == x) {
                        Some(i) if !bound.contains(x) && keep[i] => vec![holes[i].clone(), x.clone()],
                        Some(i) if !bound.contains(x) => vec![holes[i].clone()],
                        _ => vec![x.clone()],
                    };
                    outs = outs.into_iter().flat_map(|v| choices.iter().map(move |c| v.iter().cloned().chain(std::iter::once(c.clone())).collect::<Vec<_>>())).collect();
                }
                outs.into_iter().map(|v| atom(p, &v)).collect()
            }
            Node::And(a, b) | Node::Or(a, b) | Node::Imp(a, b) => {
                let mut out = Vec::new();
                for l in go(a, args, holes, keep, bound) {
                    for r in go(b, args, holes, keep, bound) {
                        out.push(match f.node() {
                            Node::And(..) => and(l.clone(), r),
                            Node::Or(..) => or(l.clone(), r),
                            _ => imp(l.clone(), r),
                        });
                    }
                }
                out
            }
            Node::All(x, a) | Node::Ex(x, a) => {
                bound.push(x.clone());
                let bodies = go(a, args, holes, keep, bound);
                bound.pop();
                bodies.into_iter().map(|b| if matches!(f.node(), Node::All(..)) { all(x, b) } else { ex(x, b) }).collect()
            }
        }
    }
    go(f, args, holes, keep, &mut Vec::new())
}
