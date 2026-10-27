//! The grammar in `SPEC.md`, read with two tokens of lookahead: after a justification's
//! arguments, a lowercase name is the next label if a colon follows it. Nothing here knows what a
//! formula means: the checker reads the trees this produces.

use crate::lexer::{Kw, Sym, Tok, Token};
use crate::Error;

/// A formula as written. Definitions are still names here.
#[derive(Clone, Debug)]
pub enum FExpr {
    Absurd(usize),
    /// `Name targ*`: a predicate, definition or parameter applied.
    Atom { name: String, args: Vec<TArg>, line: usize },
    Not(Box<FExpr>, usize),
    And(Box<FExpr>, Box<FExpr>, usize),
    Or(Box<FExpr>, Box<FExpr>, usize),
    Imp(Box<FExpr>, Box<FExpr>, usize),
    Forall(Vec<String>, Box<FExpr>, usize),
    Exists(Vec<String>, Box<FExpr>, usize),
}

/// An argument of a predicate or definition: a variable, a bare name, or a parenthesized
/// formula (which, when it is a bare application, may also be read as a template).
#[derive(Clone, Debug)]
pub enum TArg {
    Var(String, usize),
    Name(String, usize),
    Paren(Box<FExpr>),
}

impl FExpr {
    pub fn line(&self) -> usize {
        match self {
            FExpr::Absurd(l) | FExpr::Atom { line: l, .. } | FExpr::Not(_, l) | FExpr::And(.., l) | FExpr::Or(.., l) => *l,
            FExpr::Imp(.., l) | FExpr::Forall(.., l) | FExpr::Exists(.., l) => *l,
        }
    }
}

impl TArg {
    pub fn line(&self) -> usize {
        match self {
            TArg::Var(_, l) | TArg::Name(_, l) => *l,
            TArg::Paren(f) => f.line(),
        }
    }
}

/// An argument after the rule: a line, variable or theorem by name, or a theorem's instance
/// in parentheses with templates.
#[derive(Clone, Debug)]
pub enum Arg {
    Ident(String, usize),
    Instance { head: String, targs: Vec<TArg>, line: usize },
}

impl Arg {
    pub fn line(&self) -> usize {
        match self {
            Arg::Ident(_, l) | Arg::Instance { line: l, .. } => *l,
        }
    }
}

/// `by rule args`.
#[derive(Clone, Debug)]
pub struct Just {
    pub rule: String,
    pub args: Vec<Arg>,
    pub line: usize,
}

/// A declared parameter: a predicate with placeholders fixing its arity, `(P x y)`, or a
/// lowercase individual of a definition. A theorem's `predicate P x y` is the same without
/// parentheses.
#[derive(Clone, Debug)]
pub struct Param {
    pub name: String,
    pub holes: Vec<String>,
    pub line: usize,
}

#[derive(Clone, Debug)]
pub struct Assume {
    pub label: String,
    pub formula: FExpr,
    pub line: usize,
}

#[derive(Clone, Debug)]
pub struct Line {
    pub label: String,
    pub formula: FExpr,
    pub just: Just,
    pub line: usize,
}

#[derive(Clone, Debug)]
pub enum Step {
    Line(Line),
    Lemma { name: String, block: Block, line: usize },
}

/// `therefore F`: the closing line of a block. It closes the line right above it.
#[derive(Clone, Debug)]
pub struct Therefore {
    pub formula: FExpr,
    pub line: usize,
}

/// A theorem's or lemma's block: its declarations in order, its steps, and its closing line.
#[derive(Clone, Debug)]
pub struct Block {
    pub variables: Vec<(String, usize)>,
    pub predicates: Vec<Param>,
    pub assumes: Vec<Assume>,
    pub steps: Vec<Step>,
    pub therefore: Therefore,
}

#[derive(Clone, Debug)]
pub enum Item {
    Predicate { name: String, holes: Vec<String>, line: usize },
    Define { name: String, params: Vec<Param>, body: FExpr, line: usize },
    Theorem { name: String, block: Block, line: usize },
}

/// `import PATH`: the file `PATH.hai`, relative to this one.
#[derive(Clone, Debug)]
pub struct Import {
    pub name: String,
    pub line: usize,
}

#[derive(Clone, Debug)]
pub struct File {
    pub imports: Vec<Import>,
    pub items: Vec<Item>,
}

pub fn parse(toks: &[Token]) -> Result<File, Error> {
    let mut p = Parser { toks, pos: 0 };
    let mut imports = Vec::new();
    while p.peek() == Some(&Tok::Kw(Kw::Import)) {
        let line = p.line();
        p.pos += 1;
        let Some(Tok::Path(name)) = p.peek() else {
            return Err(p.err("expected a path after `import`"));
        };
        imports.push(Import { name: name.clone(), line });
        p.pos += 1;
    }
    let mut items = Vec::new();
    while p.pos < toks.len() {
        items.push(p.item()?);
    }
    Ok(File { imports, items })
}

struct Parser<'a> {
    toks: &'a [Token],
    pos: usize,
}

const ITEM_KEYWORDS: [Kw; 4] = [Kw::Theorem, Kw::Define, Kw::Import, Kw::Predicate];

/// The sections of a block, in the order they must come.
const SECTIONS: [(Kw, &str); 3] = [(Kw::Predicate, "predicate"), (Kw::Variable, "variable"), (Kw::Assume, "assume")];

impl Parser<'_> {
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos).map(|t| &t.tok)
    }

    fn peek2(&self) -> Option<&Tok> {
        self.toks.get(self.pos + 1).map(|t| &t.tok)
    }

    fn line(&self) -> usize {
        self.toks.get(self.pos).or(self.toks.last()).map_or(1, |t| t.line)
    }

    fn err(&self, msg: impl Into<String>) -> Error {
        Error::new(self.line(), msg)
    }

    fn eat(&mut self, t: impl Into<Tok>) -> bool {
        if self.peek() == Some(&t.into()) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn expect(&mut self, t: impl Into<Tok>, what: &str) -> Result<(), Error> {
        if self.eat(t) {
            Ok(())
        } else {
            Err(self.err(format!("expected {what}")))
        }
    }

    /// The `)` for a `(` on line `open`. When the formula ran on to a later line without it, the
    /// error points at the `(`.
    fn close(&mut self, open: usize) -> Result<(), Error> {
        if self.eat(Sym::RParen) {
            return Ok(());
        }
        if self.line() > open {
            return Err(Error::new(open, "this `(` has no `)`"));
        }
        Err(self.err("expected `)`"))
    }

    fn at_item_keyword(&self) -> bool {
        match self.peek() {
            None => true,
            Some(Tok::Kw(k)) => ITEM_KEYWORDS.contains(k),
            _ => false,
        }
    }

    fn lower(&mut self, what: &str) -> Result<String, Error> {
        match self.peek() {
            Some(Tok::Lower(n)) => {
                let n = n.clone();
                self.pos += 1;
                Ok(n)
            }
            Some(Tok::Upper(n)) => Err(self.err(format!("expected {what}, which is lowercase, not `{n}`"))),
            Some(Tok::Kw(k)) => {
                let word = crate::lexer::KEYWORDS.iter().find(|(_, x)| x == k).map_or("?", |(w, _)| w);
                Err(self.err(format!("expected {what}, and `{word}` is a keyword")))
            }
            _ => Err(self.err(format!("expected {what}"))),
        }
    }

    fn upper(&mut self, what: &str) -> Result<String, Error> {
        match self.peek() {
            Some(Tok::Upper(n)) => {
                let n = n.clone();
                self.pos += 1;
                Ok(n)
            }
            Some(Tok::Lower(n)) => Err(self.err(format!("expected {what}, which is capitalized, not `{n}`"))),
            _ => Err(self.err(format!("expected {what}"))),
        }
    }

    /// `label :`.
    /// The `:` after a theorem's or lemma's name: every name that can be cited has one.
    fn name_colon(&mut self, kind: &str, name: &str) -> Result<(), Error> {
        if self.eat(Sym::Colon) {
            Ok(())
        } else {
            Err(self.err(format!("a {kind}'s name is followed by a colon, like every name that can be cited: `{kind} {name}:`")))
        }
    }

    fn at_label(&self) -> bool {
        matches!(self.peek(), Some(Tok::Lower(_))) && self.peek2() == Some(&Tok::Sym(Sym::Colon))
    }

    /// Lowercase placeholders after a declared name, fixing its arity.
    fn holes(&mut self) -> Result<Vec<String>, Error> {
        let mut holes = Vec::new();
        while let Some(Tok::Lower(h)) = self.peek() {
            if self.at_label() {
                break;
            }
            if holes.contains(h) {
                return Err(self.err(format!("placeholder `{h}` appears twice")));
            }
            holes.push(h.clone());
            self.pos += 1;
        }
        Ok(holes)
    }

    /// A parameter of a definition: `(P x y)`, a statement `A`, or a lowercase individual.
    fn param(&mut self) -> Result<Option<Param>, Error> {
        let line = self.line();
        match self.peek() {
            Some(Tok::Sym(Sym::LParen)) => {
                self.pos += 1;
                let name = self.upper("a parameter's name after `(`")?;
                let holes = self.holes()?;
                if holes.is_empty() {
                    return Err(self.err(format!("`{name}` has no placeholders, so it goes without parentheses: `{name}`")));
                }
                self.expect(Sym::RParen, "`)` after the parameter's placeholders")?;
                Ok(Some(Param { name, holes, line }))
            }
            Some(Tok::Lower(n) | Tok::Upper(n)) => {
                let name = n.clone();
                self.pos += 1;
                Ok(Some(Param { name, holes: Vec::new(), line }))
            }
            _ => Ok(None),
        }
    }

    fn item(&mut self) -> Result<Item, Error> {
        let line = self.line();
        match self.peek() {
            Some(Tok::Kw(Kw::Predicate)) => {
                self.pos += 1;
                let name = self.upper("a predicate's name")?;
                let holes = self.holes()?;
                Ok(Item::Predicate { name, holes, line })
            }
            Some(Tok::Kw(Kw::Define)) => {
                self.pos += 1;
                let name = self.upper("a definition's name")?;
                let mut params = Vec::new();
                while let Some(p) = self.param()? {
                    params.push(p);
                }
                self.expect(Sym::Equals, "`=` after the definition's parameters")?;
                let body = self.formula()?;
                Ok(Item::Define { name, params, body, line })
            }
            Some(Tok::Kw(Kw::Theorem)) => {
                self.pos += 1;
                let name = self.lower("a theorem's name")?;
                self.name_colon("theorem", &name)?;
                let block = self.block(&name, false)?;
                Ok(Item::Theorem { name, block, line })
            }
            Some(Tok::Kw(Kw::Import)) => Err(self.err("imports come before everything else")),
            _ => Err(self.err("expected `theorem`, `define` or `predicate`")),
        }
    }

    /// Declarations in order, steps, then `therefore`. A lemma declares no predicates.
    fn block(&mut self, name: &str, lemma: bool) -> Result<Block, Error> {
        let mut variables = Vec::new();
        let mut predicates = Vec::new();
        let mut assumes = Vec::new();
        let mut section = 0;
        loop {
            let line = self.line();
            let Some(&Tok::Kw(k)) = self.peek() else { break };
            let Some(want) = SECTIONS.iter().position(|(s, _)| *s == k) else { break };
            if want < section {
                let (_, after) = SECTIONS[section];
                return Err(self.err(format!("`{}` lines come before `{after}` lines in a block", SECTIONS[want].1)));
            }
            section = want;
            self.pos += 1;
            match k {
                Kw::Variable => {
                    let first = variables.len();
                    while let Some(Tok::Lower(x)) = self.peek() {
                        if self.at_label() {
                            break;
                        }
                        variables.push((x.clone(), self.line()));
                        self.pos += 1;
                    }
                    if variables.len() == first {
                        return Err(self.err("`variable` needs at least one name"));
                    }
                }
                Kw::Predicate => {
                    let pname = self.upper("a predicate's name after `predicate`")?;
                    if lemma {
                        return Err(Error::new(line, format!("a lemma declares no predicates: declare `{pname}` in its theorem")));
                    }
                    let holes = self.holes()?;
                    predicates.push(Param { name: pname, holes, line });
                }
                Kw::Assume => {
                    let label = self.lower("the assumption's label")?;
                    if let Some(Tok::Sym(Sym::LParen)) = self.peek() {
                        return Err(self.err("an assumption takes no parameters: declare a theorem's predicates with `predicate`"));
                    }
                    self.expect(Sym::Colon, "`:` after the assumption's label")?;
                    let formula = self.formula()?;
                    assumes.push(Assume { label, formula, line });
                }
                _ => unreachable!(),
            }
        }
        let mut steps: Vec<Step> = Vec::new();
        loop {
            let line = self.line();
            match self.peek() {
                Some(Tok::Kw(Kw::Lemma)) => {
                    self.pos += 1;
                    let lemma = self.lower("the lemma's name")?;
                    self.name_colon("lemma", &lemma)?;
                    let block = self.block(&lemma, true)?;
                    steps.push(Step::Lemma { name: lemma, block, line });
                }
                Some(Tok::Kw(Kw::Therefore)) => {
                    self.pos += 1;
                    let formula = self.formula()?;
                    if self.peek() == Some(&Tok::Kw(Kw::By)) {
                        return Err(self.err("`therefore` takes no `by`: it closes the line right above it"));
                    }
                    let therefore = Therefore { formula, line };
                    return Ok(Block { variables, predicates, assumes, steps, therefore });
                }
                Some(Tok::Kw(k)) if SECTIONS.iter().any(|(s, _)| s == k) => {
                    return Err(self.err("declarations come before the steps of a block"));
                }
                _ if self.at_label() => steps.push(Step::Line(self.step_line()?)),
                _ if self.at_item_keyword() => {
                    // The `therefore` belongs after the block's last line, so that is where it's missing.
                    let last = self.toks.get(self.pos.wrapping_sub(1)).map_or(1, |t| t.line);
                    return Err(Error::new(last, format!("the block `{name}` has no `therefore`")));
                }
                _ => return Err(self.step_error(&steps)),
            }
        }
    }

    /// The error for a token where a step should start. A lowercase name read as an argument of
    /// the previous line is probably a label without its colon.
    fn step_error(&self, steps: &[Step]) -> Error {
        if let Some(Step::Line(prev)) = steps.last() {
            let name = |a: &Arg| match a {
                Arg::Ident(n, l) | Arg::Instance { head: n, line: l, .. } => (n.clone(), *l),
            };
            // The first argument on a line of its own, or else the last one if a formula follows it.
            let formula_next = matches!(self.peek(), Some(Tok::Upper(_) | Tok::Sym(Sym::LParen) | Tok::Kw(Kw::Forall | Kw::Exists | Kw::Not | Kw::Absurd)));
            let stray = prev.just.args.iter().map(name).find(|(_, l)| *l > prev.just.line).or_else(|| match prev.just.args.last() {
                Some(Arg::Ident(n, l)) if *l < self.line() || formula_next => Some((n.clone(), *l)),
                _ => None,
            });
            if let Some((n, l)) = stray {
                return Error::new(l, format!("`{n}` was read as an argument of the line above. If it is a label, it needs a colon: `{n}:`"));
            }
        }
        match self.peek() {
            Some(Tok::Lower(n)) => self.err(format!("expected a label: `{n}:`")),
            _ => self.err("expected a labeled line, a `lemma`, or `therefore`"),
        }
    }

    fn step_line(&mut self) -> Result<Line, Error> {
        let line = self.line();
        let label = self.lower("a label")?;
        self.expect(Sym::Colon, "`:`")?;
        let formula = self.formula()?;
        self.expect(Kw::By, "`by` after the formula")?;
        let just = self.just()?;
        Ok(Line { label, formula, just, line })
    }

    /// A name after `by`, or after `(`: a rule, line, variable or theorem, all lowercase.
    fn name_after_by(&mut self) -> Result<String, Error> {
        match self.peek() {
            Some(Tok::Lower(_)) => self.lower(""),
            Some(Tok::Upper(n)) => Err(self.err(format!("`{n}` is capitalized, so it isn't a rule, line or theorem: templates follow their theorem, `t {n}`"))),
            _ => Err(self.err("expected a rule, line, variable or theorem")),
        }
    }

    fn just(&mut self) -> Result<Just, Error> {
        let line = self.line();
        let rule = self.name_after_by()?;
        let mut args = Vec::new();
        loop {
            match self.peek() {
                // A lowercase name is an argument unless it's the next step's label.
                Some(Tok::Lower(n)) if !self.at_label() => {
                    let (head, l) = (n.clone(), self.line());
                    self.pos += 1;
                    // `thm T1 T2`: a theorem instance as an argument.
                    let targs = self.templates()?;
                    args.push(if targs.is_empty() { Arg::Ident(head, l) } else { Arg::Instance { head, targs, line: l } });
                }
                Some(Tok::Upper(_)) => {
                    self.name_after_by()?;
                }
                Some(Tok::Sym(Sym::LParen)) => {
                    self.pos += 1;
                    match self.peek() {
                        Some(Tok::Lower(n)) if crate::check::RULES.contains(&n.as_str()) => {
                            return Err(self.err(format!("one rule per line: give `{n}` a line of its own")));
                        }
                        Some(Tok::Lower(n)) => return Err(self.err(format!("a theorem's templates follow its name, without parentheses: `{n} T`"))),
                        _ => return Err(self.err("a template in parentheses follows its theorem: `t (T a)`")),
                    }
                }
                _ => break,
            }
        }
        Ok(Just { rule, args, line })
    }

    /// Templates after a theorem: a name, or in parentheses a predicate given arguments or a
    /// formula. They end at the first lowercase name, the first line fed to the theorem.
    fn templates(&mut self) -> Result<Vec<TArg>, Error> {
        let mut out = Vec::new();
        loop {
            match self.peek() {
                Some(Tok::Upper(n)) if self.peek2() != Some(&Tok::Sym(Sym::Dot)) => {
                    out.push(TArg::Name(n.clone(), self.line()));
                    self.pos += 1;
                }
                Some(Tok::Sym(Sym::LParen)) if !matches!(self.peek2(), Some(Tok::Lower(_))) => out.push(self.paren_targ()?),
                _ => break,
            }
        }
        Ok(out)
    }

    /// `( formula )` as a template, which a lone name doesn't need.
    fn paren_targ(&mut self) -> Result<TArg, Error> {
        let open = self.line();
        self.pos += 1;
        let f = self.formula()?;
        if let FExpr::Atom { name, args, .. } = &f {
            if args.is_empty() {
                return Err(self.err(format!("`{name}` has no arguments, so it goes without parentheses: `{name}`")));
            }
        }
        self.close(open)?;
        Ok(TArg::Paren(Box::new(f)))
    }

    /// Arguments of a predicate or definition in a formula.
    fn targs(&mut self) -> Result<Vec<TArg>, Error> {
        let mut out = Vec::new();
        loop {
            match self.peek() {
                Some(Tok::Upper(n)) => {
                    out.push(TArg::Name(n.clone(), self.line()));
                    self.pos += 1;
                }
                // A lowercase name is an argument unless it's the next line's label.
                Some(Tok::Lower(n)) if !self.at_label() => {
                    out.push(TArg::Var(n.clone(), self.line()));
                    self.pos += 1;
                }
                Some(Tok::Sym(Sym::LParen)) => out.push(self.paren_targ()?),
                _ => break,
            }
        }
        Ok(out)
    }

    // ---- formulas ----

    /// formula := quantified | disj ('->' formula)?
    pub fn formula(&mut self) -> Result<FExpr, Error> {
        let line = self.line();
        let left = self.disj()?;
        if self.eat(Sym::Arrow) {
            let right = self.formula()?;
            return Ok(FExpr::Imp(Box::new(left), Box::new(right), line));
        }
        Ok(left)
    }

    fn disj(&mut self) -> Result<FExpr, Error> {
        let line = self.line();
        let first = self.conj()?;
        if self.peek() != Some(&Tok::Kw(Kw::Or)) {
            return Ok(first);
        }
        let mut parts = vec![first];
        while self.eat(Kw::Or) {
            parts.push(self.conj()?);
        }
        Ok(parts.into_iter().rev().reduce(|acc, f| FExpr::Or(Box::new(f), Box::new(acc), line)).unwrap())
    }

    fn conj(&mut self) -> Result<FExpr, Error> {
        let line = self.line();
        let first = self.neg()?;
        if self.peek() != Some(&Tok::Kw(Kw::And)) {
            return Ok(first);
        }
        let mut parts = vec![first];
        while self.eat(Kw::And) {
            parts.push(self.neg()?);
        }
        Ok(parts.into_iter().rev().reduce(|acc, f| FExpr::And(Box::new(f), Box::new(acc), line)).unwrap())
    }

    /// neg := 'not' neg | quantifier | atom. A quantifier's body extends as far right as it can.
    fn neg(&mut self) -> Result<FExpr, Error> {
        let line = self.line();
        match self.peek() {
            Some(Tok::Kw(Kw::Not)) => {
                self.pos += 1;
                Ok(FExpr::Not(Box::new(self.neg()?), line))
            }
            Some(Tok::Kw(q @ (Kw::Forall | Kw::Exists))) => {
                let q = *q;
                self.pos += 1;
                let mut vars = Vec::new();
                while let Some(Tok::Lower(_)) = self.peek() {
                    vars.push(self.lower("")?);
                }
                if vars.is_empty() {
                    return Err(self.err("a quantifier binds lowercase variables, then `.`"));
                }
                self.expect(Sym::Dot, "`.` after the quantifier's variables")?;
                let body = self.formula()?;
                Ok(match q {
                    Kw::Forall => FExpr::Forall(vars, Box::new(body), line),
                    _ => FExpr::Exists(vars, Box::new(body), line),
                })
            }
            _ => self.atom(),
        }
    }

    fn atom(&mut self) -> Result<FExpr, Error> {
        let line = self.line();
        match self.peek() {
            Some(Tok::Kw(Kw::Absurd)) => {
                self.pos += 1;
                Ok(FExpr::Absurd(line))
            }
            Some(Tok::Upper(_)) => {
                let name = self.upper("")?;
                let args = self.targs()?;
                if self.peek() == Some(&Tok::Sym(Sym::Dot)) {
                    return Err(self.err(format!("`{name}.` is not a formula: `.` only ends a quantifier's variables")));
                }
                Ok(FExpr::Atom { name, args, line })
            }
            Some(Tok::Sym(Sym::LParen)) => {
                self.pos += 1;
                let f = self.formula()?;
                self.close(line)?;
                Ok(f)
            }
            Some(Tok::Lower(n)) => Err(self.err(format!("`{n}` is lowercase, so it isn't a statement or predicate"))),
            _ => Err(self.err("expected a formula")),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::lex;

    fn show(f: &FExpr) -> String {
        match f {
            FExpr::Absurd(_) => "absurd".into(),
            FExpr::Atom { name, args, .. } => {
                let args: Vec<String> = args.iter().map(|a| match a {
                    TArg::Var(v, _) | TArg::Name(v, _) => v.clone(),
                    TArg::Paren(f) => format!("({})", show(f)),
                }).collect();
                if args.is_empty() { name.clone() } else { format!("({} {})", name, args.join(" ")) }
            }
            FExpr::Not(a, _) => format!("(not {})", show(a)),
            FExpr::And(a, b, _) => format!("(and {} {})", show(a), show(b)),
            FExpr::Or(a, b, _) => format!("(or {} {})", show(a), show(b)),
            FExpr::Imp(a, b, _) => format!("(imp {} {})", show(a), show(b)),
            FExpr::Forall(xs, a, _) => format!("(forall {} {})", xs.join(" "), show(a)),
            FExpr::Exists(xs, a, _) => format!("(exists {} {})", xs.join(" "), show(a)),
        }
    }

    fn parsed(src: &str) -> Vec<Item> {
        parse(&lex(src).unwrap()).unwrap().items
    }

    fn formula(src: &str) -> String {
        let items = parsed(&format!("define X = {src}"));
        let Item::Define { body, .. } = &items[0] else { panic!() };
        show(body)
    }

    #[test]
    fn precedence() {
        assert_eq!(formula("A -> B -> C"), "(imp A (imp B C))");
        assert_eq!(formula("not A and B or C -> D"), "(imp (or (and (not A) B) C) D)");
        assert_eq!(formula("A and B and C"), "(and A (and B C))");
        assert_eq!(formula("forall x y. P x -> Q y"), "(forall x y (imp (P x) (Q y)))");
        assert_eq!(formula("(forall x. P x) -> exists y. Q y"), "(imp (forall x (P x)) (exists y (Q y)))");
        assert_eq!(formula("A and forall x. P x -> B"), "(and A (forall x (imp (P x) B)))");
        assert_eq!(formula("Iff (In z x) (In z y and P z)"), "(Iff ((In z x)) ((and (In z y) (P z))))");
    }

    #[test]
    fn items() {
        let src = "predicate P x\ndefine Iff A B = (A -> B) and (B -> A)\ndefine Ind (Q x) = Q x -> forall x. Q x\n\
                   theorem t:\n  predicate R y\n  variable x\n  assume i: Ind R\n  assume a: A\n  therefore A -> A";
        let items = parsed(src);
        assert!(matches!(&items[0], Item::Predicate { name, holes, .. } if name == "P" && holes == &["x"]));
        let Item::Define { params, .. } = &items[1] else { panic!() };
        assert_eq!(params.iter().map(|p| p.name.as_str()).collect::<Vec<_>>(), ["A", "B"]);
        let Item::Define { params, .. } = &items[2] else { panic!() };
        assert!(params[0].name == "Q" && params[0].holes == ["x"]);
        let Item::Theorem { block, .. } = &items[3] else { panic!() };
        assert_eq!(block.variables[0].0, "x");
        assert_eq!(block.predicates[0].holes, ["y"]);
        assert_eq!(block.assumes.len(), 2);
        assert_eq!(show(&block.therefore.formula), "(imp A A)");
    }

    #[test]
    fn blocks_and_justifications() {
        let src = "theorem t:\n assume h: A or B\n lemma l:\n  assume a: A\n  r: B or A by or_i a\n  therefore A -> B or A\n \
                   k: B by forall_e pz w x\n m: C by imp_e ind k l\n n: D by imp_e f Unicorn u h\n therefore A";
        let items = parsed(src);
        let Item::Theorem { block, .. } = &items[0] else { panic!() };
        assert_eq!(block.steps.len(), 4);
        let Step::Lemma { name, block: inner, .. } = &block.steps[0] else { panic!() };
        assert_eq!(name, "l");
        assert_eq!(inner.steps.len(), 1);
        let Step::Line(k) = &block.steps[1] else { panic!() };
        assert_eq!(k.just.rule, "forall_e");
        assert!(matches!(&k.just.args[0], Arg::Ident(n, _) if n == "pz"));
        assert_eq!(k.just.args.len(), 3);
        let Step::Line(m) = &block.steps[2] else { panic!() };
        assert_eq!(m.just.args.len(), 3);
        let Step::Line(n) = &block.steps[3] else { panic!() };
        assert!(matches!(&n.just.args[0], Arg::Instance { head, targs, .. } if head == "f" && targs.len() == 1));
        assert_eq!(n.just.args.len(), 3);
    }

    #[test]
    fn errors() {
        let e = parse(&lex("theorem t:\n assume b: B\n variable x\n therefore B").unwrap()).unwrap_err();
        assert_eq!((e.line, e.msg.as_str()), (3, "`variable` lines come before `assume` lines in a block"));
        let e = parse(&lex("theorem t:\n variable x\n predicate P y\n therefore B").unwrap()).unwrap_err();
        assert_eq!((e.line, e.msg.as_str()), (3, "`predicate` lines come before `variable` lines in a block"));
        let e = parse(&lex("theorem t:\n a: A by reit x\n assume b: B\n therefore A").unwrap()).unwrap_err();
        assert_eq!((e.line, e.msg.as_str()), (3, "declarations come before the steps of a block"));
        let e = parse(&lex("theorem t:\n a: A by reit x\ntheorem u:").unwrap()).unwrap_err();
        assert_eq!(e.msg, "the block `t` has no `therefore`");
        let e = parse(&lex("theorem t:\n a: A by reit x\n therefore A by a").unwrap()).unwrap_err();
        assert_eq!((e.line, e.msg.as_str()), (3, "`therefore` takes no `by`: it closes the line right above it"));
        let e = parse(&lex("theorem t\n a: A by reit x\n therefore A").unwrap()).unwrap_err();
        assert_eq!((e.line, e.msg.as_str()), (2, "a theorem's name is followed by a colon, like every name that can be cited: `theorem t:`"));
        let e = parse(&lex("theorem t:\n lemma l\n  a: A by reit x\n  therefore A\n therefore A").unwrap()).unwrap_err();
        assert_eq!((e.line, e.msg.as_str()), (3, "a lemma's name is followed by a colon, like every name that can be cited: `lemma l:`"));
        let e = parse(&lex("theorem t:\n a: A by reit x\n p Person x by reit a\n therefore A").unwrap()).unwrap_err();
        assert_eq!((e.line, e.msg.as_str()), (3, "`p` was read as an argument of the line above. If it is a label, it needs a colon: `p:`"));
        let e = parse(&lex("define X = x").unwrap()).unwrap_err();
        assert_eq!(e.msg, "`x` is lowercase, so it isn't a statement or predicate");
        let e = parse(&lex("define X\nimport a").unwrap()).unwrap_err();
        assert!(e.msg.contains("expected `=`"));
    }

    #[test]
    fn whitespace_independent() {
        let a = parsed("theorem t: assume a: A therefore A");
        let b = parsed("theorem t\n  :\n  assume a:\n    A\n  therefore\n    A");
        assert_eq!(format!("{a:?}").replace(char::is_numeric, ""), format!("{b:?}").replace(char::is_numeric, ""));
    }
}
