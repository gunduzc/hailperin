//! The grammar in `SPEC.md`, read with two tokens of lookahead. Nothing here knows what a
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

/// What a justification cites: a rule, a line, a theorem, or a theory member.
#[derive(Clone, Debug)]
pub enum Ref {
    Name(String),
    Member { theory: String, member: String },
}

/// An argument after the rule: a line or variable by name, a theory member, or an instance
/// in parentheses with templates.
#[derive(Clone, Debug)]
pub enum Arg {
    Ident(String, usize),
    Ref(Ref, usize),
    Instance { head: Ref, targs: Vec<TArg>, line: usize },
}

impl Arg {
    pub fn line(&self) -> usize {
        match self {
            Arg::Ident(_, l) | Arg::Ref(_, l) | Arg::Instance { line: l, .. } => *l,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Just {
    pub head: Ref,
    /// Templates right after the head, for a theory member or a theorem.
    pub targs: Vec<TArg>,
    pub args: Vec<Arg>,
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

/// Assumptions, steps, then the result: the line labeled with the block's own name.
#[derive(Clone, Debug)]
pub struct Block {
    pub assumes: Vec<Assume>,
    pub steps: Vec<Step>,
    pub result: Line,
}

#[derive(Clone, Debug)]
pub enum Member {
    Include { theory: String, line: usize },
    Axiom { label: String, params: Vec<String>, formula: FExpr, line: usize },
}

#[derive(Clone, Debug)]
pub enum Item {
    Define { name: String, params: Vec<String>, body: FExpr, line: usize },
    Theory { name: String, members: Vec<Member>, line: usize },
    Theorem { name: String, theories: Vec<String>, block: Block, line: usize },
}

/// `import NAME`: the file `NAME.hai` next to this one.
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
        imports.push(Import { name: p.lower("a file name")?, line });
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

const ITEM_KEYWORDS: [Kw; 4] = [Kw::Theorem, Kw::Theory, Kw::Define, Kw::Import];

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

    /// `label :`, or `label Name... :` for a theory member with parameters.
    fn at_label(&self) -> bool {
        if !matches!(self.peek(), Some(Tok::Lower(_))) {
            return false;
        }
        let mut j = self.pos + 1;
        while matches!(self.toks.get(j).map(|t| &t.tok), Some(Tok::Upper(_))) {
            j += 1;
        }
        matches!(self.toks.get(j).map(|t| &t.tok), Some(Tok::Sym(Sym::Colon)))
    }

    fn item(&mut self) -> Result<Item, Error> {
        let line = self.line();
        match self.peek() {
            Some(Tok::Kw(Kw::Define)) => {
                self.pos += 1;
                let name = self.upper("a definition's name")?;
                let mut params = Vec::new();
                loop {
                    match self.peek() {
                        Some(Tok::Upper(n) | Tok::Lower(n)) => {
                            params.push(n.clone());
                            self.pos += 1;
                        }
                        _ => break,
                    }
                }
                self.expect(Sym::Equals, "`=` after the definition's parameters")?;
                let body = self.formula()?;
                Ok(Item::Define { name, params, body, line })
            }
            Some(Tok::Kw(Kw::Theory)) => {
                self.pos += 1;
                let name = self.upper("a theory's name")?;
                let mut members = Vec::new();
                while !self.at_item_keyword() {
                    members.push(self.member()?);
                }
                Ok(Item::Theory { name, members, line })
            }
            Some(Tok::Kw(Kw::Theorem)) => {
                self.pos += 1;
                let name = self.lower("a theorem's name")?;
                let mut theories = Vec::new();
                if self.eat(Kw::In) {
                    theories.push(self.upper("a theory's name after `in`")?);
                    while let Some(Tok::Upper(_)) = self.peek() {
                        theories.push(self.upper("")?);
                    }
                }
                let block = self.block(&name)?;
                Ok(Item::Theorem { name, theories, block, line })
            }
            Some(Tok::Kw(Kw::Import)) => Err(self.err("imports come before everything else")),
            _ => Err(self.err("expected `theorem`, `theory` or `define`")),
        }
    }

    fn member(&mut self) -> Result<Member, Error> {
        let line = self.line();
        if self.eat(Kw::Include) {
            return Ok(Member::Include { theory: self.upper("a theory's name after `include`")?, line });
        }
        let label = self.lower("an axiom's label")?;
        let mut params = Vec::new();
        while let Some(Tok::Upper(_)) = self.peek() {
            params.push(self.upper("")?);
        }
        self.expect(Sym::Colon, "`:` after the axiom's label")?;
        let formula = self.formula()?;
        Ok(Member::Axiom { label, params, formula, line })
    }

    /// `assume*`, steps, then the line labeled `name`.
    fn block(&mut self, name: &str) -> Result<Block, Error> {
        let mut assumes = Vec::new();
        while self.peek() == Some(&Tok::Kw(Kw::Assume)) {
            let line = self.line();
            self.pos += 1;
            let label = self.lower("the assumption's label")?;
            self.expect(Sym::Colon, "`:` after the assumption's label")?;
            let formula = self.formula()?;
            assumes.push(Assume { label, formula, line });
        }
        let mut steps = Vec::new();
        loop {
            let line = self.line();
            match self.peek() {
                Some(Tok::Kw(Kw::Lemma)) => {
                    self.pos += 1;
                    let lemma = self.lower("the lemma's name")?;
                    let block = self.block(&lemma)?;
                    steps.push(Step::Lemma { name: lemma, block, line });
                }
                Some(Tok::Kw(Kw::Assume)) => return Err(self.err("assumptions come first in a block")),
                _ if self.at_label() => {
                    let l = self.step_line()?;
                    if l.label == name {
                        return Ok(Block { assumes, steps, result: l });
                    }
                    steps.push(Step::Line(l));
                }
                _ if self.at_item_keyword() => {
                    return Err(self.err(format!("the block `{name}` has no result: it ends with the line labeled `{name}`")))
                }
                Some(Tok::Lower(n)) => return Err(self.err(format!("expected a label: `{n}:`"))),
                _ => return Err(self.err("expected a labeled line")),
            }
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

    fn reference(&mut self) -> Result<Ref, Error> {
        match self.peek() {
            Some(Tok::Upper(theory)) if self.peek2() == Some(&Tok::Sym(Sym::Dot)) => {
                let theory = theory.clone();
                self.pos += 2;
                let member = self.lower("a member's label after `.`")?;
                Ok(Ref::Member { theory, member })
            }
            Some(Tok::Lower(_)) => Ok(Ref::Name(self.lower("")?)),
            Some(Tok::Upper(n)) => Err(self.err(format!("`{n}` is capitalized, so it isn't a rule, line or theorem"))),
            _ => Err(self.err("expected a rule, line, theorem or theory member")),
        }
    }

    fn just(&mut self) -> Result<Just, Error> {
        let line = self.line();
        let head = self.reference()?;
        let mut targs = Vec::new();
        let mut args = Vec::new();
        loop {
            match self.peek() {
                // A lowercase name is an argument unless it's the next step's label.
                Some(Tok::Lower(n)) if !self.at_label() => {
                    args.push(Arg::Ident(n.clone(), self.line()));
                    self.pos += 1;
                }
                Some(Tok::Upper(_)) if self.peek2() == Some(&Tok::Sym(Sym::Dot)) => {
                    let l = self.line();
                    args.push(Arg::Ref(self.reference()?, l));
                }
                // Templates for the head come first, as bare names or in parentheses.
                Some(Tok::Upper(n)) if args.is_empty() => {
                    targs.push(TArg::Name(n.clone(), self.line()));
                    self.pos += 1;
                }
                Some(Tok::Sym(Sym::LParen)) => {
                    let l = self.line();
                    self.pos += 1;
                    match self.peek() {
                        Some(Tok::Upper(_)) if self.peek2() == Some(&Tok::Sym(Sym::Dot)) => {
                            let head = self.reference()?;
                            let ts = self.targs()?;
                            self.expect(Sym::RParen, "`)`")?;
                            args.push(Arg::Instance { head, targs: ts, line: l });
                        }
                        Some(Tok::Lower(n)) if crate::check::RULES.contains(&n.as_str()) => {
                            return Err(self.err(format!("one rule per line: give `{n}` a line of its own")));
                        }
                        Some(Tok::Lower(_)) => {
                            // `(thm T1 T2)`: a theorem instance as an argument.
                            let head = self.reference()?;
                            let ts = self.targs()?;
                            self.expect(Sym::RParen, "`)`")?;
                            args.push(Arg::Instance { head, targs: ts, line: l });
                        }
                        _ if args.is_empty() => {
                            let f = self.formula()?;
                            self.expect(Sym::RParen, "`)`")?;
                            targs.push(TArg::Paren(Box::new(f)));
                        }
                        _ => return Err(self.err("templates come right after the rule, before the lines")),
                    }
                }
                _ => break,
            }
        }
        Ok(Just { head, targs, args, line })
    }

    /// Templates after a theory member or theorem, inside an instance.
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
                Some(Tok::Sym(Sym::LParen)) => {
                    self.pos += 1;
                    let f = self.formula()?;
                    self.expect(Sym::RParen, "`)`")?;
                    out.push(TArg::Paren(Box::new(f)));
                }
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
                    return Err(self.err(format!("`{name}.` names a theory member, which belongs after `by`, not in a formula")));
                }
                Ok(FExpr::Atom { name, args, line })
            }
            Some(Tok::Sym(Sym::LParen)) => {
                self.pos += 1;
                let f = self.formula()?;
                self.expect(Sym::RParen, "`)`")?;
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
        let items = parsed("define Iff A B = (A -> B) and (B -> A)\ntheory T\n  include S\n  ax: forall x. P x\n  ind P: P -> forall x. P x\ntheorem t in T S\n  assume a: A\n  t: A -> A by imp_i a a");
        assert!(matches!(&items[0], Item::Define { params, .. } if params == &["A", "B"]));
        let Item::Theory { members, .. } = &items[1] else { panic!() };
        assert!(matches!(&members[0], Member::Include { theory, .. } if theory == "S"));
        assert!(matches!(&members[2], Member::Axiom { params, .. } if params == &["P"]));
        let Item::Theorem { theories, block, .. } = &items[2] else { panic!() };
        assert_eq!(theories, &["T", "S"]);
        assert_eq!(block.assumes.len(), 1);

        assert_eq!(block.result.label, "t");
    }

    #[test]
    fn blocks_and_justifications() {
        let src = "theorem t\n assume h: A or B\n lemma l\n  assume a: A\n  r: B or A by or_i2 a\n  l: A -> B or A by imp_i a r\n \
                   k: B by forall_e PA.pz w x\n m: C by imp_e (PA.ind ZeroLeft) k l\n n: D by f (Unicorn) u h\n t: A by n";
        let items = parsed(src);
        let Item::Theorem { block, .. } = &items[0] else { panic!() };
        assert_eq!(block.steps.len(), 4);
        let Step::Lemma { name, block: inner, .. } = &block.steps[0] else { panic!() };
        assert_eq!(name, "l");
        assert_eq!(inner.steps.len(), 1);
        let Step::Line(k) = &block.steps[1] else { panic!() };
        assert!(matches!(&k.just.args[0], Arg::Ref(Ref::Member { theory, member }, _) if theory == "PA" && member == "pz"));
        assert_eq!(k.just.args.len(), 3);
        let Step::Line(m) = &block.steps[2] else { panic!() };
        assert!(matches!(&m.just.args[0], Arg::Instance { targs, .. } if targs.len() == 1));
        let Step::Line(n) = &block.steps[3] else { panic!() };
        assert_eq!(n.just.targs.len(), 1);
        assert_eq!(n.just.args.len(), 2);
    }

    #[test]
    fn errors() {
        let e = parse(&lex("theorem t\n a: A by x\n assume b: B").unwrap()).unwrap_err();
        assert_eq!((e.line, e.msg.as_str()), (3, "assumptions come first in a block"));
        let e = parse(&lex("theorem t\n a: A by x\ntheorem u").unwrap()).unwrap_err();
        assert_eq!(e.msg, "the block `t` has no result: it ends with the line labeled `t`");
        let e = parse(&lex("define X = x").unwrap()).unwrap_err();
        assert_eq!(e.msg, "`x` is lowercase, so it isn't a statement or predicate");
        let e = parse(&lex("define X\nimport a").unwrap()).unwrap_err();
        assert!(e.msg.contains("expected `=`"));
    }

    #[test]
    fn whitespace_independent() {
        let a = parsed("theorem t assume a: A t: A by a");
        let b = parsed("theorem t\n  assume a:\n    A\n  t:\n    A\n      by a");
        assert_eq!(format!("{a:?}").replace(char::is_numeric, ""), format!("{b:?}").replace(char::is_numeric, ""));
    }
}
