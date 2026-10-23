use crate::lexer::{Kw, Sym, Tok, Token};
use crate::Error;

/// An expression: names, holes, applications and blocks. `$` and `|>` are gone after parsing.
#[derive(Clone, Debug)]
pub enum Expr {
    Name(String, usize),
    Hole(usize),
    App(Box<Expr>, Vec<Expr>),
    /// `forall x y { … }`: inside, the variables are arbitrary individuals.
    Forall { vars: Vec<String>, body: Block, line: usize },
    /// `assume h : A { … }`: inside, `h` is evidence for `A`.
    Assume { name: String, hyp: Box<Expr>, body: Block, line: usize },
    /// `obtain x h from e { … }`: `e` proves `exists x $ A x`; inside, `h` proves `A x`.
    Obtain { var: String, name: String, from: Box<Expr>, body: Block, line: usize },
}

enum Binder {
    Forall(Vec<String>),
    Assume(String, Expr),
    Obtain(String, String, Expr),
}

/// Steps, then the block's result: `shows [FORMULA] by EXPR`, or a bare expression when
/// there are no steps.
#[derive(Clone, Debug)]
pub struct Block {
    pub steps: Vec<Step>,
    pub stmt: Option<Box<Expr>>,
    pub result: Box<Expr>,
}

/// `have NAME : FORMULA by EXPR`; the formula is optional.
#[derive(Clone, Debug)]
pub struct Step {
    pub name: String,
    pub stmt: Option<Expr>,
    pub by: Expr,
    pub line: usize,
}

impl Expr {
    pub fn line(&self) -> usize {
        match self {
            Expr::Name(_, l) | Expr::Hole(l) => *l,
            Expr::App(h, _) => h.line(),
            Expr::Forall { line, .. } | Expr::Assume { line, .. } | Expr::Obtain { line, .. } => *line,
        }
    }

    /// The head and all arguments, flattening nested applications.
    pub fn spine(&self) -> (&Expr, Vec<&Expr>) {
        match self {
            Expr::App(h, args) => {
                let (head, mut all) = h.spine();
                all.extend(args.iter());
                (head, all)
            }
            _ => (self, Vec::new()),
        }
    }
}

/// Expressions print as written, with `$` before a final argument that is an application.
impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let atom = |e: &Expr, f: &mut std::fmt::Formatter| match e {
            Expr::Name(..) | Expr::Hole(_) => write!(f, "{e}"),
            _ => write!(f, "({e})"),
        };
        match self {
            Expr::Name(n, _) => write!(f, "{n}"),
            Expr::Hole(_) => write!(f, "_"),
            Expr::App(..) => {
                let (head, args) = self.spine();
                atom(head, f)?;
                for (i, a) in args.iter().enumerate() {
                    if i + 1 == args.len() && matches!(a, Expr::App(..)) {
                        write!(f, " $ {a}")?;
                    } else {
                        write!(f, " ")?;
                        atom(a, f)?;
                    }
                }
                Ok(())
            }
            Expr::Forall { .. } | Expr::Assume { .. } | Expr::Obtain { .. } => write!(f, "{{ … }}"),
        }
    }
}

/// A parameter of a `let`: `P`, or `(P x y)` to give its arity.
#[derive(Clone, Debug)]
pub struct ParamDecl {
    pub name: String,
    pub arity: Option<usize>,
    pub line: usize,
}

#[derive(Clone, Debug)]
pub enum Item {
    Let { name: String, params: Vec<ParamDecl>, body: Option<Expr>, line: usize },
    /// `let NAME = given … given …`: a named set of premises.
    Set { name: String, parts: Vec<Part>, line: usize },
    Proof { name: String, parts: Vec<Part>, line: usize },
}

#[derive(Clone, Debug)]
pub enum Part {
    Param { name: String, arity: usize, line: usize },
    /// `given all SET`: every `given` of a set of premises.
    All { set: String, line: usize },
    Premise { name: String, stmt: Expr, line: usize },
    Have(Step),
    Shows { stmt: Expr, by: Expr, line: usize },
}

/// `import NAME`: the file `NAME.hai` next to this one.
#[derive(Clone, Debug)]
pub struct Import {
    pub name: String,
    pub line: usize,
}

/// A file: its imports, which come first, then its items.
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
        imports.push(Import { name: p.name()?, line });
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

impl Parser<'_> {
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos).map(|t| &t.tok)
    }

    fn line(&self) -> usize {
        self.toks.get(self.pos).or(self.toks.last()).map_or(1, |t| t.line)
    }

    fn err(&self, msg: impl Into<String>) -> Error {
        Error::new(self.line(), msg)
    }

    fn eat(&mut self, s: Sym) -> bool {
        if self.peek() == Some(&Tok::Sym(s)) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn expect(&mut self, s: Sym, what: &str) -> Result<(), Error> {
        if self.eat(s) {
            Ok(())
        } else {
            Err(self.err(format!("expected {what}")))
        }
    }

    fn expect_kw(&mut self, k: Kw, what: &str) -> Result<(), Error> {
        if self.peek() == Some(&Tok::Kw(k)) {
            self.pos += 1;
            Ok(())
        } else {
            Err(self.err(format!("expected {what}")))
        }
    }

    fn name(&mut self) -> Result<String, Error> {
        match self.peek() {
            Some(Tok::Name(n)) => {
                let n = n.clone();
                self.pos += 1;
                Ok(n)
            }
            _ => Err(self.err("expected a name")),
        }
    }

    fn item(&mut self) -> Result<Item, Error> {
        let line = self.line();
        match self.peek() {
            Some(Tok::Kw(Kw::Let)) => {
                self.pos += 1;
                let name = self.name()?;
                let params = self.params(|t| t == &Tok::Sym(Sym::Equals))?;
                if !self.eat(Sym::Equals) {
                    return Ok(Item::Let { name, params, body: None, line });
                }
                if self.peek() == Some(&Tok::Kw(Kw::Given)) {
                    if !params.is_empty() {
                        return Err(Error::new(line, "a set of premises takes no parameters"));
                    }
                    let mut parts = Vec::new();
                    while self.peek() == Some(&Tok::Kw(Kw::Given)) {
                        parts.push(self.part()?);
                    }
                    return Ok(Item::Set { name, parts, line });
                }
                Ok(Item::Let { name, params, body: Some(self.expr()?), line })
            }
            Some(Tok::Kw(Kw::Import)) => Err(self.err("imports must come before everything else")),
            Some(Tok::Kw(Kw::Proof)) => {
                self.pos += 1;
                let name = self.name()?;
                let mut parts = Vec::new();
                while !matches!(self.peek(), None | Some(Tok::Kw(Kw::Let | Kw::Proof | Kw::Import))) {
                    parts.push(self.part()?);
                }
                Ok(Item::Proof { name, parts, line })
            }
            _ => Err(self.err("expected `let` or `proof`")),
        }
    }

    /// Parameters up to a token where `stop` holds or that can't start a parameter.
    fn params(&mut self, stop: impl Fn(&Tok) -> bool) -> Result<Vec<ParamDecl>, Error> {
        let mut params = Vec::new();
        loop {
            let line = self.line();
            match self.peek() {
                Some(t) if stop(t) => break,
                Some(Tok::Name(_)) => params.push(ParamDecl { name: self.name()?, arity: None, line }),
                Some(Tok::Sym(Sym::LParen)) => {
                    self.pos += 1;
                    let name = self.name()?;
                    let mut arity = 0;
                    while matches!(self.peek(), Some(Tok::Name(_))) {
                        self.pos += 1;
                        arity += 1;
                    }
                    self.expect(Sym::RParen, "`)`")?;
                    params.push(ParamDecl { name, arity: Some(arity), line });
                }
                _ => break,
            }
        }
        Ok(params)
    }

    fn part(&mut self) -> Result<Part, Error> {
        let line = self.line();
        match self.peek() {
            Some(Tok::Kw(Kw::Given)) => {
                self.pos += 1;
                if self.peek() == Some(&Tok::Kw(Kw::All)) {
                    self.pos += 1;
                    return Ok(Part::All { set: self.name()?, line });
                }
                let name = self.name()?;
                if self.eat(Sym::Colon) {
                    return Ok(Part::Premise { name, stmt: self.expr()?, line });
                }
                let mut arity = 0;
                while matches!(self.peek(), Some(Tok::Name(_))) {
                    self.pos += 1;
                    arity += 1;
                }
                Ok(Part::Param { name, arity, line })
            }
            Some(Tok::Kw(Kw::Have)) => Ok(Part::Have(self.step()?)),
            Some(Tok::Kw(Kw::Shows)) => {
                self.pos += 1;
                let stmt = self.expr()?;
                self.expect_kw(Kw::By, "`by`")?;
                Ok(Part::Shows { stmt, by: self.expr()?, line })
            }
            _ => Err(self.err("expected `given`, `have` or `shows`")),
        }
    }

    fn step(&mut self) -> Result<Step, Error> {
        let line = self.line();
        self.expect_kw(Kw::Have, "`have`")?;
        let name = self.name()?;
        let stmt = if self.eat(Sym::Colon) { Some(self.expr()?) } else { None };
        self.expect_kw(Kw::By, "`by`")?;
        Ok(Step { name, stmt, by: self.expr()?, line })
    }

    fn block(&mut self) -> Result<Block, Error> {
        self.expect(Sym::LBrace, "`{`")?;
        let mut steps = Vec::new();
        while self.peek() == Some(&Tok::Kw(Kw::Have)) {
            steps.push(self.step()?);
        }
        let mut stmt = None;
        if self.peek() == Some(&Tok::Kw(Kw::Shows)) {
            self.pos += 1;
            if self.peek() != Some(&Tok::Kw(Kw::By)) {
                stmt = Some(Box::new(self.expr()?));
            }
            self.expect_kw(Kw::By, "`by`")?;
        } else if !steps.is_empty() {
            return Err(self.err("after `have` steps, a block ends with `shows … by …`"));
        }
        let result = Box::new(self.expr()?);
        self.expect(Sym::RBrace, "`}`")?;
        Ok(Block { steps, stmt, result })
    }

    /// `forall x y` followed by `{` or another binder starts a block; `forall x $ …` is a
    /// formula.
    fn at_forall_binder(&self) -> bool {
        let is_forall = |t: Option<&Token>| matches!(t.map(|t| &t.tok), Some(Tok::Name(n)) if n == "forall");
        if !is_forall(self.toks.get(self.pos)) {
            return false;
        }
        let mut j = self.pos + 1;
        while matches!(self.toks.get(j).map(|t| &t.tok), Some(Tok::Name(n)) if n != "forall") {
            j += 1;
        }
        j > self.pos + 1
            && (is_forall(self.toks.get(j))
                || matches!(
                    self.toks.get(j).map(|t| &t.tok),
                    Some(Tok::Sym(Sym::LBrace) | Tok::Kw(Kw::Assume | Kw::Obtain))
                ))
    }

    fn at_binder(&self) -> bool {
        self.at_forall_binder() || matches!(self.peek(), Some(Tok::Kw(Kw::Assume | Kw::Obtain)))
    }

    /// One or more binders, then one block: `forall x assume h : A forall y { … }` is the
    /// same as `forall x { assume h : A { forall y { … } } }`.
    fn binder_chain(&mut self) -> Result<Expr, Error> {
        let mut binders = Vec::new();
        while self.at_binder() {
            let line = self.line();
            match self.peek() {
                Some(Tok::Kw(Kw::Assume)) => {
                    self.pos += 1;
                    let name = self.name()?;
                    self.expect(Sym::Colon, "`:`")?;
                    let hyp = self.expr()?;
                    binders.push((line, Binder::Assume(name, hyp)));
                }
                Some(Tok::Kw(Kw::Obtain)) => {
                    self.pos += 1;
                    let var = self.name()?;
                    let name = self.name()?;
                    self.expect_kw(Kw::From, "`from`")?;
                    let from = self.expr()?;
                    binders.push((line, Binder::Obtain(var, name, from)));
                }
                _ => {
                    self.pos += 1;
                    let mut vars = Vec::new();
                    while matches!(self.peek(), Some(Tok::Name(n)) if n != "forall") {
                        vars.push(self.name()?);
                    }
                    binders.push((line, Binder::Forall(vars)));
                }
            }
        }
        let wrap = |(line, b): (usize, Binder), body: Block| match b {
            Binder::Forall(vars) => Expr::Forall { vars, body, line },
            Binder::Assume(name, hyp) => Expr::Assume { name, hyp: Box::new(hyp), body, line },
            Binder::Obtain(var, name, from) => Expr::Obtain { var, name, from: Box::new(from), body, line },
        };
        let mut rest = binders.into_iter().rev();
        let mut expr = wrap(rest.next().expect("a chain has at least one binder"), self.block()?);
        for b in rest {
            expr = wrap(b, Block { steps: Vec::new(), stmt: None, result: Box::new(expr) });
        }
        Ok(expr)
    }

    /// expr := dollar ("|>" dollar)*
    fn expr(&mut self) -> Result<Expr, Error> {
        let mut e = self.dollar()?;
        while self.eat(Sym::Pipe) {
            let line = self.line();
            let rhs = self.dollar()?;
            let (plugged, holes) = plug(rhs, &e);
            if holes != 1 {
                return Err(Error::new(line, format!("the right side of `|>` needs exactly one `_`, found {holes}")));
            }
            e = plugged;
        }
        Ok(e)
    }

    /// dollar := app ("$" dollar)?
    fn dollar(&mut self) -> Result<Expr, Error> {
        let app = self.app()?;
        if self.eat(Sym::Dollar) {
            let rest = self.dollar()?;
            return Ok(match app {
                Expr::App(h, mut args) => {
                    args.push(rest);
                    Expr::App(h, args)
                }
                head => Expr::App(Box::new(head), vec![rest]),
            });
        }
        Ok(app)
    }

    /// app := atom atom*
    fn app(&mut self) -> Result<Expr, Error> {
        let head = self.atom()?;
        let mut args = Vec::new();
        // `forall` is only ever a head, so an argument list stops there: that's where the next
        // binder of a chain begins.
        while matches!(self.peek(), Some(Tok::Name(n)) if n != "forall")
            || matches!(self.peek(), Some(Tok::Sym(Sym::Hole | Sym::LParen)))
        {
            args.push(self.atom()?);
        }
        Ok(if args.is_empty() { head } else { Expr::App(Box::new(head), args) })
    }

    fn atom(&mut self) -> Result<Expr, Error> {
        let line = self.line();
        if self.at_binder() {
            return self.binder_chain();
        }
        match self.peek() {
            Some(Tok::Name(_)) => Ok(Expr::Name(self.name()?, line)),
            Some(Tok::Sym(Sym::Hole)) => {
                self.pos += 1;
                Ok(Expr::Hole(line))
            }
            Some(Tok::Sym(Sym::LParen)) => {
                self.pos += 1;
                let e = self.expr()?;
                self.expect(Sym::RParen, "`)`")?;
                Ok(e)
            }
            _ => Err(self.err("expected an expression")),
        }
    }
}

/// Replaces every hole in `e` with `with`, returning the result and the number of holes.
fn plug(e: Expr, with: &Expr) -> (Expr, usize) {
    let block = |b: Block, n: &mut usize| {
        let steps = b
            .steps
            .into_iter()
            .map(|s| {
                let stmt = s.stmt.map(|x| {
                    let (x, k) = plug(x, with);
                    *n += k;
                    x
                });
                let (by, k) = plug(s.by, with);
                *n += k;
                Step { stmt, by, ..s }
            })
            .collect();
        let stmt = b.stmt.map(|x| {
            let (x, k) = plug(*x, with);
            *n += k;
            Box::new(x)
        });
        let (result, k) = plug(*b.result, with);
        *n += k;
        Block { steps, stmt, result: Box::new(result) }
    };
    match e {
        Expr::Forall { vars, body, line } => {
            let mut n = 0;
            let body = block(body, &mut n);
            (Expr::Forall { vars, body, line }, n)
        }
        Expr::Assume { name, hyp, body, line } => {
            let (hyp, mut n) = plug(*hyp, with);
            let body = block(body, &mut n);
            (Expr::Assume { name, hyp: Box::new(hyp), body, line }, n)
        }
        Expr::Obtain { var, name, from, body, line } => {
            let (from, mut n) = plug(*from, with);
            let body = block(body, &mut n);
            (Expr::Obtain { var, name, from: Box::new(from), body, line }, n)
        }
        Expr::Hole(_) => (with.clone(), 1),
        Expr::Name(..) => (e, 0),
        Expr::App(h, args) => {
            let (h, mut n) = plug(*h, with);
            let args = args
                .into_iter()
                .map(|a| {
                    let (a, k) = plug(a, with);
                    n += k;
                    a
                })
                .collect();
            (Expr::App(Box::new(h), args), n)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::lex;

    fn show(e: &Expr) -> String {
        match e {
            Expr::Name(n, _) => n.clone(),
            Expr::Hole(_) => "_".into(),
            Expr::App(h, args) => {
                let args: Vec<String> = args.iter().map(show).collect();
                format!("({} {})", show(h), args.join(" "))
            }
            _ => "{block}".into(),
        }
    }

    fn expr(src: &str) -> String {
        let items = parse(&lex(&format!("let X = {src}")).unwrap()).unwrap().items;
        let Item::Let { body: Some(b), .. } = &items[0] else { panic!() };
        show(b)
    }

    #[test]
    fn dollar_and_pipe() {
        assert_eq!(expr("forall x $ imp A $ imp B C"), "(forall x (imp A (imp B C)))");
        assert_eq!(expr("or A B |> imp _ absurd"), "(imp (or A B) absurd)");
        assert_eq!(expr("A |> f _ |> g _ x"), "(g (f A) x)");
    }

    #[test]
    fn pipe_needs_one_hole() {
        let e = parse(&lex("let X = A |> f B").unwrap()).unwrap_err();
        assert_eq!(e.msg, "the right side of `|>` needs exactly one `_`, found 0");
    }

    #[test]
    fn items_and_parts() {
        let src = "let Succ x y\nlet Ind (P x) = P\nproof p given A given P x given h : A \
                   have k : A by h shows A by k";
        let items = parse(&lex(src).unwrap()).unwrap().items;
        assert!(matches!(&items[0], Item::Let { params, body: None, .. } if params.len() == 2));
        assert!(matches!(&items[1], Item::Let { params, .. } if params[0].arity == Some(1)));
        let Item::Proof { parts, .. } = &items[2] else { panic!() };
        assert!(matches!(&parts[0], Part::Param { arity: 0, .. }));
        assert!(matches!(&parts[1], Part::Param { arity: 1, .. }));
        assert!(matches!(&parts[2], Part::Premise { .. }));
        assert!(matches!(&parts[3], Part::Have(Step { stmt: Some(_), .. })));
        assert!(matches!(&parts[4], Part::Shows { .. }));
    }

    #[test]
    fn blocks() {
        let src = "proof p shows A by forall x y { have a by h x shows by trans a b } \
                   proof q shows A by assume h : A { obtain x k from e { k } }";
        let items = parse(&lex(src).unwrap()).unwrap().items;
        let Item::Proof { parts, .. } = &items[0] else { panic!() };
        let Part::Shows { by: Expr::Forall { vars, body, .. }, .. } = &parts[0] else { panic!() };
        assert_eq!(vars, &["x", "y"]);
        assert_eq!(body.steps.len(), 1);
        let Item::Proof { parts, .. } = &items[1] else { panic!() };
        let Part::Shows { by: Expr::Assume { body, .. }, .. } = &parts[0] else { panic!() };
        assert!(matches!(&*body.result, Expr::Obtain { var, .. } if var == "x"));
        // `forall x $ …` is still a formula.
        assert_eq!(expr("forall x $ A"), "(forall x A)");
        // A chain of binders is the same as nested blocks.
        let chained = parse(&lex("proof p shows A by forall x assume h : P x forall y z { h }").unwrap()).unwrap().items;
        let nested = parse(&lex("proof p shows A by forall x { assume h : P x { forall y z { h } } }").unwrap()).unwrap().items;
        assert_eq!(format!("{chained:?}"), format!("{nested:?}"));
    }

    #[test]
    fn premise_sets() {
        let items = parse(&lex("let S = given A given a : A let T = given all S proof p given all T shows A by a").unwrap()).unwrap().items;
        assert!(matches!(&items[0], Item::Set { parts, .. } if parts.len() == 2));
        assert!(matches!(&items[1], Item::Set { parts, .. } if matches!(&parts[0], Part::All { set, .. } if set == "S")));
        assert!(matches!(&items[2], Item::Proof { parts, .. } if matches!(&parts[0], Part::All { .. })));
    }

    #[test]
    fn imports_come_first() {
        let f = parse(&lex("import a import b let X").unwrap()).unwrap();
        assert_eq!(f.imports.iter().map(|i| i.name.as_str()).collect::<Vec<_>>(), ["a", "b"]);
        assert_eq!(f.items.len(), 1);
        let e = parse(&lex("let X\nimport a").unwrap()).unwrap_err();
        assert_eq!((e.line, e.msg.as_str()), (2, "imports must come before everything else"));
    }

    #[test]
    fn whitespace_independent() {
        let a = parse(&lex("proof p given A shows A by x").unwrap()).unwrap().items;
        let b = parse(&lex("proof p\n  given A\n  shows A\n    by x").unwrap()).unwrap().items;
        assert_eq!(format!("{a:?}").replace(char::is_numeric, ""), format!("{b:?}").replace(char::is_numeric, ""));
    }
}
