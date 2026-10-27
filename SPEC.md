# hailperin spec

## Logic

Universally free (Hailperin-style) intuitionistic first-order logic.

- One domain, possibly empty.
- Terms are variables. No sorts, no built-in equality. Individuals are predicates (`Socrates x`), functions are relations (`Succ x y`).
- Theorems are closed formulas, and logical validities: whatever a theorem assumes, axioms included, is in its statement. Modus ponens is the only rule.
- Classical logic is a schema, `define ExcludedMiddle A = A or not A`, assumed one instance at a time. Non-emptiness is a formula: `not (forall x. absurd)`.

### Formulas

```
absurd
P x1 ... xn                   predicate applied to variables
not A                         means  A -> absurd
A and B    A or B    A -> B   infix. `->` is right-associative, `and` and `or` nest to the right
forall x y. A    exists x y. A   the body extends as far right as it can
```

Precedence, tightest first: `not`, `and`, `or`, `->`. Formulas are equal up to renaming of bound variables. Substitution never captures.

### Axioms

Every closure (a `forall` prefix over the free variables, extra `forall`s allowed, in any order) of an instance of:

| name | instance | condition |
|---|---|---|
| `imp1` | `A -> B -> A` | |
| `imp2` | `(A -> B -> C) -> (A -> B) -> A -> C` | |
| `and_i` | `A -> B -> A and B` | |
| `and_e1`, `and_e2` | `A and B -> A`, `A and B -> B` | |
| `or_i1`, `or_i2` | `A -> A or B`, `B -> A or B` | |
| `or_e` | `(A -> C) -> (B -> C) -> A or B -> C` | |
| `efq` | `absurd -> A` | |
| `dist` | `(forall x. A -> B) -> (forall x. A) -> forall x. B` | |
| `vac` | `A -> forall x. A` | `x` not free in `A` |
| `inst` | `(forall x. A) -> A[y/x]` | the closure binds `y`, even if `y` doesn't occur |
| `ex_i` | `A[y/x] -> exists x. A` | the closure binds `y`, even if `y` doesn't occur |
| `ex_e` | `(forall x. A -> C) -> (exists x. A) -> C` | `x` not free in `C` |

These fourteen and modus ponens are the kernel. Everything below is translated into them.

## Language

A file is ASCII. Whitespace only separates tokens. A comment runs from `--` to the end of its line, and belongs to the item after it, or to the line it trails. Everything is declared before it is used, and no name is ever two things at once. Nothing shadows: a quantifier binds a name that is new where it stands, not a variable in scope, a binder around it, a definition's parameter, a label (the line's own included) or a theorem. A `therefore` restates the variables its block closes, which is not shadowing: `variable a` ... `therefore forall a. P a -> P a`.

**Names.** Uppercase: predicates, definitions, parameters. Lowercase: variables, labels, theorems, lemmas, rules. A name matches `letter (letter | digit | '_' (letter | digit))*`. Reserved: `theorem lemma define import predicate variable assume therefore by forall exists and or not absurd`, and the rule names, `auto` among them.

```
file      ::= import* item*
import    ::= 'import' path
path      ::= part ('/' part)*                    one token, no spaces
part      ::= name | '.' | '..'
item      ::= predicate | define | theorem

predicate ::= 'predicate' Name var*
define    ::= 'define' Name param* '=' formula
param     ::= '(' Name var+ ')' | Name | var
theorem   ::= 'theorem' name ':' predicate* block
lemma     ::= 'lemma' name ':' block

block     ::= ('variable' var+)*
              ('assume' label ':' formula)*
              (line | lemma)*
              'therefore' formula
line      ::= label ':' formula 'by' just

just      ::= rule arg*                           a rule from the table, then lines and variables
arg       ::= name template*                      a line, a variable, or a theorem with its templates
template  ::= Name | '(' formula ')'              in parentheses, anything but a lone Name

formula   ::= disj ['->' formula]
disj      ::= conj ('or' conj)*
conj      ::= neg ('and' neg)*
neg       ::= 'not' neg | quant | atom
quant     ::= ('forall' | 'exists') var+ '.' formula
atom      ::= 'absurd' | Name targ* | '(' formula ')'
targ      ::= var | Name | '(' formula ')'        in parentheses, anything but a lone Name
```

A quantifier's body reaches as far right as it can: `A and forall x. P x -> B` is `A and (forall x. (P x -> B))`.

The grammar is LL(2): after a justification's arguments, a lowercase name is the next label or one more argument, and the `:` after it decides.

### Declarations

```
predicate In x y
predicate Rain
```

A predicate is declared once, at file level, before any use. The lowercase placeholders fix its arity, and nothing else does. A capitalized name nothing declares or defines is an error, and the error says what to declare.

### Definitions

```
define Iff A B = (A -> B) and (B -> A)
define Eq x y = forall z. Iff (In z x) (In z y)
define Induction (P x) = (forall x. Zero x -> P x) -> (forall y x. P x -> Succ x y -> P y) -> forall x. P x
```

A definition names a formula and asserts nothing. A parameter in parentheses is a predicate, with placeholders fixing its arity: `(P x)`. An uppercase parameter alone is a statement: `A`. A lowercase parameter is an individual. Definitions unfold and fold silently wherever a rule needs it, and messages print an instance of a definition over individuals by its name. Applied to fewer individuals than it takes, a definition is a template: `EqOr A e` is the predicate `z |-> Eq z e or A`.

### Axioms and schemas

```
define Pz = forall x z. Zero z -> Plus x z x
define Ps = forall x y s p q. Succ y s -> Plus x y p -> Succ p q -> Plus x s q
...
define Q = Sz and Si and Pred and Pz and Ps and ...

define Induction (P x) = (forall x. Zero x -> P x) -> (forall y x. P x -> Succ x y -> P y) -> forall x. P x
```

There are no theories. An axiom is a definition, and a finitely axiomatized theory is the conjunction of its axioms, `Q`. A schema is a definition with a predicate parameter, `Induction`, and its instances are formulas, `Induction ZeroLeft`. Nothing at top level asserts anything.

A theorem assumes what it uses, like any other assumption, and its `therefore` discharges it:

```
theorem zero_left:
  assume ax:  Q
  assume ind: Induction ZeroLeft
  pz: Pz                                  by and_e ax
  ...
  therefore Q -> Induction ZeroLeft -> forall x. ZeroLeft x
```

`and_e` takes an axiom out of the conjunction by name. A theory that is not finitely axiomatizable, PA or ZF, has no single formula, so a theorem of PA assumes Q and the instances of induction it uses, which is all a proof in PA ever uses. An instance that mentions a variable of a lemma is assumed closed over it, `assume sep: forall e. Separation (EqOr A e)`, and instantiated where it is used, `forall_e sep e u`. A citation supplies the cited theorem's assumptions like any antecedent: `imp_e zero_left ax ind zx`.

A schema is sound when its parameter may be any formula (induction, separation, excluded middle). When it may not (Sigma_1 induction, naive comprehension, the truth schema), mind which instances you assume, or arithmetize. The checker cannot tell.

### Theorems and lemmas

```
predicate Socrates x
predicate Person x
predicate Mortal x

theorem socrates_is_mortal:
  assume sp: forall x. Socrates x -> Person x
  assume pm: forall x. Person x -> Mortal x
  lemma sm:
    variable x
    assume s: Socrates x
    p: Person x                           by imp_e sp s
    m: Mortal x                           by imp_e pm p
    therefore forall x. Socrates x -> Mortal x
  therefore (forall x. Socrates x -> Person x)
              -> (forall x. Person x -> Mortal x)
              -> forall x. Socrates x -> Mortal x
```

A theorem and a lemma are the same construct, a block. Its name is followed by a colon, like every name that can be cited: labels, assumptions, lemmas and theorems. A theorem is a block at top level, and its `therefore` is a closed formula. A lemma is a block inside a block, and its `therefore` may rest on the variables, assumptions and lines of the blocks around it, which stay open on its result. A lemma's name is visible after it, in the block that contains it, and nowhere else.

**Declarations first, in order.** A block opens with its `predicate` lines, then `variable`, then `assume`, each section possibly empty, then its steps and lemmas, then `therefore`. Read in order: what the theorem is about, for which individuals, given what. The header says everything a theorem rests on, and so does its statement.

- `predicate P x` declares a predicate the theorem is schematic over, its arity fixed by the placeholders: the theorem holds for every predicate of that arity, and a citation picks one. It is the same declaration as at file level, with the theorem for its scope, and the same thing as a definition's `(P x)`. Only theorems declare predicates, and their lemmas use them.
- `variable x y` opens one layer per name, outermost first. A variable occurs free only inside a block whose `variable` named it. Nothing after `by` brings a variable into scope.
- `assume h: A` opens an assumption layer.

**Lines.** A line stands for its closure: the stated formula under an implication for each open assumption it rests on and a `forall` for each variable in scope. The kernel holds the closure. Quine and Hailperin write `|- A` for this: the closure of `A` is a theorem.

**`therefore F`.** The closing line of every block, and the rule that introduces `->` and `forall`. `F` must be the line right above it, a step, a lemma or an assumption, closed over everything the block opened, innermost first: an implication for each `assume`, a `forall` for each `variable`, in declaration order. The checker verifies the closure. A line that does not rest on some declaration is weakened under it, so a block may close a variable the line never used. To close an earlier line, or one from a block around this one, bring it down with `reit` first.

**Scope ends with the block.** After `therefore`, the block's variables, assumptions and labels are gone. No name is ever reused while another of the same name is in scope: not a variable for a label, not a label for a variable, not a placeholder for a name in scope, not a theorem's name for either. The order of layers is the order of declaration, and a different order is a different nesting.

**Rules.** Every justification starts with a rule. A fact, meaning a line, a theorem or a theorem's instance, is applied with `imp_e` and restated with `reit`, and never cited bare. Several arguments of one kind mean the rule applied once per argument, in order.

| rule | from | gives |
|---|---|---|
| `imp_e f a...` | a fact `f : A -> B -> ...`, `a : A`, ... | what is left after the antecedents given. Each run of `forall`s of `f` is instantiated by matching the lines after it, and the stated formula |
| `and_i a b...` | `A`, `B`, ... | `A and B and ...`, nested to the right like the formula |
| `and_e c` | `A and B and ...`, stated as one of its conjuncts | that conjunct. The stated formula says which |
| `or_i a` | `A`, stated as an `or` with `A` among its alternatives | the stated `or`. The stated formula says where |
| `or_e d p q...` | `A or B or ...`, `A -> C`, `B -> C`, ... | `C`. One case per alternative, the last case taking what is left |
| `absurd_e f` | `absurd` | the stated formula |
| `forall_e h y...` | `forall x.... A`, `y...` in scope | `A[y/x]...` |
| `exists_i l` | `A[y/x]...`, stated as `exists x.... A`, for some `y...` in scope | `exists x.... A`. The witnesses are found by comparing the two, as many binders as the line accounts for |
| `exists_e e g` | `e : exists x.... A`, `g : forall w.... A[w/x] -> C`, no `w` free in `C` | `C`. `g` is usually a lemma's `therefore`, one `variable` per binder |
| `reit f` | a fact `f : F` | `F` restated: bound names renamed, definitions folded or unfolded. Nothing is instantiated |
| `auto` | | reserved for a tool that fills lines in. The checker refuses it |

Every rule takes as much as the formula has. `A and B and C` is `A and (B and C)` and `exists x y. A` is `exists x. exists y. A`, and each rule applies the kernel's binary axiom once per link, so nothing in the kernel changes. A block's `therefore` is the only thing that closes a layer.

A theorem is a fact like a line. Applying a fact with `imp_e` instantiates its `forall`s: each variable takes what the lines after it, or the stated formula, have in its place, and `forall_e` serves the variables neither fixes. With `pz: Pz`, `Plus w w w by imp_e pz zw` finds `z := w` from the line and `x := w` from the stated formula. `imp_e plus_rw ax e p` works for `plus_rw : Q -> forall x y a b. Eq a b -> Plus x y a -> Plus x y b`: `ax` meets `Q`, then the `forall`s are found from `e` and `p`. `not A` is `A -> absurd`, so `imp_e` serves it.

**Predicates at a citation.** A schema's instance is a formula, written out where it is assumed: `Adduction NoSelfSub`, `Separation (EqOr A e)`. A theorem's predicates are passed as templates at every citation, after its name and in declaration order: `by imp_e next_exists T0 t0`. Templates are uppercase and the lines fed after them are lowercase, so the first lowercase name ends them. A template is a predicate or definition applied to its first individuals, leaving as many places as the parameter has, or any formula when the parameter has none: `imp_e diaconescu (Inhabited a) sets`. A predicate is in parentheses exactly when it is given arguments among other names, in a definition's header, at a citation, or inside an instance. A name alone never is.

**Russell**, with the witness box the elimination needs:

```
predicate In x y
define Iff A B = (A -> B) and (B -> A)

theorem russell:
  assume h: exists r. forall x. Iff (In x r) (not (In x x))
  lemma c:
    variable r
    assume hr: forall x. Iff (In x r) (not (In x x))
    rr:  Iff (In r r) (not (In r r))      by forall_e hr r
    fwd: In r r -> not (In r r)           by and_e rr
    bwd: not (In r r) -> In r r           by and_e rr
    lemma nr:
      assume in_rr: In r r
      n: not (In r r)                     by imp_e fwd in_rr
      f: absurd                           by imp_e n in_rr
      therefore not (In r r)
    r1: In r r                            by imp_e bwd nr
    f:  absurd                            by imp_e nr r1
    therefore forall r. not (forall x. Iff (In x r) (not (In x x)))
  k: absurd                               by exists_e h c
  therefore not (exists r. forall x. Iff (In x r) (not (In x x)))
```

### Imports

`import pa` checks `pa.hai` from the same directory, once, however often it is imported. A file sees the names of the files it imports, of theirs, and its own, and nothing else, so it means the same whoever imports it. A path is relative to the importing file, with `/` between its parts, and `.` and `..` mean what they always mean: `import fs0/syntax`, `import ../pa`. Absolute paths and wildcards are errors. A file reached by two paths is the same file, checked once. Paths only find files: every name lives in one namespace, so cycles and name clashes are errors, even between files that don't see each other. Nothing at top level asserts anything, so an import adds no assumptions.

### Formatting

`hailperin fmt FILE` prints the file in its canonical layout: one item per line, one indentation level per block, `by` in one column per segment, `=` in one column per run of definitions, a blank line between top-level items, comments where they were. The source's line breaks and blank lines are kept and its spacing is forgotten: a continued line is indented a fixed amount past its item, and a `by` that starts a line stands in its segment's column. Nothing is broken unless a width is given, and then a longer line breaks before its `by`, then before an operator, the outermost first. A segment is a run of steps in one block with no lemma between them, so the steps before a lemma, the lemma's own and the steps after it align separately. A `therefore` has no `by`, so it takes no part in the columns. A run of definitions ends at a blank line. The flags are `--indent N`, `--continue N`, `--width N`, `--by pad|space` for both columns, and `--scope segment|theorem`, and each person formats their own way.

`hailperin explain FILE` prints each line's scope and formula.
