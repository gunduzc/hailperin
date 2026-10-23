# hailperin spec

## Logic

Universally free (Hailperin-style) intuitionistic first-order logic.

- One domain, which may be empty. Nothing is assumed to exist; "something exists" is a hypothesis.
- No sorts, no constants, no function symbols, no built-in equality. Terms are variables only.
  Names of individuals are predicates (`Socrates x`); functions are relations (`Succ x y`).
- Theorems are closed formulas. Modus ponens is the only rule.
- Classical reasoning is a hypothesis: `let EM A = or A (not A)`, then `given em : EM P`.

### Formulas

```
absurd
P x1 ... xn                   predicate applied to variables
and A B ...  or A B ...  imp A B ...    (variadic, nested to the right)
not A                         means  imp A absurd
forall x A   exists x A
```

Formulas are compared up to alpha-equivalence. Substitution never captures.

### Axioms

Every closure (a `forall` prefix covering the free variables; extra `forall`s allowed, any order)
of an instance of:

| name | instance | condition |
|---|---|---|
| `imp1` | `imp A B A` | |
| `imp2` | `imp (imp A B C) (imp A B) A C` | |
| `and_i` | `imp A B (and A B)` | |
| `and_e1`, `and_e2` | `imp (and A B) A`, `imp (and A B) B` | |
| `or_i1`, `or_i2` | `imp A (or A B)`, `imp B (or A B)` | |
| `or_e` | `imp (imp A C) (imp B C) (or A B) C` | |
| `efq` | `imp absurd A` | |
| `dist` | `imp (forall x $ imp A B) (forall x A) (forall x B)` | |
| `vac` | `imp A (forall x A)` | `x` not free in `A` |
| `inst` | `imp (forall x A) A[y/x]` | the closure binds `y`, even if `y` doesn't occur |
| `ex_i` | `imp A[y/x] (exists x A)` | the closure binds `y`, even if `y` doesn't occur |
| `ex_e` | `imp (forall x $ imp A C) (exists x A) C` | `x` not free in `C` |

## Language

A file is its imports, then a sequence of `let`s and `proof`s, checked in order. A name is
either a parameter or something defined earlier. Whitespace only separates tokens.

```
import pa                            pa.hai, next to this file
let Succ x y                         primitive predicate (asserts nothing)
let Three x = exists a $ ...         definition
let Induction (P x) = ...            (P x) gives a predicate parameter its arity

proof name
  given A                            statement parameter
  given P x                          predicate parameter (arity 1)
  given h : FORMULA                  hypothesis
  given all SET                      every `given` of a set of hypotheses
  have n : FORMULA by EXPR           step; the formula is optional
  shows FORMULA by EXPR              conclusion, last
```

- **Names:** uppercase = statements and predicates; lowercase = individuals, evidence, proofs.
- **Expressions:** application by juxtaposition. `f $ x y` is `f (x y)`.
  `e |> f _ y` is `f e y`, with exactly one `_`.
- **Evidence:** applying evidence for `imp A B` to evidence for `A` is modus ponens; applying
  evidence for `forall x $ A x` to a block variable `y` gives `A y`.
- **Blocks:** `forall x y { ... }` (arbitrary individuals), `assume h : A { ... }` (gives
  `imp A ...`), `obtain x h from e { ... }` (uses `e : exists x $ A x`; the result can't mention
  `x`). Binders can be chained before one block: `forall x assume h : A forall y { ... }` is
  `forall x { assume h : A { forall y { ... } } }`. A block is a bare expression, or `have`
  steps followed by `shows [FORMULA] by EXPR`.
  Blocks are translated into closed kernel steps; the kernel never sees them. Proofs can't
  be applied to evidence that depends on an `assume` or `obtain`.
- **Axioms** get their letters from formula arguments (`imp1 A B`), from the evidence they are
  applied to (`and_e1 ab`), or from the step's stated formula (`have k : ... by imp1`); the last
  is the only way to get a `forall` prefix.
- **Proofs** are called like functions: predicate arguments first (inferred from the evidence
  when they are applied to distinct bound variables), then evidence. A proof is checked once;
  calls check only its signature. Proofs are second-class: never passed or returned.
- **Templates:** a predicate argument is a name, possibly with leading arguments filled in
  (`LessThan y`). Free individual names in templates are closed with `forall`.
- **Axiom schemas** of a theory (induction, separation, excluded middle, ...) are not hypotheses.
  A proof takes the instances it uses (`given ind : Induction ZeroLeft`); a proof over a
  predicate `P` takes `given ind : Induction P`, and each caller supplies its instance. A
  proof uses finitely many instances, so nothing provable is lost. Statements about a whole
  theory need arithmetization. `Induction` and `ind` are conventions from the examples, not
  rules: `Induction` is an ordinary `let`, and `ind` an ordinary hypothesis.
- **Hypothesis sets:** `let PA = given ... given ...` names a list of `given`s and asserts nothing.
  `given all PA`, in a proof or in another set, stands for all of them. `p PA` passes the
  caller's parameters and hypotheses that `p` got from `PA` (directly or through nested sets),
  by name; the rest are passed as usual. Sets are expanded before checking; the kernel never
  sees them.
- **Imports** come first. `import pa` checks `pa.hai` from the same directory and makes
  everything it defines available, as if pasted in. Each file is pasted once, however often
  it is imported, and a file can't import itself, even through others. Imported names share
  one namespace, so a clash is an error. Since nothing at top level asserts anything, an
  import can't add assumptions: every proof still states its own hypotheses.
- **Comments:** `{- ... -}`, nestable.
