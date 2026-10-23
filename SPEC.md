# hailperin spec

## Logic

Inclusive (Hailperin-style) first-order logic, intuitionistic by default.

- One domain, which may be empty. Nothing is assumed to exist; "something exists" is a premise.
- No sorts, no constants, no function symbols, no built-in equality. Terms are variables only.
  Names of individuals are predicates (`Socrates x`); functions are relations (`Succ x y`).
- Theorems are closed formulas. Modus ponens is the only rule.
- Classical reasoning is a premise: `let EM A = or A (not A)`, then `given em : EM P`.

### Formulas

```
absurd
P x₁ … xₙ                     predicate applied to variables
and A B …    or A B …    imp A B …      (variadic, nested to the right)
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

### Semantics

A **Kripke model** is a partial order of worlds. Each world `w` has a domain `D(w)`, which may
be empty, and each predicate of arity n a set `P(w)` of n-tuples from `D(w)`; both only grow
along the order. A world forces a formula, given values in `D(w)` for its free variables:

- `absurd` never; `P x̄` when the values of `x̄` are in `P(w)`; `and` and `or` as usual;
- `imp A B` when every later world (`w` included) that forces `A` forces `B`;
- `forall x A` when every later world forces `A` for every element of its domain as `x`;
- `exists x A` when `w` forces `A` for some element of `D(w)` as `x`.

A theorem from premises `Γ` (closed formulas) **holds** if every world of every model that
forces all of `Γ` forces the theorem. Classical models are the one-world Kripke models.
Forcing persists: what a world forces, every later world forces.

### Soundness

Every theorem the kernel produces holds. The kernel sees only expanded closed formulas
(definitions, sets, blocks and imports are the checker's), so it suffices that:

- **Axiom closures are forced everywhere.** The propositional axioms are intuitionistically
  valid, and a closure assigns every free variable an element of a later world's domain. `vac`
  is persistence, since `x` isn't free in `A`; `dist` and `ex_e` unfold the clauses above.
  `inst` and `ex_i` need an element for `y`, which the closure supplies because it must bind
  `y`. Without that, `imp (forall x absurd) absurd` would be an axiom, and it fails in the
  empty domain.
- **Modus ponens preserves holding:** take the later world to be `w` itself.
- **Calling a lemma preserves holding.** A lemma holds for its letters as predicates, so in
  every model. Given templates and a prefix, fix a world `v` and values `ē` in `D(v)` for the
  prefix. On the worlds above `v`, read each letter `P` as the tuples its template is forced
  of, with `ē` for the template's other free variables. This is a Kripke model, by
  persistence. Capture-free substitution means a formula with the templates substituted is
  forced exactly when the original is forced in this model. So the lemma's instance holds at
  every such `v` and `ē`, which is what its closure over the prefix says.

### Completeness

**Classical** (proved during the design, not written up in full): if a closed formula `φ`
holds in every classical model, empty domains included, then the kernel proves it from
finitely many `EM` instances. Let `E` be `exists x $ imp absurd absurd`, "something exists".

1. **Under `E`:** `φ` holds in every non-empty structure, so a complete Hilbert system
   (Enderton's: closures of axioms, modus ponens only) proves it. Its only step missing here is
   dropping a `forall` whose variable doesn't occur, and the kernel proves that step from `E`
   by `ex_e`. Its tautologies follow from `EM` instances. So `imp E φ` is provable.
2. **Under `not E`:** every `forall` subformula is provable and every `exists` subformula is
   refutable, so `φ` reduces to a propositional formula over the statement letters. That
   formula holds under every valuation (each is an empty structure), so it's a tautology, and
   `imp (not E) φ` is provable.
3. **Combine** with the instance `or E (not E)`.

**Intuitionistic** (conjecture): theorems are exactly what holds in all Kripke models with
possibly empty domains. The kernel simulates, rule by rule, the formulas-in-context sequent
calculus of categorical logic: adding a variable to the context is `vac`, substituting
variables is `inst` with its outer `forall`, and `forall` introduction and `exists`
elimination come from `dist`, `vac` and `ex_e`. Nothing simulates removing a variable, as
empty domains require. That calculus allows empty types and is complete for its categorical
models (Makkai–Reyes, Joyal), including Kripke models with possibly empty domains. Unchecked:
the cited result for this exact setting, and the simulation written out in full. Either
failing would make the kernel prove less than it could, never something false.

## Language

A file is its imports, then a sequence of `let`s and `proof`s, checked in order. A name is
either a parameter or something defined earlier. Whitespace only separates tokens.

```
import pa                            pa.hai, next to this file
let Succ x y                         primitive predicate (asserts nothing)
let Three x = exists a $ …           definition
let Induction (P x) = …              (P x) gives a predicate parameter its arity

proof name
  given A                            statement parameter
  given P x                          predicate parameter (arity 1)
  given h : FORMULA                  premise
  given all SET                      every `given` of a set of premises
  have n : FORMULA by EXPR           step; the formula is optional
  shows FORMULA by EXPR              conclusion, last
```

- **Names:** uppercase = statements and predicates; lowercase = individuals, evidence, proofs.
- **Expressions:** application by juxtaposition. `f $ x y` is `f (x y)`.
  `e |> f _ y` is `f e y`, with exactly one `_`.
- **Evidence:** applying evidence for `imp A B` to evidence for `A` is modus ponens; applying
  evidence for `forall x $ A x` to a block variable `y` gives `A y`.
- **Blocks:** `forall x y { … }` (arbitrary individuals), `assume h : A { … }` (gives
  `imp A …`), `obtain x h from e { … }` (uses `e : exists x $ A x`; the result can't mention
  `x`). Binders can be chained before one block: `forall x assume h : A forall y { … }` is
  `forall x { assume h : A { forall y { … } } }`. A block is a bare expression, or `have`
  steps followed by `shows [FORMULA] by EXPR`.
  Blocks are translated into closed kernel steps; the kernel never sees them. Proofs can't
  be applied to evidence that depends on an `assume` or `obtain`.
- **Axioms** get their letters from formula arguments (`imp1 A B`), from the evidence they are
  applied to (`and_e1 ab`), or from the step's stated formula (`have k : … by imp1`); the last
  is the only way to get a `forall` prefix.
- **Proofs** are called like functions: predicate arguments first (inferred from the evidence
  when they are applied to distinct bound variables), then evidence. A proof is checked once;
  calls check only its signature. Proofs are second-class: never passed or returned.
- **Templates:** a predicate argument is a name, possibly with leading arguments filled in
  (`LessThan y`). Free individual names in templates are closed with `forall`.
- **Axiom schemas** of a theory (induction, separation, excluded middle, …) are not premises.
  A proof takes the instances it uses (`given ind : Induction ZeroLeft`); a proof over a
  predicate `P` takes `given ind : Induction P`, and each caller supplies its instance. A
  proof uses finitely many instances, so nothing provable is lost. Statements about a whole
  theory need arithmetization.
- **Premise sets:** `let PA = given … given …` names a list of `given`s and asserts nothing.
  `given all PA`, in a proof or in another set, stands for all of them. `p PA` passes the
  caller's parameters and premises that `p` got from `PA` (directly or through nested sets),
  by name; the rest are passed as usual. Sets are expanded before checking; the kernel never
  sees them.
- **Imports** come first. `import pa` checks `pa.hai` from the same directory and makes
  everything it defines available, as if pasted in. Each file is pasted once, however often
  it is imported, and a file can't import itself, even through others. Imported names share
  one namespace, so a clash is an error. Since nothing at top level asserts anything, an
  import can't add assumptions: every proof still states its own premises.
- **Comments:** `{- … -}`, nestable.

## Deferred

`under`, anonymous templates, projection by name, qualified names and aliased imports (`.`
is reserved), documentation.
