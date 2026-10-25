# hailperin spec

## Logic

Universally free (Hailperin-style) intuitionistic first-order logic.

- One domain, possibly empty.
- Terms are variables. No sorts, no built-in equality. Individuals are predicates (`Socrates x`), functions are relations (`Succ x y`).
- Theorems are closed formulas. Modus ponens is the only rule.
- Classical logic is a theory: `em A: A or not A`. Non-emptiness is a formula: `not (forall x. absurd)`.

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

A file is ASCII, comments included. Whitespace only separates tokens. Comments are `{- ... -}` and nest.

**Names.** Uppercase: predicates, definitions, theories. Lowercase: variables, labels, theorems, rules. A name matches `letter (letter | digit | '_' (letter | digit))*`. Reserved: `theorem theory define include import in assume lemma by forall exists and or not absurd`, and the rule names, `auto` among them.

```
file     ::= import* item*
import   ::= 'import' name
item     ::= define | theory | theorem

define   ::= 'define' Name param* '=' formula
theory   ::= 'theory' Name member*
member   ::= 'include' Name
           | label ':' formula
           | label Name+ ':' formula

theorem  ::= 'theorem' name ['in' Name+] block
block    ::= assume* step* result
assume   ::= 'assume' label ':' formula
step     ::= label ':' formula 'by' just
           | 'lemma' label block
result   ::= label ':' formula 'by' just         the label is the block's own name

just     ::= ref targ* arg*                      templates for the head first, then lines
ref      ::= rule | name | Name '.' label
arg      ::= label | var | Name '.' label | '(' ref targ* ')'

formula  ::= ('forall' | 'exists') var+ '.' formula
           | disj ['->' formula]
disj     ::= conj ('or' conj)*
conj     ::= neg ('and' neg)*
neg      ::= 'not' neg | atom
atom     ::= 'absurd' | Name targ* | '(' formula ')'
targ     ::= var | Name | '(' formula ')' | '(' Name targ* ')'
```

The grammar is LL(2): after a justification's arguments, a lowercase name is the next label or one more argument, and the `:` after it decides. Everything else is LL(1).

### Definitions

```
define Iff A B = (A -> B) and (B -> A)
define Eq x y = forall z. Iff (In z x) (In z y)
define Induction P = (forall x. Zero x -> P x) -> (forall y x. P x -> Succ x y -> P y) -> forall x. P x
```

A definition names a formula and asserts nothing. Uppercase parameters are predicates, with arity read off the body. Lowercase parameters are individuals. An uppercase name nothing defines, used in a definition or a theory member, is a primitive predicate of the file from then on, with the arity of that use. Definitions unfold and fold silently wherever a rule needs it. Applied to fewer individuals than it takes, a definition is a template: `EqOr A e` is the predicate `z |-> Eq z e or A`.

### Theories

```
theory Q
  pz: forall x z. Zero z -> Plus x z x
  ...

theory HA
  include Q
  ind P: (forall x. Zero x -> P x) -> (forall y x. P x -> Succ x y -> P y) -> forall x. P x

theory PA
  include HA
  include Classical
```

A theory is a named list of labeled closed formulas and asserts nothing. `include` copies members in: `PA.pz` and `Q.pz` are the same member. A member with parameters, `ind P`, is a schema, and each application is one closed formula.

`PA.pz` is the axiom, `PA.ind ZeroLeft` an instance, `Sets.sep (EqOr A e)` an instance closed over the variable `e` in scope. The members a theorem mentions, directly or through the theorems it cites, are its premises. `hailperin explain` prints them. `theorem t in PA HA` claims every premise of `t` is in a named theory, and is checked.

A schema is sound when its parameter may be any formula (induction, separation, excluded middle). When it may not (Sigma_1 induction, naive comprehension, the truth schema), mind which instances you mention, or arithmetize. The checker cannot tell.

### Theorems

```
theorem socrates_is_mortal
  assume sp: forall x. Socrates x -> Person x
  assume pm: forall x. Person x -> Mortal x
  lemma all
    assume s: Socrates x
    sp1: Socrates x -> Person x          by forall_e sp x
    pm1: Person x -> Mortal x            by forall_e pm x
    p:   Person x                        by imp_e sp1 s
    m:   Mortal x                        by imp_e pm1 p
    sm:  Socrates x -> Mortal x          by imp_i s m
    all: forall x. Socrates x -> Mortal x     by forall_i x sm
  socrates_is_mortal:
    (forall x. Socrates x -> Person x)
      -> (forall x. Person x -> Mortal x)
      -> forall x. Socrates x -> Mortal x     by imp_i sp pm all
```

**Blocks.** Labels are local to their block. A block's result must close every assumption the block opened, and is visible after the block under the block's name.

**Parameters.** Uppercase names nothing defines are the theorem's parameters, with arity read off their use. A citation infers them from its lines or, when that fails, takes templates first: `by all_to_some (Unicorn) u h`.

**Lines.** A line stands for its closure: the stated formula under an implication for each open assumption it rests on and a `forall` for each variable in scope. The kernel holds the closure. Quine and Hailperin write `|- A` for this: the closure of `A` is a theorem.

**Scope.** A variable is in scope from its first free occurrence until `forall_i` or `exists_e` closes it. An assumption is open from its `assume` until `imp_i` or `exists_e` closes it. A line derived from others is in the scope of all of them. Layers close in any order: closing one that is not innermost moves it inward first, by Hailperin's QE1 and QE5, which is allowed unless the variable moved is free in an assumption it passes. Variables are not scoped by blocks. A theorem's result has closed everything.

**Rules.** Several arguments of one kind mean the rule applied once per argument, in order.

| rule | from | gives |
|---|---|---|
| `imp_i a... l` | assumptions `a...`, line `l : L` | `A -> ... -> L`. Closes `a...` |
| `imp_e f a...` | `f : A -> B`, `a : A` | `B` |
| `and_i a b` | `A`, `B` | `A and B` |
| `and_e1 c`, `and_e2 c` | `A and B` | `A`, `B` |
| `or_i1 a`, `or_i2 b` | `A`, `B` | `A or B`. The other side from the stated formula |
| `or_e d p q` | `A or B`, `A -> C`, `B -> C` | `C` |
| `absurd_e f` | `absurd` | the stated formula |
| `forall_i x... l` | `l : L` with `x...` in scope | `forall x.... L`. Closes `x...`. `x` not free in any open assumption |
| `forall_e h y...` | `forall x.... A` | `A[y/x]...`. `y...` enter scope |
| `exists_i l` | `A[y/x]`, stated as `exists x. A` | `exists x. A`. `exists_i l y` names the witness when `A` doesn't show it |
| `exists_e e h c` | `e : exists x. A`, `h` assumes `A[w/x]`, `c : C` | `C`. Closes `w` and `h`. `w` not free in `C` or any other open assumption |
| `t a...` | theorem `t`, lines for its leading antecedents | the rest of `t`. Leading `forall`s are instantiated by matching the lines and the stated formula |
| `l` | line `l` | `L` restated, folded or unfolded |
| `auto` | | reserved for a tool that fills lines in. The checker refuses it |

A theory member, or a theorem with its antecedents supplied, is a line. Citing either with lines instantiates its leading `forall`s: each variable takes what the lines, or the stated formula, have in its place, and `forall_e` serves the variables neither fixes. `Plus w w w by Q.pz zw` finds `z := w` from the line and `x := w` from the stated formula. `not A` is `A -> absurd`, so `imp_i` and `imp_e` serve it.

**Russell**, with the lemma nesting the witnesses need:

```
define NotSelf x = not (In x x)

theorem russell in Sets
  assume h: exists u. forall x. In x u
  lemma u_case
    assume hu: forall x. In x u
    sep: exists s. forall z. Iff (In z s) (In z u and NotSelf z)    by forall_e (Sets.sep NotSelf) u
    lemma s_case
      assume hs: forall z. Iff (In z s) (In z u and NotSelf z)
      hss: Iff (In s s) (In s u and NotSelf s)                       by forall_e hs s
      fwd: In s s -> In s u and NotSelf s                            by and_e1 hss
      bwd: In s u and NotSelf s -> In s s                            by and_e2 hss
      lemma nx
        assume x: In s s
        c:  In s u and NotSelf s                                     by imp_e fwd x
        ns: NotSelf s                                                by and_e2 c
        f:  absurd                                                   by imp_e ns x
        nx: NotSelf s                                                by imp_i x f
      su: In s u                                                     by forall_e hu s
      c2: In s u and NotSelf s                                       by and_i su nx
      x2: In s s                                                     by imp_e bwd c2
      f2: absurd                                                     by imp_e nx x2
      s_case: absurd                                                 by exists_e sep hs f2
    u_case: absurd                                                   by exists_e h hu s_case
  russell: not (exists u. forall x. In x u)                          by imp_i h u_case
```

### Imports

`import pa` checks `pa.hai` from the same directory and pastes it in, once, however often it is imported. Cycles and name clashes are errors. Nothing at top level asserts anything, so an import adds no premises.

### Formatting

`hailperin fmt` indents one level per block and changes nothing else. `hailperin explain FILE` prints each line's closure and each theorem's premises.
