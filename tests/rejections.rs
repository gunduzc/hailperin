//! Things the checker must refuse, and a few things it must allow, as source text.

fn err(src: &str) -> String {
    match hailperin::verify(src) {
        Ok(p) => panic!("accepted: {p:?}"),
        Err(e) => e.msg,
    }
}

fn ok(src: &str) -> Vec<String> {
    match hailperin::verify(src) {
        Ok(p) => p.into_iter().map(|(n, f)| format!("{n}: {}", hailperin::print::show(&f))).collect(),
        Err(e) => panic!("rejected: {e}"),
    }
}

#[test]
fn forall_does_not_give_exists() {
    // false in the empty domain
    let src = "theorem bad\n assume h: forall x. P x\n e: exists x. P x by exists_i h\n bad: (forall x. P x) -> exists x. P x by imp_i h e";
    assert_eq!(err(src), "bad: `exists_i` needs a witness, and no variable is in scope");
}

#[test]
fn something_exists_is_not_free() {
    let src = "theorem bad\n lemma t\n  assume f: absurd\n  t: absurd -> absurd by imp_i f f\n bad: exists x. absurd -> absurd by exists_i t";
    assert_eq!(err(src), "bad: `exists_i` needs a witness, and no variable is in scope");
}

#[test]
fn a_witness_makes_it_go_through() {
    let src = "theorem ok\n assume h: forall x. P x\n assume e: exists x. P x\n lemma c\n  assume p: P w\n  pw: P w by forall_e h w\n  ex: exists x. P x by exists_i pw\n  c: exists x. P x by exists_e e p ex\n ok: (forall x. P x) -> (exists x. P x) -> exists x. P x by imp_i h e c";
    assert_eq!(ok(src), ["ok: (forall x. P x) -> (exists x. P x) -> exists x. P x"]);
}

#[test]
fn a_variable_stays_in_scope_through_a_derivation() {
    // Q is derived under x, so it is still under x: `forall x. Q`, which is not `Q`.
    let src = "theorem bad\n assume f: forall x. P x -> Q\n assume p: forall x. P x\n fx: P x -> Q by forall_e f x\n px: P x by forall_e p x\n q: Q by imp_e fx px\n k: (forall x. P x) -> Q by imp_i p q\n bad: (forall x. P x -> Q) -> (forall x. P x) -> Q by imp_i f k";
    assert_eq!(err(src), "bad: the variable `x` is still open");
}

#[test]
fn eigenvariable_condition() {
    // `x` is free in the open assumption `p`, so it can't be generalized yet.
    let src = "theorem bad\n assume p: P x\n all: forall x. P x by forall_i x p\n bad: P x -> forall x. P x by imp_i p all";
    assert_eq!(err(src), "bad: `x` is free in the assumption P x");
}

#[test]
fn labels_are_local_to_their_block() {
    let src = "theorem bad\n lemma l\n  assume a: A\n  k: A by a\n  l: A -> A by imp_i a k\n bad: A -> A by k";
    assert_eq!(err(src), "bad: `k` is not a rule, a line here, or a theorem");
}

#[test]
fn premises_are_computed_and_checked() {
    let src = "theory T\n t: forall x. P x\ntheory U\n u: forall x. Q x\ntheorem bad in T\n q: Q x by forall_e U.u x\n bad: forall x. Q x by forall_i x q";
    assert_eq!(err(src), "bad: `U.u` is a premise, but not a member of T");
    let src = "theory T\n t: forall x. P x\ntheory U\n include T\ntheorem ok in U\n p: P x by forall_e U.t x\n ok: forall x. P x by forall_i x p";
    assert_eq!(ok(src), ["ok: forall x. P x"]);
}

#[test]
fn cited_theorems_carry_their_premises() {
    let src = "theory T\n t: forall x. P x\ntheorem first in T\n p: P x by forall_e T.t x\n first: forall x. P x by forall_i x p\ntheorem second\n second: forall x. P x by first";
    // `second` names no theory, so any premise is fine, and it rests on T.t through `first`.
    assert_eq!(ok(src).len(), 2);
    let src = "theory T\n t: forall x. P x\ntheory U\n u: forall x. Q x\ntheorem first in T\n p: P x by forall_e T.t x\n first: forall x. P x by forall_i x p\ntheorem second in U\n second: forall x. P x by first";
    assert_eq!(err(src), "second: `T.t` is a premise, but not a member of U");
}

#[test]
fn parameters_are_inferred_at_citation() {
    let src = "theorem mp\n assume ab: A -> B\n assume a: A\n b: B by imp_e ab a\n mp: (A -> B) -> A -> B by imp_i ab a b\n\
               theorem use\n assume h: P x -> Q x\n assume p: P x\n q: Q x by mp h p\n k: (P x -> Q x) -> P x -> Q x by imp_i h p q\n use: forall x. (P x -> Q x) -> P x -> Q x by forall_i x k";
    assert_eq!(ok(src).len(), 2);
}

#[test]
fn definitions_fold_and_unfold_silently() {
    let src = "define Iff A B = (A -> B) and (B -> A)\ntheorem ok\n assume a: A\n aa: A -> A by imp_i a a\n i: Iff A A by and_i aa aa\n ok: Iff A A by i";
    assert_eq!(ok(src), ["ok: (A -> A) and (A -> A)"]);
}

#[test]
fn citation_instantiates_by_matching_or_says_what_it_cannot() {
    let src = "theory T\n t: forall x y. P x -> Q x y\ntheorem ok in T\n assume p: P a\n q: Q a b by T.t p\n k: P a -> Q a b by imp_i p q\n ok: forall a b. P a -> Q a b by forall_i a b k";
    assert!(hailperin::verify(src).is_ok(), "{:?}", hailperin::verify(src).err());
    // `y` occurs in neither the line nor the stated formula.
    let src = "theory T\n t: forall x y. P x -> R x\ntheorem bad in T\n assume p: P a\n bad: R a by T.t p";
    assert_eq!(err(src), "bad: can't work out `y` in forall x y. P x -> R x: instantiate it with `forall_e`");
}

#[test]
fn one_rule_per_line() {
    let src = "theorem t\n assume a: A\n t: A -> A by imp_i a (imp_i a a)";
    assert_eq!(err(src), "one rule per line: give `imp_i` a line of its own");
}
