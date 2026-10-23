//! Things the checker must refuse, and a few things it must allow.

fn err(src: &str) -> String {
    match hailperin::verify(src) {
        Ok(p) => panic!("accepted: {p:?}"),
        Err(e) => e.msg,
    }
}

fn ok(src: &str) -> Vec<String> {
    match hailperin::verify(src) {
        Ok(p) => p.into_iter().map(|(n, f)| format!("{n}: {f}")).collect(),
        Err(e) => panic!("rejected: {e}"),
    }
}

#[test]
fn not_an_instance() {
    assert_eq!(err("proof bogus given A given B shows imp A B by imp1"), "bogus: imp A B is not an instance of `imp1`");
}

#[test]
fn inst_needs_its_forall() {
    // false in the empty domain
    assert_eq!(err("proof bad shows imp (forall x $ absurd) absurd by inst"), "bad: imp (forall x $ absurd) absurd is not an instance of `inst`");
}

#[test]
fn something_exists_is_not_free() {
    assert_eq!(err("proof bad shows exists x $ imp absurd absurd by ex_i"), "bad: exists x $ imp absurd absurd is not an instance of `ex_i`");
}

#[test]
fn side_conditions() {
    assert_eq!(err("let Man x\nproof bad have v : forall x $ imp (Man x) (forall x $ Man x) by vac shows absurd by v"), "bad: forall x $ imp (Man x) (forall x $ Man x) is not an instance of `vac`");
    assert_eq!(err("let P x\nproof bad given f : forall x $ imp (P x) (P x) shows absurd by ex_e f"), "bad: ex_e: `x` is free in P x");
}

#[test]
fn modus_ponens_must_fit() {
    assert_eq!(err("proof bad given A given B given a : A given f : imp B A shows A by f a"), "bad: imp B A needs B, but got A");
}

#[test]
fn formulas_are_closed() {
    assert_eq!(err("let Man x\nproof bad given h : Man x shows absurd by h"), "bad: `x` is free: bind it with `forall` or `exists`");
}

#[test]
fn kinds_and_names() {
    assert_eq!(err("let Mortal x\nlet Wise x\nlet F = Mortal Wise"), "expected an individual: a lowercase variable name");
    assert_eq!(err("let man x"), "`man` should be uppercase (it's a statement or predicate)");
    assert_eq!(err("let P x\nlet P y"), "`P` is already defined");
    assert_eq!(err("let F = Nope"), "`Nope` is not defined");
    assert_eq!(err("let imp1 = absurd"), "`imp1` is built in");
}

#[test]
fn proof_structure() {
    assert_eq!(err("proof p given A"), "p: a proof needs a `shows`");
    assert_eq!(err("proof p given A shows imp A A by imp1 A A given B"), "p: `shows` must be the last part of a proof");
    assert_eq!(err("proof p given A given A shows absurd by x"), "p: `A` is already used in this proof");
    assert_eq!(err("proof p given A shows A by imp1 A A"), "p: this proves imp A A A, not A");
}

#[test]
fn calls_check_their_hypotheses() {
    let prelude = "proof keep given A given a : A shows A by a\n";
    // Inferring A from the evidence works; a mismatched explicit A does not.
    assert_eq!(ok(&format!("{prelude}proof p given B given b : B shows B by keep b")).len(), 2);
    assert_eq!(err(&format!("{prelude}proof p given B given C given b : B shows C by keep C b")), "p: keep: evidence 1 should prove C, but proves B");
}

const PA: &str = "let Zero x\nlet Succ x y\n\
                  let Induction (P x) = imp (forall x $ imp (Zero x) (P x)) \
                    (forall y $ forall x $ imp (P x) (Succ x y) (P y)) (forall x $ P x)\n";

#[test]
fn induction_instances_are_hypotheses() {
    // A proof over any P takes induction for P as a hypothesis, and a caller passes its instance on.
    let src = format!(
        "{PA}proof use given P x given ind : Induction P given b : forall x $ imp (Zero x) (P x) \
           given s : forall y $ forall x $ imp (P x) (Succ x y) (P y) \
           shows forall x $ P x by ind b s\n\
         proof forward given ind : Induction Zero given b : forall x $ imp (Zero x) (Zero x) \
           given s : forall y $ forall x $ imp (Zero x) (Succ x y) (Zero y) \
           shows forall x $ Zero x by use Zero ind b s"
    );
    assert_eq!(ok(&src).len(), 2);
    // Another instance can't stand in for it.
    let bad = format!(
        "{PA}proof use given P x given ind : Induction P shows imp absurd absurd by efq absurd\n\
         proof other given Q x given ind : Induction Zero shows imp absurd absurd by use Q ind"
    );
    assert!(err(&bad).starts_with("other: use: evidence 1 should prove "));
}

#[test]
fn templates_close_over_their_variables() {
    // A two-place relation with its first argument fixed, as a one-place predicate.
    let src = "let R x y\n\
               proof all_of given P x given s : forall x $ P x shows forall x $ P x by s\n\
               proof p given h : forall y $ forall x $ R y x shows forall y $ forall x $ R y x by all_of (R y) h";
    assert_eq!(ok(src)[1], "p: forall y $ forall x $ R y x");
}

#[test]
fn predicate_arguments_are_predicates() {
    let pre = "let Q x\nlet All (P x) = forall x $ P x\nproof keep given A given a : A shows A by a\nlet F = All ";
    assert_eq!(err(&format!("{pre}absurd")), "`absurd` is a statement, but a 1-place predicate is needed");
    assert_eq!(err(&format!("{pre}(not Q)")), "`not` can't be a 1-place predicate argument; give it a name with `let`");
    assert_eq!(err(&format!("{pre}imp1")), "`imp1` is built in, not a predicate");
    assert_eq!(err(&format!("{pre}keep")), "`keep` is a proof, not a predicate");
    assert_eq!(err(&format!("{pre}x")), "`x` is lowercase, so it isn't a predicate");
}

#[test]
fn no_capture_through_definitions() {
    // The definition's bound y must not capture the caller's y.
    let src = "let R x y\n\
               let Some (P x) = exists y $ P y\n\
               proof p given h : forall y $ Some (R y) shows forall y $ exists y' $ R y y' by h";
    assert_eq!(ok(src), ["p: forall y $ exists y' $ R y y'"]);
}

#[test]
fn classical_hypotheses_are_inherited() {
    // A proof that uses excluded middle can't be called without supplying it.
    let src = std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/examples/classical.hai")).unwrap();
    let cut = src.find("proof dne\n").unwrap();
    let bad = format!("{}proof dne given A given nna : not (not A) shows A by peirce (trans nna (efq A))", &src[..cut]);
    assert_eq!(err(&bad), "dne: `peirce` needs 2 piece(s) of evidence, got 1");
}

#[test]
fn quantifiers_can_be_swapped() {
    // Not provable before `inst` allowed its variable anywhere in the prefix.
    let src = "proof swap given R x y given h : forall x $ forall y $ R x y \
               shows forall y $ forall x $ R x y by forall y x { h x y }";
    assert_eq!(ok(src), ["swap: forall y $ forall x $ R x y"]);
}

#[test]
fn obtained_witness_stays_inside() {
    assert_eq!(err("proof bad given P x given e : exists x $ P x shows absurd by obtain w pw from e { pw }"), "bad: this proves P w, not absurd");
    assert_eq!(err("let P x\nproof bad given e : exists x $ P x have h by obtain w pw from e { pw } shows absurd by h"), "bad: the result of `obtain` can't mention `w`: P w");
}

#[test]
fn blocks_check_their_names_and_shapes() {
    assert_eq!(err("proof bad given h : absurd shows absurd by forall h { h }"), "bad: `h` is already used in this proof");
    assert_eq!(err("proof bad given A shows imp A A by forall x { x }"), "bad: `x` is not defined");
}

#[test]
fn proofs_under_assumptions_are_refused() {
    let src = "proof keep given A given a : A shows A by a\n\
               proof bad given A shows imp A A by assume a : A { keep a }";
    assert_eq!(err(src), "bad: `keep` can't be applied to evidence that depends on an `assume` or `obtain`");
}

#[test]
fn templates_may_mention_variables_under_assumptions() {
    // `R y` mentions `y`, which comes from inside an `obtain`: fine, since no evidence depends
    // on the assumption.
    let src = "let R x y\n\
               proof refl given P x shows forall x $ imp (P x) (P x) by forall x assume h : P x { h }\n\
               proof p given e : exists y $ forall x $ R y x \
               shows forall x $ exists y $ R y x by forall x obtain y h from e {
                 have i : imp (R y x) (exists y' $ R y' x) by ex_i
                 shows by i (refl (R y) x (h x)) }";
    assert_eq!(ok(src)[1], "p: forall x $ exists y $ R y x");
}

#[test]
fn hypothesis_sets() {
    let base = "let S = given A given a : A\nlet T = given all S given B\nproof keep given all T shows A by a\n";
    // Passing the outer set passes the inner one's hypotheses too.
    assert_eq!(ok(&format!("{base}proof again given all T shows A by keep T")).len(), 2);
    // Passing just the inner set leaves the rest to be given explicitly.
    assert_eq!(ok(&format!("{base}proof third given all S given C shows A by keep S C")).len(), 2);
    // Passing it needs every hypothesis in scope under its name.
    assert_eq!(err(&format!("{base}proof p given A shows A by keep S")), "p: passing that set needs evidence named `a` here");
    // A set is not a statement.
    assert_eq!(err(&format!("{base}let F = imp S S")), "`S` is a set of hypotheses, not a statement");
}

#[test]
fn inst_and_ex_i_never_capture() {
    // Instantiating `x` at `y` under `exists y` would turn "everyone has a y" into "some y has itself".
    assert_eq!(err("let R x y\nproof bad shows forall y $ imp (forall x $ exists y $ R x y) (exists y $ R y y) by inst"), "bad: forall y $ imp (forall x $ exists y $ R x y) (exists y $ R y y) is not an instance of `inst`");
    assert_eq!(err("let R x y\nproof bad shows forall y $ imp (forall y $ R y y) (exists x $ forall y $ R x y) by ex_i"), "bad: forall y $ imp (forall y $ R y y) (exists x $ forall y $ R x y) is not an instance of `ex_i`");
}

#[test]
fn no_recursion_or_forward_references() {
    assert_eq!(err("let F = F"), "`F` is not defined");
    assert_eq!(err("let F x = F x"), "`F` is not defined");
    assert_eq!(err("let S = given all S"), "S: `S` is not a set of hypotheses");
    assert_eq!(err("proof p given A given a : A shows A by p a"), "p: `p` is not defined");
    let src = "proof p given A given a : A shows A by q a\nproof q given A given a : A shows A by a";
    assert_eq!(err(src), "p: `q` is not defined");
}

#[test]
fn names_stay_in_their_blocks() {
    let pre = "let P x\nproof bad given h : forall x $ P x ";
    assert_eq!(err(&format!("{pre}have k : forall y $ P y by forall y {{ h y }} shows forall z $ P z by h y")), "bad: `y` is not defined");
    assert_eq!(err("proof bad given A have k : imp A A by assume a : A { a } shows A by a"), "bad: `a` is not defined");
    assert_eq!(err("proof bad given A have k : imp A A by assume c : A { have b : A by c shows A by b } shows A by b"), "bad: `b` is not defined");
    assert_eq!(err("let P x\nproof bad given e : exists x $ P x shows forall z $ P z by forall z obtain z h from e { h }"), "bad: `z` is already used in this proof");
    // Sibling blocks may reuse a name.
    let src = format!("{pre}have k : forall y $ P y by forall y {{ h y }} shows forall y $ P y by forall y {{ h y }}");
    assert_eq!(ok(&src), ["bad: forall y $ P y"]);
}

#[test]
fn theorems_take_no_predicates() {
    assert_eq!(err("let P x\nproof bad given h : forall x $ P x given Q x shows forall x $ Q x by h Q"), "bad: `h` is a theorem; it takes only evidence and individuals");
}

#[test]
fn vac() {
    assert_eq!(ok("proof p given A shows imp A (forall x $ A) by vac"), ["p: imp A (forall x $ A)"]);
    // `x` may be free in the body, as long as the new binder is another variable.
    let src = "let P x\nproof p shows forall x $ imp (P x) (forall y $ P x) by vac";
    assert_eq!(ok(src), ["p: forall x $ imp (P x) (forall y $ P x)"]);
}

#[test]
fn pipe() {
    let src = "proof p given A given B given a : A shows imp B A by a |> imp1 A B _";
    assert_eq!(ok(src), ["p: imp B A"]);
}

#[test]
fn axiom_closures_are_flexible() {
    // Extra binders, in any order.
    let src = "let P x\nproof p shows forall z $ forall y $ forall x $ imp (forall x $ P x) (P y) by inst";
    assert_eq!(ok(src), ["p: forall z $ forall y $ forall x $ imp (forall x $ P x) (P y)"]);
    // The instantiated variable need not occur, as long as it's bound.
    assert_eq!(ok("proof p given A shows forall y $ imp (forall x $ A) A by inst"), ["p: forall y $ imp (forall x $ A) A"]);
    assert_eq!(ok("proof p given A shows forall y $ imp A (exists x $ A) by ex_i"), ["p: forall y $ imp A (exists x $ A)"]);
    // Statements match up to renaming of bound variables.
    let src = "let R x y\nproof p given h : forall x $ forall y $ R x y shows forall a $ forall b $ R a b by h";
    assert_eq!(ok(src), ["p: forall a $ forall b $ R a b"]);
}

#[test]
fn steps_depend_only_on_what_they_use() {
    // A step inside `assume` that doesn't use the assumption can still be passed to a proof.
    let pre = "proof keep given A given a : A shows A by a\n";
    let src = format!("{pre}proof p given A given B given a : A shows imp B A by assume b : B {{ have k : A by a shows A by keep k }}");
    assert_eq!(ok(&src)[1], "p: imp B A");
    let src = format!("{pre}proof p given A given B given C given ac : and A C shows imp B A by \
                       assume b : B {{ have k : A by and_e1 ac shows A by keep k }}");
    assert_eq!(ok(&src)[1], "p: imp B A");
    // One that does use it still can't.
    let src = format!("{pre}proof p given A shows imp A A by assume a : A {{ have k : A by a shows A by keep k }}");
    assert_eq!(err(&src), "p: `keep` can't be applied to evidence that depends on an `assume` or `obtain`");
}

#[test]
fn axioms_on_evidence_use_the_stated_result() {
    // The stated formula fixes the letters of `ex_i` that its evidence can't.
    let src = "let R x y\nproof p given h : forall a $ exists b $ R a b shows forall a $ exists y $ R a y by \
               forall a { obtain b k from h a { have r : exists y $ R a y by ex_i k shows by r } }";
    assert_eq!(ok(src), ["p: forall a $ exists y $ R a y"]);
    // A witness that doesn't occur can be any individual in scope, but there must be one.
    let src = "let True = imp absurd absurd\nproof p shows forall z $ exists x $ True by \
               forall z { have t : True by efq absurd have e : exists x $ True by ex_i t shows by e }";
    assert_eq!(ok(src), ["p: forall z $ exists x $ imp absurd absurd"]);
    let src = "let True = imp absurd absurd\nproof p have t : True by efq absurd shows exists x $ True by ex_i t";
    assert_eq!(err(src), "p: `ex_i` needs a witness, and no individual is in scope");
}

#[test]
fn fixed_axiom_instances_report_why_they_fail() {
    assert_eq!(err("let P x\nlet Q\nproof p have k by imp1 (P z) Q shows imp absurd absurd by efq absurd"), "p: this axiom instance has `z` free: formulas must be closed");
}

#[test]
fn sets_included_twice_count_once() {
    let base = "let C = given A given a : A\nlet S1 = given all C\nlet S2 = given all C\n";
    let src = format!("{base}proof p given all S1 given all S2 shows A by a\nproof q given all S2 shows A by p S2");
    assert_eq!(ok(&src), ["p: A", "q: A"]);
    // A real clash is reported where the proof includes the set.
    let src = format!("{base}let D = given A\nproof p given all C\n given all D shows A by a");
    let e = hailperin::verify(&src).unwrap_err();
    assert_eq!((e.line, e.msg.as_str()), (6, "p: `A` is already used in this proof"));
}

#[test]
fn inference_respects_shadowing() {
    // In `forall c $ forall c $ and (Q c) (R c)`, both `c`s are the inner one, so it isn't an
    // instance of `forall a $ forall b $ and (Q a) (P b)`.
    let src = "let Q x\nlet R x\nproof k given P x given h : forall a $ forall b $ and (Q a) (P b) shows imp absurd absurd by efq absurd\n\
               proof use given h : forall c $ forall c $ and (Q c) (R c) shows imp absurd absurd by k h";
    assert_eq!(err(src), "use: can't work out `P` for `k`; pass it explicitly");
}

/// Like `ok` and `err`, with imports found in `examples/`.
fn with_examples(src: &str) -> Result<Vec<String>, String> {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples");
    let mut proved = Vec::new();
    let r = hailperin::verify_in(src, &dir, None, &mut |_, p| proved.extend(p.map(|(n, _)| n.clone())));
    r.map(|()| proved).map_err(|e| e.to_string())
}

#[test]
fn imports_are_pasted_once() {
    // plus_comm imports pa; importing pa again is a no-op, not a clash.
    let src = "import plus_comm\nimport pa\nproof again given all PA given izl : Induction ZeroLeft \
               given isl : Induction SuccLeft given ind : Induction Comm \
               shows forall x $ forall y $ forall z $ imp (Plus x y z) (Plus y x z) by plus_comm PA izl isl ind";
    assert_eq!(with_examples(src).unwrap(), ["again"]);
    // Imported names clash like any others.
    assert_eq!(with_examples("import basics\nlet Man x").unwrap_err(), "line 2: `Man` is already defined");
}
