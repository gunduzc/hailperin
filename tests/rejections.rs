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
    let src = "theorem bad:\n predicate P x\n assume h: forall x. P x\n e: exists x. P x by exists_i h\n therefore (forall x. P x) -> exists x. P x";
    assert_eq!(err(src), "bad: `exists_i` needs a witness, and no variable is in scope");
}

#[test]
fn something_exists_is_not_free() {
    let src = "theorem bad:\n lemma t:\n  assume f: absurd\n  therefore absurd -> absurd\n e: exists x. absurd -> absurd by exists_i t\n therefore exists x. absurd -> absurd";
    assert_eq!(err(src), "bad: `exists_i` needs a witness, and no variable is in scope");
}

#[test]
fn a_witness_makes_it_go_through() {
    let src = "theorem ok:\n predicate P x\n assume h: forall x. P x\n assume e: exists x. P x\n lemma c:\n  variable w\n  assume p: P w\n  pw: P w by forall_e h w\n  ex: exists x. P x by exists_i pw\n  therefore forall w. P w -> exists x. P x\n k: exists x. P x by exists_e e c\n therefore (forall x. P x) -> (exists x. P x) -> exists x. P x";
    assert_eq!(ok(src), ["ok: (forall x. P x) -> (exists x. P x) -> exists x. P x"]);
}

#[test]
fn therefore_states_the_closure() {
    // Q is derived under x, so the lemma yields `forall x. Q`, not `Q`.
    let src = "theorem bad:\n predicate P x\n predicate Q\n assume f: forall x. P x -> Q\n assume p: forall x. P x\n lemma l:\n  variable x\n  fx: P x -> Q by forall_e f x\n  px: P x by forall_e p x\n  q: Q by imp_e fx px\n  therefore Q\n therefore (forall x. P x -> Q) -> (forall x. P x) -> Q";
    assert_eq!(err(src), "bad: `q`, closed over `x`, gives forall x. Q, not Q");
    let src = "theorem bad:\n predicate A\n assume a: A\n therefore A";
    assert_eq!(err(src), "bad: `a`, closed over `a`, gives A -> A, not A");
}

#[test]
fn variables_are_declared() {
    let src = "theorem bad:\n predicate P x\n assume p: P x\n therefore P x -> P x";
    assert_eq!(err(src), "bad: `x` is not in scope: declare it with `variable x`, or bind it");
    let src = "theorem bad:\n predicate P x\n assume h: forall x. P x\n p: P y by forall_e h y\n therefore (forall x. P x) -> P y";
    assert_eq!(err(src), "bad: `y` is not in scope: declare it with `variable y`, or bind it");
}

#[test]
fn names_never_meet() {
    let src = "theorem bad:\n predicate P y\n variable x\n assume x: P x\n therefore forall x. P x -> P x";
    assert_eq!(err(src), "bad: `x` is a variable in scope, so it can't be a label");
    let src = "theorem bad:\n predicate P y\n variable x\n lemma l:\n  variable x\n  therefore forall x. absurd -> absurd\n therefore absurd";
    assert_eq!(err(src), "bad: `x` is already a variable in scope");
    let src = "theorem bad:\n predicate P x\n variable x\n assume h: P x\n therefore forall x. P x -> P x";
    assert_eq!(err(src), "bad: `x` is a name here, so it can't be a placeholder of `P`");
}

#[test]
fn predicates_are_declared() {
    let src = "define X = P a";
    assert_eq!(err(src), "`P` is not declared: add `predicate P x` before this, or to the theorem");
    let src = "predicate P x\ntheorem bad:\n assume a: P\n therefore P -> P";
    assert_eq!(err(src), "bad: `P` takes 1 argument(s), got 0");
}

#[test]
fn sections_come_in_order() {
    let src = "theorem bad:\n predicate A\n assume a: A\n variable x\n therefore A -> A";
    assert_eq!(err(src), "`variable` lines come before `assume` lines in a block");
    let src = "theorem bad:\n predicate A\n a: A by reit x\n assume b: A\n therefore A";
    assert_eq!(err(src), "declarations come before the steps of a block");
}

#[test]
fn labels_are_local_to_their_block() {
    let src = "theorem bad:\n predicate A\n lemma l:\n  assume a: A\n  k: A by reit a\n  therefore A -> A\n j: A by reit k\n therefore A";
    assert_eq!(err(src), "bad: `k` was a line of lemma `l`, which has closed");
}

#[test]
fn a_citation_passes_every_template() {
    let src = "theorem mp:\n predicate A\n predicate B\n assume ab: A -> B\n assume a: A\n b: B by imp_e ab a\n therefore (A -> B) -> A -> B\n\
               theorem use:\n predicate P x\n predicate Q x\n lemma l:\n  variable x\n  assume h: P x -> Q x\n  assume p: P x\n  q: Q x by imp_e mp (P x) (Q x) h p\n  therefore forall x. (P x -> Q x) -> P x -> Q x\n therefore forall x. (P x -> Q x) -> P x -> Q x";
    assert_eq!(ok(src).len(), 2);
    let src = "theorem mp:\n predicate A\n predicate B\n assume ab: A -> B\n assume a: A\n b: B by imp_e ab a\n therefore (A -> B) -> A -> B\n\
               theorem bad:\n predicate P x\n predicate Q x\n lemma l:\n  variable x\n  assume h: P x -> Q x\n  assume p: P x\n  q: Q x by imp_e mp (P x) h p\n  therefore forall x. (P x -> Q x) -> P x -> Q x\n therefore forall x. (P x -> Q x) -> P x -> Q x";
    assert_eq!(err(src), "bad: `mp` takes templates for `A` and `B`, in that order");
    let src = src.replace("imp_e mp (P x) h p", "imp_e mp (P x) (Q x) (Q x) h p");
    assert_eq!(err(&src), "bad: `mp` takes only templates for `A` and `B`, in that order");
    // A template may be a definition applied to fewer individuals than it takes.
    let src = "predicate R x y\npredicate Q\ndefine RA a z = R z a\ntheorem t:\n predicate P x\n lemma l:\n  variable x\n  assume h: P x\n  assume q: Q\n  therefore forall x. P x -> Q -> Q\n therefore forall x. P x -> Q -> Q\n\
               theorem ok:\n variable a\n assume r: R a a\n assume q: Q\n k: Q by imp_e t (RA a) r q\n therefore forall a. R a a -> Q -> Q";
    assert_eq!(ok(src).len(), 2);
}

#[test]
fn definitions_fold_and_unfold_silently() {
    let src = "define Iff A B = (A -> B) and (B -> A)\ntheorem ok:\n predicate A\n lemma aa:\n  assume a: A\n  therefore A -> A\n i: Iff A A by and_i aa aa\n therefore Iff A A";
    assert_eq!(ok(src), ["ok: (A -> A) and (A -> A)"]);
}

#[test]
fn citation_instantiates_by_matching_or_says_what_it_cannot() {
    let src = "predicate P x\npredicate Q x y\ndefine T = forall x y. P x -> Q x y\ntheorem ok:\n assume t: T\n lemma l:\n  variable a b\n  assume p: P a\n  q: Q a b by imp_e t p\n  therefore forall a b. P a -> Q a b\n therefore T -> forall a b. P a -> Q a b";
    assert!(hailperin::verify(src).is_ok(), "{:?}", hailperin::verify(src).err());
    // `y` occurs in neither the line nor the stated formula.
    let src = "predicate P x\npredicate R x\ntheorem bad:\n variable a\n assume t: forall x y. P x -> R x\n assume p: P a\n r: R a by imp_e t p\n therefore forall a. (forall x y. P x -> R x) -> P a -> R a";
    assert_eq!(err(src), "bad: can't work out `y` in forall x y. P x -> R x: instantiate it with `forall_e`");
}

#[test]
fn exists_e_takes_the_closed_witness_line() {
    let src = "predicate P x\npredicate Q\ntheorem ok:\n assume e: exists x. P x\n assume f: forall x. P x -> Q\n lemma g:\n  variable w\n  assume p: P w\n  q: Q by imp_e f p\n  therefore forall w. P w -> Q\n k: Q by exists_e e g\n therefore (exists x. P x) -> (forall x. P x -> Q) -> Q";
    assert_eq!(ok(src).len(), 1);
    // The conclusion may not mention the witness.
    let src = "predicate P x\ntheorem bad:\n assume e: exists x. P x\n lemma g:\n  variable w\n  assume p: P w\n  therefore forall w. P w -> P w\n k: P w by exists_e e g\n therefore (exists x. P x) -> P w";
    assert_eq!(err(src), "bad: `w` is not in scope: declare it with `variable w`, or bind it");
    let src = "predicate P x\ntheorem bad:\n variable w\n assume e: exists x. P x\n lemma g:\n  variable v\n  assume p: P v\n  pw: P w by reit p\n  therefore forall v. P v -> P w\n k: P w by exists_e e g\n therefore forall w. (exists x. P x) -> P w";
    assert_eq!(err(src), "bad: this gives P v, not P w");
}

#[test]
fn one_rule_per_line() {
    let src = "theorem t:\n predicate A\n assume a: A\n b: A and A by and_i a (and_i a a)\n therefore A -> A and A";
    assert_eq!(err(src), "one rule per line: give `and_i` a line of its own");
}

#[test]
fn a_label_without_its_colon_is_pointed_at() {
    let src = "theorem t:\n predicate A\n assume a: A\n b: A by reit a\n c A by b\n therefore A -> A";
    assert_eq!(err(src), "`c` was read as an argument of the line above. If it is a label, it needs a colon: `c:`");
}

// ---- the negative examples, one function each: the source and what the checker says ----

/// `failure: line N: message`, as the command line prints it.
fn fail(src: &str) -> String {
    match hailperin::verify(src) {
        Ok(p) => panic!("accepted: {p:?}"),
        Err(e) => format!("failure: {e}"),
    }
}

#[test]
fn neg_check_missing_template() {
    let src = "-- A citation of a theorem passes a template for each of its predicates.\npredicate R x y\npredicate Q\ntheorem t:\n  predicate P x\n  lemma l:\n    variable x\n    assume h: P x\n    assume q: Q\n    therefore forall x. P x -> Q -> Q\n  therefore forall x. P x -> Q -> Q\ntheorem bad:\n  variable a\n  assume r: R a a\n  assume q: Q\n  k: Q by imp_e t r q\n  therefore forall a. R a a -> Q -> Q\n";
    assert_eq!(fail(src), "failure: line 16: bad: `t` takes a template for `P x`");
}

#[test]
fn neg_check_arity() {
    let src = "-- A predicate is used with the wrong number of arguments.\npredicate P x\ntheorem bad:\n  variable x y\n  assume h: P x\n  therefore forall x y. P x -> P x y\n";
    assert_eq!(fail(src), "failure: line 6: bad: `P` takes 1 argument(s), got 2");
}

#[test]
fn neg_check_auto() {
    let src = "-- `auto` is held for a tool that fills lines in. Until it runs, the line is unfilled.\ntheorem id:\n  predicate A\n  assume a: A\n  b: A by auto\n  therefore A -> A\n";
    assert_eq!(fail(src), "failure: line 5: id: `auto` marks a line for a tool to fill in, and this line is still unfilled");
}

#[test]
fn neg_check_auto_label() {
    let src = "theorem t:\n  predicate A\n  assume auto: A\n  b: A by auto\n  therefore A -> A\n";
    assert_eq!(fail(src), "failure: line 3: t: `auto` is a rule, so it can't be a label");
}

#[test]
fn neg_check_duplicate_theorem() {
    let src = "theorem twice:\n  predicate A\n  assume a: A\n  therefore A -> A\ntheorem twice:\n  predicate A\n  assume a: A\n  therefore A -> A\n";
    assert_eq!(fail(src), "failure: line 5: `twice` is already a theorem");
}

#[test]
fn neg_check_exists_e_shape() {
    let src = "-- The second line given to `exists_e` must be `forall w. A -> C`.\npredicate P x\npredicate Q\ntheorem bad:\n  assume e: exists x. P x\n  assume q: Q\n  k: Q by exists_e e q\n  therefore (exists x. P x) -> Q -> Q\n";
    assert_eq!(fail(src), "failure: line 7: bad: `exists_e` needs `forall x. A -> C`, and Q isn't one");
}

#[test]
fn neg_check_exists_e_witness() {
    let src = "-- The witness line's hypothesis must be the body of the `exists`.\npredicate P x\npredicate R x\npredicate Q\ntheorem bad:\n  assume e: exists x. P x\n  assume f: forall x. R x -> Q\n  k: Q by exists_e e f\n  therefore (exists x. P x) -> (forall x. R x -> Q) -> Q\n";
    assert_eq!(fail(src), "failure: line 8: bad: the witness line assumes R x, which isn't exists x. P x at `x`");
}

#[test]
fn neg_check_label_local() {
    let src = "-- A lemma's labels are local to it.\ntheorem bad:\n  predicate A\n  lemma l:\n    assume a: A\n    k: A by reit a\n    therefore A -> A\n  j: A by reit k\n  therefore A\n";
    assert_eq!(fail(src), "failure: line 8: bad: `k` was a line of lemma `l`, which has closed");
}

#[test]
fn neg_check_not_a_forall() {
    let src = "theorem bad:\n  predicate A\n  variable x\n  assume a: A\n  b: A by forall_e a x\n  therefore forall x. A -> A\n";
    assert_eq!(fail(src), "failure: line 5: bad: can't instantiate at `x`: A doesn't start with `forall`");
}

#[test]
fn neg_check_not_an_and() {
    let src = "theorem bad:\n  predicate A\n  predicate B\n  assume a: A or B\n  b: A by and_e a\n  therefore (A or B) -> A\n";
    assert_eq!(fail(src), "failure: line 5: bad: `and_e` needs an `and`, and A or B isn't one");
}

#[test]
fn neg_check_not_an_implication() {
    let src = "theorem bad:\n  predicate A\n  predicate B\n  assume a: A\n  assume b: B\n  c: B by imp_e a b\n  therefore A -> B -> B\n";
    assert_eq!(fail(src), "failure: line 6: bad: `a` is A, which is not an implication: `imp_e` takes the implication first, then its antecedents");
}

#[test]
fn neg_check_or_side() {
    let src = "theorem bad:\n  predicate A\n  predicate B\n  predicate C\n  assume a: A\n  b: B or C by or_i a\n  therefore A -> B or C\n";
    assert_eq!(fail(src), "failure: line 6: bad: A is not an alternative of B or C");
}

#[test]
fn neg_check_shadowing() {
    let src = "-- Names never meet: a label may not be a variable in scope.\npredicate P x\ntheorem bad:\n  variable x\n  assume x: P x\n  therefore forall x. P x -> P x\n";
    assert_eq!(fail(src), "failure: line 5: bad: `x` is a variable in scope, so it can't be a label");
}

#[test]
fn neg_check_template_arity() {
    let src = "-- A schema applied to a predicate of the wrong arity.\npredicate R x y\ndefine Ind (P x) = (forall x. P x) -> exists x. P x\ntheorem bad:\n  assume k: Ind R\n  therefore Ind R -> Ind R\n";
    assert_eq!(fail(src), "failure: line 5: bad: `Ind` needs a 1-place predicate for `P x`, and `R` has 2 places");
}

#[test]
fn neg_check_therefore_closes_assumptions() {
    let src = "-- A block's `therefore` closes every assumption the block opened.\ntheorem bad:\n  predicate A\n  lemma l:\n    assume a: A\n    therefore A\n  therefore A\n";
    assert_eq!(fail(src), "failure: line 6: bad: `a`, closed over `a`, gives A -> A, not A");
}

#[test]
fn neg_check_therefore_closes_variables() {
    let src = "-- A block's `therefore` closes every variable the block opened.\npredicate P x\ntheorem bad:\n  assume h: forall x. P x\n  lemma l:\n    variable x\n    px: P x by forall_e h x\n    therefore P x\n  therefore (forall x. P x) -> P x\n";
    assert_eq!(fail(src), "failure: line 8: bad: `px`, closed over `x`, gives forall x. P x, not P x");
}

#[test]
fn neg_check_undeclared_in_definition() {
    let src = "define Pair x y = exists p. In x p and In y p\n";
    assert_eq!(fail(src), "failure: line 1: `In` is not declared: add `predicate In x y` before this, or to the theorem");
}

#[test]
fn neg_check_undeclared_predicate() {
    let src = "-- Every predicate is declared before it is used.\ntheorem bad:\n  assume h: P\n  therefore P -> P\n";
    assert_eq!(fail(src), "failure: line 3: bad: `P` is not declared: add `predicate P` before this, or to the theorem");
}

#[test]
fn neg_check_variable_not_declared() {
    let src = "-- A variable is in scope only after `variable` declares it.\npredicate P x\ntheorem bad:\n  assume h: forall x. P x\n  px: P x by forall_e h x\n  therefore (forall x. P x) -> P x\n";
    assert_eq!(fail(src), "failure: line 5: bad: `x` is not in scope: declare it with `variable x`, or bind it");
}

#[test]
fn neg_check_witness_escape() {
    let src = "-- The conclusion of `exists_e` may not mention the witness.\npredicate P x\ntheorem bad:\n  variable w\n  assume e: exists x. P x\n  lemma g:\n    variable v\n    assume p: P v\n    therefore forall v. P v -> P v\n  k: P w by exists_e e g\n  therefore forall w. (exists x. P x) -> P w\n";
    assert_eq!(fail(src), "failure: line 10: bad: the conclusion mentions the witness `v`: P v");
}

#[test]
fn neg_check_wrong_conclusion() {
    let src = "-- The stated formula isn't a conjunct.\ntheorem bad:\n  predicate A\n  predicate B\n  predicate C\n  assume ab: A and B\n  c: C by and_e ab\n  therefore A and B -> C\n";
    assert_eq!(fail(src), "failure: line 7: bad: C is not a conjunct of A and B");
}

#[test]
fn neg_empty_something_exists() {
    let src = "-- Standard logic proves that something exists. Here it has to be a hypothesis.\ndefine True = absurd -> absurd\ntheorem something:\n  lemma t:\n    assume f: absurd\n    therefore True\n  e: exists x. True by exists_i t\n  therefore exists x. True\n";
    assert_eq!(fail(src), "failure: line 7: something: `exists_i` needs a witness, and no variable is in scope");
}

#[test]
fn neg_empty_textbook_forall_exists() {
    let src = "-- The textbook \"if everything is P, something is P\": nothing is in scope to point at.\npredicate P x\ntheorem textbook:\n  assume h: forall x. P x\n  e: exists x. P x by exists_i h\n  therefore (forall x. P x) -> exists x. P x\n";
    assert_eq!(fail(src), "failure: line 5: textbook: `exists_i` needs a witness, and no variable is in scope");
}

#[test]
fn neg_empty_vacuous_inst() {
    let src = "-- Dropping a vacuous `forall`: `forall_e` needs a variable, and there is none.\ntheorem vacuous:\n  predicate A\n  assume h: forall x. A\n  a: A by forall_e h\n  therefore (forall x. A) -> A\n";
    assert_eq!(fail(src), "failure: line 5: vacuous: `forall_e` takes a `forall` line, then the variables");
}

#[test]
fn neg_lex_not_ascii() {
    let src = "-- café\ntheorem t:\n  predicate A\n  assume a: A\n  therefore A -> A\n";
    assert_eq!(fail(src), "failure: line 1: files are ASCII, and this byte isn't");
}

#[test]
fn neg_lex_prime() {
    let src = "theorem t:\n  predicate A\n  assume a: A\n  a': A by a\n  therefore A -> A\n";
    assert_eq!(fail(src), "failure: line 4: `a'` is not a name: write `ap` or `a1` for a prime");
}

#[test]
fn neg_lex_qualified_name() {
    let src = "theorem t:\n  assume a: A.b\n  therefore A -> A\n";
    assert_eq!(fail(src), "failure: line 2: `A.` is not a formula: `.` only ends a quantifier's variables");
}

#[test]
fn neg_lex_trailing_underscore() {
    let src = "theorem t:\n  predicate A\n  assume a_: A\n  therefore A -> A\n";
    assert_eq!(fail(src), "failure: line 3: `a_` is not a name: an underscore needs a letter or digit after it");
}

#[test]
fn neg_lex_underscore_name() {
    let src = "-- A name starts with a letter.\ntheorem t:\n  predicate A\n  assume _a: A\n  therefore A -> A by _a\n";
    assert_eq!(fail(src), "failure: line 4: a name starts with a letter, not `_`");
}

#[test]
fn neg_lex_unexpected_character() {
    let src = "theorem t:\n  predicate A\n  assume a: A\n  b: A by imp_e a $ a\n  therefore A -> A\n";
    assert_eq!(fail(src), "failure: line 4: unexpected character `$`");
}

#[test]
fn neg_parse_declaration_late() {
    let src = "theorem t:\n  predicate A\n  assume a: A\n  k: A by reit a\n  assume b: A\n  therefore A -> A\n";
    assert_eq!(fail(src), "failure: line 5: declarations come before the steps of a block");
}

#[test]
fn neg_parse_lost_colon() {
    let src = "theorem t:\n  predicate A\n  assume a: A\n  b: A by reit a\n  c A by b\n  therefore A -> A\n";
    assert_eq!(fail(src), "failure: line 5: `c` was read as an argument of the line above. If it is a label, it needs a colon: `c:`");
}

#[test]
fn neg_parse_lowercase_formula() {
    let src = "theorem t:\n  assume a: a\n  therefore a -> a\n";
    assert_eq!(fail(src), "failure: line 2: `a` is lowercase, so it isn't a statement or predicate");
}

#[test]
fn neg_parse_name_needs_colon() {
    let src = "theorem t\n  predicate A\n  assume a: A\n  therefore A -> A\n";
    assert_eq!(fail(src), "failure: line 2: a theorem's name is followed by a colon, like every name that can be cited: `theorem t:`");
}

#[test]
fn neg_parse_missing_therefore() {
    let src = "theorem t:\n  predicate A\n  assume a: A\n  k: A by reit a\ntheorem u:\n  predicate A\n  assume a: A\n  therefore A -> A\n";
    assert_eq!(fail(src), "failure: line 4: the block `t` has no `therefore`");
}


#[test]
fn neg_parse_one_rule_per_line() {
    let src = "theorem t:\n  predicate A\n  predicate B\n  assume a: A\n  assume b: B\n  c: A and (A and B) by and_i a (and_i a b)\n  therefore A -> B -> A and (A and B)\n";
    assert_eq!(fail(src), "failure: line 6: one rule per line: give `and_i` a line of its own");
}

#[test]
fn neg_parse_section_order() {
    let src = "theorem t:\n  predicate A\n  assume a: A\n  variable x\n  therefore A -> A\n";
    assert_eq!(fail(src), "failure: line 4: `variable` lines come before `assume` lines in a block");
}

#[test]
fn neg_parse_therefore_takes_no_by() {
    let src = "theorem t:\n  predicate A\n  assume a: A\n  therefore A -> A by a\n";
    assert_eq!(fail(src), "failure: line 4: `therefore` takes no `by`: it closes the line right above it");
}

#[test]
fn neg_check_therefore_needs_a_line() {
    let src = "theorem t:\n  predicate A\n  variable x\n  therefore forall x. A\n";
    assert_eq!(fail(src), "failure: line 4: t: `therefore` closes the line right above it, and `t` has none");
}

#[test]
fn neg_check_by_names_a_rule() {
    let src = "theorem t:\n  predicate A\n  assume a: A\n  k: A by a\n  therefore A -> A\n";
    assert_eq!(fail(src), "failure: line 4: t: `by` names a rule first: `imp_e a ...` applies `a`, `reit a` restates it");
    let src = "predicate P x\ntheorem s:\n  variable y\n  assume a: P y\n  therefore forall y. P y -> P y\ntheorem t:\n  variable y\n  assume a: P y\n  k: P y by s a\n  therefore forall y. P y -> P y\n";
    assert_eq!(fail(src), "failure: line 9: t: `by` names a rule first: `imp_e s ...` applies `s`, `reit s` restates it");
}

/// Every theorem is a logical validity: an assumed axiom is discharged like any assumption, so
/// it is in the statement, and a citation supplies it.
#[test]
fn axioms_are_assumptions() {
    let src = "predicate P x\npredicate Q x\ndefine Ax = forall x. P x -> Q x\n\
        theorem t:\n assume ax: Ax\n lemma l:\n  variable x\n  assume p: P x\n  q: Q x by imp_e ax p\n  therefore forall x. P x -> Q x\n therefore Ax -> forall x. P x -> Q x\n\
        theorem u:\n variable y\n assume ax: Ax\n assume p: P y\n q: Q y by imp_e t ax p\n therefore forall y. Ax -> P y -> Q y";
    // Messages print an instance of a definition by its name.
    assert_eq!(ok(src), ["t: Ax -> Ax", "u: forall y. Ax -> P y -> Q y"]);
    // The statement must say what was assumed.
    let src = "predicate P x\npredicate Q x\ndefine Ax = forall x. P x -> Q x\n\
        theorem t:\n assume ax: Ax\n lemma l:\n  variable x\n  assume p: P x\n  q: Q x by imp_e ax p\n  therefore forall x. P x -> Q x\n therefore forall x. P x -> Q x";
    assert!(err(src).starts_with("t: `l`, closed over `ax`, gives"));
    // A citation has to supply it.
    let src = "predicate P x\npredicate Q x\ndefine Ax = forall x. P x -> Q x\n\
        theorem t:\n assume ax: Ax\n lemma l:\n  variable x\n  assume p: P x\n  q: Q x by imp_e ax p\n  therefore forall x. P x -> Q x\n therefore Ax -> forall x. P x -> Q x\n\
        theorem u:\n variable y\n assume p: P y\n q: Q y by imp_e t p\n therefore forall y. P y -> Q y";
    assert!(err(src).ends_with("but got P y"), "{}", err(src));
}

/// A schema is a definition with a predicate parameter, and a theorem assumes the instances it
/// uses. An instance that mentions a lemma's variable is assumed closed, and instantiated.
#[test]
fn schemas_are_definitions() {
    let src = "predicate P x\npredicate R x y\ndefine Ind (S x) = (forall x. S x) -> exists x. S x\n\
        theorem t:\n assume ind: forall y. Ind (R y)\n lemma l:\n  variable y\n  i: Ind (R y) by forall_e ind y\n  therefore forall y. Ind (R y)\n therefore (forall y. Ind (R y)) -> forall y. Ind (R y)";
    assert_eq!(ok(src).len(), 1);
}

/// Closing weakens a line under the block's assumptions, together with the variables they
/// mention, even when those variables belong to an outer block.
#[test]
fn closing_weakens_under_outer_variables() {
    let src = "predicate P x\npredicate A\ntheorem t:\n  variable w\n  lemma k:\n    assume a: A\n    assume p: P w\n    r: A by reit a\n    therefore A -> P w -> A\n  therefore forall w. A -> P w -> A\n";
    assert_eq!(ok(src), ["t: forall w. A -> P w -> A"]);
}

/// Modus ponens with nothing open reports in the file's syntax, like everywhere else.
#[test]
fn neg_check_mp_at_top() {
    let src = "predicate A\npredicate B\ntheorem s:\n  assume a: A and B\n  r: A by and_e a\n  therefore A and B -> A\ntheorem e:\n  assume a: B\n  therefore B -> B\ntheorem t:\n  k: A by imp_e s e\n  therefore A\n";
    assert_eq!(fail(src), "failure: line 11: t: A and B -> A needs A and B, but got B -> B");
}

/// `exists_e` takes the `exists` first: the message says so when the two are swapped.
#[test]
fn neg_check_exists_e_order() {
    let src = "predicate P x\ntheorem t:\n  assume e: exists x. P x\n  lemma c:\n    variable x\n    assume p: P x\n    k: exists y. P y by exists_i p\n    therefore forall x. P x -> exists y. P y\n  r: exists y. P y by exists_e c e\n  therefore (exists x. P x) -> exists y. P y\n";
    assert_eq!(fail(src), "failure: line 9: t: `c` is forall x. P x -> exists y. P y, which is not an `exists`: `exists_e` takes the `exists` first, then the lemma");
}

/// A misspelled rule, line or theorem gets a suggestion, when one name is close.
#[test]
fn neg_check_did_you_mean() {
    let src = "predicate A\ntheorem t:\n  assume a: A\n  b: A by riet a\n  therefore A -> A\n";
    assert_eq!(fail(src), "failure: line 4: t: `riet` is not a rule, a line here, or a theorem: did you mean `reit`?");
    let src = "predicate A\ntheorem lemma_one:\n  assume a: A\n  therefore A -> A\ntheorem t:\n  assume a: A\n  b: A by imp_e lemma_on a\n  therefore A -> A\n";
    assert_eq!(fail(src), "failure: line 7: t: `lemma_on` is not a line or a theorem here: did you mean `lemma_one`?");
}

/// A cited theorem takes its lines, then variables for what is left.
#[test]
fn theorem_citation_takes_variables() {
    let src = "predicate P x\npredicate Q\n\
        theorem t:\n assume q: Q\n assume a: forall x. P x\n therefore Q -> (forall x. P x) -> forall x. P x\n\
        theorem u:\n variable y\n assume q: Q\n assume a: forall x. P x\n k: P y by imp_e t q a y\n therefore forall y. Q -> (forall x. P x) -> P y";
    assert_eq!(ok(src).len(), 2);
}

/// `therefore` closes the line right above it, so an earlier line is brought down with `reit`.
#[test]
fn reit_brings_a_line_down() {
    let src = "theorem k:\n predicate A\n predicate B\n assume a: A\n assume b: B\n r: A by reit a\n therefore A -> B -> A";
    assert_eq!(ok(src), ["k: A -> B -> A"]);
    let src = "theorem k:\n predicate A\n predicate B\n assume a: A\n assume b: B\n therefore A -> B -> A";
    assert_eq!(err(src), "k: `b`, closed over `a` and `b`, gives A -> B -> B, not A -> B -> A");
}

#[test]
fn neg_parse_unbalanced_paren() {
    let src = "theorem t:\n  predicate A\n  predicate B\n  assume a: (A -> B\n  therefore A\n";
    assert_eq!(fail(src), "failure: line 4: this `(` has no `)`");
}

/// The import cases need files: each is written to a scratch directory, then checked there.
#[test]
fn neg_imports() {
    let dir = std::env::temp_dir().join(format!("hailperin-neg-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let files: &[(&str, &str)] = &[
        ("import_broken", "-- Importing a file that doesn't check reports the failure in that file.\nimport parse_missing_colon\n"),
        ("import_cycle_a", "import import_cycle_b\n"),
        ("import_cycle_b", "import import_cycle_a\n"),
        ("import_late", "theorem t:\n  predicate A\n  assume a: A\n  therefore A -> A\nimport q\n"),
        ("import_missing", "import nonexistent\n"),
        ("import_self", "import import_self\n"),
        ("parse_missing_colon", "theorem t\n  predicate A\n  assume a: A\n  therefore A -> A\n"),
    ];
    for (name, src) in files {
        std::fs::write(dir.join(format!("{name}.hai")), src).unwrap();
    }
    let check = |name: &str| -> String {
        let path = dir.join(format!("{name}.hai"));
        let src = std::fs::read_to_string(&path).unwrap();
        match hailperin::verify_in(&src, &dir, Some(&path), &mut |_, _| {}) {
            Ok(()) => panic!("{name}: accepted"),
            Err(e) => format!("failure: {e}"),
        }
    };
    assert_eq!(check("import_broken"), "failure: parse_missing_colon.hai: line 2: a theorem's name is followed by a colon, like every name that can be cited: `theorem t:`");
    assert_eq!(check("import_cycle_a"), "failure: import_cycle_b.hai: line 1: import cycle: import_cycle_a -> import_cycle_b -> import_cycle_a");
    assert_eq!(check("import_cycle_b"), "failure: import_cycle_a.hai: line 1: import cycle: import_cycle_b -> import_cycle_a -> import_cycle_b");
    assert_eq!(check("import_late"), "failure: line 5: imports come before everything else");
    assert_eq!(check("import_missing"), "failure: line 1: can't import `nonexistent`: No such file or directory (os error 2)");
    assert_eq!(check("import_self"), "failure: line 1: import cycle: import_self -> import_self");
    std::fs::remove_dir_all(&dir).unwrap();
}

/// Paths are relative to the importing file, `.` and `..` included, and a file reached by two
/// spellings is still loaded once.
#[test]
fn imports_across_directories() {
    let dir = std::env::temp_dir().join(format!("hailperin-paths-{}", std::process::id()));
    std::fs::create_dir_all(dir.join("sub/deep")).unwrap();
    let files: &[(&str, &str)] = &[
        ("base", "predicate P x\n"),
        ("sub/a", "import ../base\ndefine A = forall x. P x\n"),
        ("sub/deep/b", "import ../a\nimport ../../base\ntheorem t:\n  variable x\n  assume ax: A\n  r: P x by forall_e ax x\n  therefore forall x. A -> P x\n"),
        ("top", "import sub/a\nimport ./sub/../base\nimport sub/deep/b\n"),
        ("sub/x", "import ../y\n"),
        ("y", "import sub/x\n"),
    ];
    for (name, src) in files {
        std::fs::write(dir.join(format!("{name}.hai")), src).unwrap();
    }
    let check = |name: &str| {
        let path = dir.join(format!("{name}.hai"));
        let src = std::fs::read_to_string(&path).unwrap();
        hailperin::verify_in(&src, path.parent().unwrap(), Some(&path), &mut |_, _| {})
    };
    assert!(check("top").is_ok());
    assert!(check("sub/deep/b").is_ok());
    assert!(check("y").unwrap_err().msg.starts_with("import cycle: "));
    std::fs::remove_dir_all(&dir).unwrap();
}

#[test]
fn keyword_as_label() {
    let src = "predicate P x\ntheorem t:\n  variable x\n  assume by: P x\n  therefore forall x. P x -> P x\n";
    assert_eq!(fail(src), "failure: line 4: expected the assumption's label, and `by` is a keyword");
}

#[test]
fn nothing_shadows() {
    // A binder may not reuse a variable in scope, an enclosing binder, a parameter or a label.
    let src = "predicate P x y\ntheorem t:\n  variable k k1\n  assume h: P k1 k\n  e: exists k k1. P k k1 by exists_i h\n  therefore forall k k1. P k1 k -> exists k k1. P k k1\n";
    assert_eq!(err(src), "t: `k` is already a variable in scope");
    assert_eq!(err("predicate P x\ndefine D = forall x. exists x. P x"), "`x` is already bound here");
    assert_eq!(err("predicate P x\ndefine D = forall x x. P x"), "`x` is already bound here");
    assert_eq!(err("predicate P x\ndefine D y = forall y. P y"), "`y` is already a parameter of this definition");
    let src = "predicate P x\ntheorem t:\n  assume h: forall x. P x\n  j: forall x. P x by reit h\n  k: forall j. P j by reit h\n  therefore (forall x. P x) -> forall x. P x\n";
    assert_eq!(err(src), "t: `j` is a label here, so it can't be a variable");
    // A line's own label counts.
    let src = "predicate P x\ntheorem t:\n  assume h: forall x. P x\n  k: forall k. P k by reit h\n  therefore (forall x. P x) -> forall x. P x\n";
    assert_eq!(err(src), "t: `k` is a label here, so it can't be a variable");
    // A `therefore` restates the variables its block closes.
    let src = "predicate P x\ntheorem t:\n  variable a\n  assume h: P a\n  therefore forall a. P a -> P a\n";
    ok(src);
}

#[test]
fn templates_are_named_only_with_arguments() {
    let pre = "predicate Q x\npredicate R x y\ntheorem t:\n predicate P x\n variable a\n assume p: P a\n therefore forall a. P a -> P a\n";
    let cite = |by: &str| format!("{pre}theorem bad:\n variable a b\n assume q: Q a\n k: Q a by {by}\n therefore forall a b. Q a -> Q a");
    assert_eq!(err(&cite("imp_e t (Q) q")), "`Q` has no arguments, so it goes without parentheses: `Q`");
    assert_eq!(err(&cite("imp_e (t Q) q")), "a theorem's templates follow its name, without parentheses: `t T`");
    assert_eq!(err(&cite("imp_e t (R a b) q")), "bad: `t` needs a 1-place predicate for `P x`, and `R a b` leaves no places");
    assert_eq!(err(&cite("imp_e t (Q a and Q b) q")), "bad: `t` needs a 1-place predicate for `P x`, and a compound formula has no places: define it, then pass the definition");
    assert_eq!(err("define D (A) = A"), "`A` has no placeholders, so it goes without parentheses: `A`");
    assert_eq!(err("predicate Q x\ndefine D (Q x) = forall a. Q a"), "`Q` is already declared, so it can't be a parameter");
}

#[test]
fn only_theorems_declare_predicates() {
    let src = "predicate Q x\ntheorem u:\n variable a\n assume q: Q a\n lemma l:\n  predicate P x\n  variable b\n  assume p: P b\n  therefore forall b. P b -> P b\n therefore forall a. Q a -> Q a";
    assert_eq!(err(src), "a lemma declares no predicates: declare `P` in its theorem");
}

#[test]
fn templates_after_a_name_that_is_not_a_theorem() {
    let pre = "predicate Q x\ntheorem t:\n predicate P x\n variable a\n assume p: P a\n therefore forall a. P a -> P a\n";
    let cite = |by: &str| format!("{pre}theorem use:\n variable a\n assume q: Q a\n k: Q a by {by}\n therefore forall a. Q a -> Q a");
    assert_eq!(err(&cite("imp_e q Q")), "use: `q` is a line, and only a theorem takes templates");
    assert_eq!(err(&cite("imp_e a Q q")), "use: `a` is a variable, and only a theorem takes templates");
    assert_eq!(err(&cite("imp_e tt Q q")), "use: `tt` is not a theorem: did you mean `t`?");
}

#[test]
fn an_unclosed_paren_is_pointed_at() {
    let src = "predicate Q x\ntheorem t:\n variable a\n assume q: Q a\n k: Q a by imp_e t (Q a q\n therefore forall a. Q a -> Q a";
    let e = hailperin::verify(src).unwrap_err();
    assert_eq!((e.line, e.msg.as_str()), (5, "this `(` has no `)`"));
}
