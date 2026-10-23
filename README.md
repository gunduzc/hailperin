# Hailperin

Hailperin is a small proof checker characterizing intuitionistic and universally free first-order logic. It's (supposed to be) complete the way classical first-order logic is.

I wanted to write a proof assistant that expresses any logically valid proof. That I could also learn in its entirety. (Source-bootstrappable version in C99 possibly coming soon.)

However, when I first designed it, I noticed that `forall x (P x)` implied `exists x (P x)`, and I thought to myself, what if `forall x (P x)` was vacuously true?

I didn't realize at the moment that for `forall x (P x)` to be vacuously true, no constants (i.e. literally nothing) would have to exist. But I kept thinking about it, searching about what's known, looking for answers.

To gain some understanding, I thought of the titular "Socrates is mortal" proof, in FOL.

```
#1 Person x -> Mortal x by hypothesis
#2 Person socrates by hypothesis
#3 Mortal socrates by #1, #2
```

Eventually, to accommodate a setting where no constants could exist, I could just do *this*, courtesy of Hailperin, the logician:

```
#1 Socrates x -> Person x by hypothesis
#2 Person x -> Mortal x by hypothesis
#3 Socrates x -> Mortal x by #1, #2
```

And I thought that was *super fun*. Technically, anything that qualified as Socrates would be mortal, and the bonus would be that if *nothing at all existed*, the proof would still hold. And I thought that was interesting.

Here's how it would work in this small checker:

```
let Socrates x
let Person x
let Mortal x

proof socrates_is_mortal
  given socrates_person : forall x $ imp (Socrates x) (Person x)
  given mortality : forall x $ imp (Person x) (Mortal x)
  shows forall x $ imp (Socrates x) (Mortal x) by
    forall x {
      have sp : imp (Socrates x) (Person x) by socrates_person x
      have pm : imp (Person x) (Mortal x) by mortality x
      shows imp (Socrates x) (Mortal x) by assume s : Socrates x { pm (sp s) } }
```

The result is this repository.

It technically doesn't allow infinite axiomatization or axiom schemas anywhere.

Systems that are infinitely axiomatized (or systems that are only finitely axiomatizable via coding) would require serious arithmetization.

But they're possible, and I'm willing to bet that one day, it will be fun to make them happen.

You have two workarounds for that purpose. The first is, you can assert the instances of the schemas you want individually, but that's clunky. I'd only recommend it if you wanted to comfortably define coding in the first place.

The second is, you could just prefer to go for a naturally finitely axiomatized theory. NBG and NF are fun options. NF's finite axiomatization is also courtesy of Hailperin, the awesome logician who made all of this possible.

Q also presents very naturally in Hailperin for those who like living life in higher difficulty settings.

I hope you enjoy Hailperin. I certainly did.

## Flagship proofs

- Diaconescu's theorem: choice implies excluded middle, over an intuitionistic core of ZF ([zfc.hai](examples/zfc.hai), `diaconescu`)
- Foundation implies excluded middle ([zfc.hai](examples/zfc.hai), `em_from_foundation`)
- Tarski's undefinability of truth, from the diagonal lemma as a hypothesis ([tarski.hai](examples/tarski.hai))
- Russell's paradox: there is no set of all sets ([zfc.hai](examples/zfc.hai), `russell`)
- Commutativity of addition in Peano arithmetic, with relations instead of functions ([plus_comm.hai](examples/plus_comm.hai))
- A universal set in New Foundations, from Hailperin's finite axiomatization ([nf.hai](examples/nf.hai), `universe`)
- $\in$-induction from adduction in intuitionistic hereditarily finite set theory ([hf.hai](examples/hf.hai), `eps_induction`)

## Usage

```
cargo run --release -- examples/socrates.hai    # prints `success`
cargo run --release -- - < file.hai              # reads standard input
cargo test
```

Exit codes: `0` success, `1` failure (`failure: line N: ...`), `2` usage error.

Syntax highlighting for [bat](https://github.com/sharkdp/bat):

```
cp editors/hailperin.sublime-syntax ~/.config/bat/syntaxes/ && bat cache --build
```

The language is described in [SPEC.md](SPEC.md); more examples are in [examples/](examples/).
