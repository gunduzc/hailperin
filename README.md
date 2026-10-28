# Hailperin

Hailperin is a small proof checker characterizing intuitionistic and universally free first-order logic. It's (supposed to be) complete the way classical first-order logic is.

I wanted to write a proof assistant that expresses any logically valid proof. That I could also learn in its entirety. (Source-bootstrappable version in C99 possibly coming soon.)

However, when I first designed it, I noticed that `forall x. P x` implied `exists x. P x`, and I thought to myself, what if `forall x. P x` was vacuously true?

I didn't realize at the moment that for `forall x. P x` to be vacuously true, no constants (i.e. literally nothing) would have to exist. But I kept thinking about it, searching about what's known, looking for answers.

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

The result is this repository.

One small limitation is that while it allows axiom schemas, there is no way to restrict axiom schemas by the properties of the predicate.

Which means the traditional presentations of some finitely axiomatized theories like $ACA_0$ and $I\Sigma_1$ are unavailable, and so are the traditional presentations of some infinitely axiomatized theories like PRA.

Systems that possess this property would require serious arithmetization work. (Or you could apply Goedel's trick that transforms ZFC into NBG, but I'm not entirely sure how.)

But they're possible, and I'm willing to bet that one day, it will be fun to make them happen.

As a result of this limitation, the theories I recommend you work in are those that are either naturally finitely axiomatized or those that are infinitely axiomatized without restricted predicates.

HF is a good choice, because it has no trouble expressing syntax and has a known proof theoretic ordinal (and a tiny, uncontroversial one at that), and proves the same theorems PA proves.

Other theories I would recommend are ZFC, NBG, IZF, HA, PA... you get the idea. The usual bunch. Presburger arithmetic and Morse-Kelley are also possible.

Quine's NF is also there, and thanks to Hailperin, the logician, it's finitely axiomatized! Isn't that nice?

Q also presents very naturally in Hailperin for those who like living life in higher difficulty settings.

Anyway.

I hope you enjoy Hailperin. I certainly did.

## Flagship proofs

- Diaconescu's theorem: choice implies excluded middle, over an intuitionistic core of ZF ([diaconescu.hai](examples/diaconescu.hai))
- Foundation implies excluded middle ([zfc.hai](examples/zfc.hai), `em_from_foundation`)
- Russell's paradox in pure logic: for any relation, nothing has exactly the non-self-members as members ([russell.hai](examples/russell.hai), `russell`)
- Cantor's theorem: no function from a set onto its subsets, by the diagonal set ([cantor.hai](examples/cantor.hai), `cantor`)
- Commutativity of addition in Peano arithmetic, with relations instead of functions ([plus_comm.hai](examples/plus_comm.hai))
- A universal set in New Foundations, from Hailperin's finite axiomatization ([nf.hai](examples/nf.hai), `universe`)

## Usage

```
cargo run --release -- examples/socrates.hai            # prints `success`
cargo run --release -- - < file.hai                      # reads standard input
cargo run --release -- fmt examples/socrates.hai        # the canonical layout (--indent, --continue, --width, --by, --scope)
cargo run --release -- explain examples/socrates.hai    # each line's scope and formula
cargo test
```

Exit codes: `0` success, `1` failure (`failure: line N: ...`), `2` usage error.

Syntax highlighting for [bat](https://github.com/sharkdp/bat):

```
cp editors/hailperin.sublime-syntax ~/.config/bat/syntaxes/ && bat cache --build
export BAT_THEME=ansi    # the terminal's own colours, so it reads on light and dark alike
```

## Editors

Formatting runs `hailperin fmt`, so put the checker on your path first: `cargo install --path .`

Vim, with highlighting, indentation the way `fmt` lays a file out, and `:HailperinFmt` for the whole buffer. Neovim reads the same files, from `~/.local/share/nvim/site/pack/` instead.

```
mkdir -p ~/.vim/pack/hailperin/start && cp -r editors/vim ~/.vim/pack/hailperin/start/hailperin
```

nano, for highlighting:

```
echo "include \"$PWD/editors/hailperin.nanorc\"" >> ~/.nanorc
```

VS Code, with Format Document and indentation as you type. The package builds without Node:

```
python3 editors/vscode/vsix.py && code --install-extension editors/vscode/hailperin-0.1.0.vsix
```

Tree-sitter, for Helix, Zed and Neovim: the grammar is in [editors/tree-sitter-hailperin](editors/tree-sitter-hailperin), with the generated parser in `src/` and the highlighting and indentation queries in `queries/`.

The language is described in [SPEC.md](SPEC.md); more examples are in [examples/](examples/).
