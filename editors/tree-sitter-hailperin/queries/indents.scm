; Indentation in Neovim's capture names. A block's lines go one level in. The rest of an item
; goes one level past its start, where `hailperin fmt` puts two, and a `by` on its own line is
; not put in its segment's column: format with `hailperin fmt -` for the exact layout, or use
; editors/vim/indent/hailperin.vim, which Neovim reads too and which is exact.

[(theorem) (lemma)] @indent.begin
[(step) (assumption) (therefore) (definition)] @indent.begin
