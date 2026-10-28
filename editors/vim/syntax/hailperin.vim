" Hailperin proof files. As a package: ~/.vim/pack/hailperin/start/hailperin, holding this
" directory's contents.
if exists('b:current_syntax')
  finish
endif

" Vim's own defaults while this file loads, whatever 'compatible' and 'cpoptions' are.
let s:cpo_save = &cpo
set cpo&vim

syn keyword hailperinKeyword theorem lemma define import predicate variable assume therefore by
syn keyword hailperinLogical forall exists and or not absurd
syn keyword hailperinRule imp_e and_i and_e or_i or_e absurd_e forall_e exists_i exists_e reit auto
syn match hailperinArrow '->'
syn match hailperinName '\<[A-Z][A-Za-z0-9_]*\>'
syn match hailperinLabel '\<[a-z][A-Za-z0-9_]*\ze\s*:'
syn match hailperinComment '--.*$'

hi def link hailperinKeyword Keyword
hi def link hailperinLogical Operator
hi def link hailperinRule Function
hi def link hailperinArrow Operator
hi def link hailperinName Type
hi def link hailperinLabel Identifier
hi def link hailperinComment Comment

let b:current_syntax = 'hailperin'

let &cpo = s:cpo_save
unlet s:cpo_save
