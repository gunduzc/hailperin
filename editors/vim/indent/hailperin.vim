" Hailperin indentation, as `hailperin fmt` lays it out: a block one level in, the line after a
" finished `therefore` one level out, the rest of an item two levels past its start, and a `by`
" on its own line in the column of the `by` above.
if exists('b:did_indent')
  finish
endif
let b:did_indent = 1

" Vim's own defaults while this file loads, whatever 'compatible' and 'cpoptions' are.
let s:cpo_save = &cpo
set cpo&vim

setlocal indentexpr=HailperinIndent(v:lnum) autoindent
setlocal indentkeys=o,O,!^F,0=therefore,0=by

" Whether a line starts an item: a label, a keyword that opens one, or a comment.
function! s:StartsItem(line) abort
  return a:line =~# '^\s*\([a-z][A-Za-z0-9_]*\s*:\|--\|\(theorem\|lemma\|define\|import\|predicate\|variable\|assume\|therefore\)\>\)'
endfunction

" Whether a line, without its comment, leaves its formula unfinished.
function! s:Unfinished(line) abort
  let code = substitute(a:line, '\s*--.*$', '', '')
  let open = len(substitute(code, '[^(]', '', 'g')) - len(substitute(code, '[^)]', '', 'g'))
  return code =~# '\(->\|\<and\|\<or\|\<not\|\.\)\s*$' || open > 0
endfunction

" The first line of the item a line belongs to.
function! s:ItemStart(lnum) abort
  let lnum = a:lnum
  while lnum > 1 && !s:StartsItem(getline(lnum))
    let lnum = prevnonblank(lnum - 1)
  endwhile
  return lnum
endfunction

" The column of the nearest `by` after other text among the items indented `base` around `lnum`,
" above it first, then below: the segment's column, as fmt sets it.
function! s:ByColumn(lnum, base) abort
  for step in [-1, 1]
    let lnum = a:lnum + step
    while lnum > 0 && lnum <= line('$')
      if getline(lnum) =~# '\S'
        let indent = indent(s:ItemStart(lnum))
        " A lemma in the same block starts another segment, with its own column.
        if indent < a:base || indent == a:base && getline(lnum) =~# '^\s*lemma\>'
          break
        endif
        let col = match(getline(lnum), '\S\s\+\zsby\>')
        if col >= 0 && indent == a:base
          return col
        endif
      endif
      let lnum += step
    endwhile
  endfor
  return -1
endfunction

function! HailperinIndent(lnum) abort
  let prev = prevnonblank(a:lnum - 1)
  let line = getline(a:lnum)
  if prev == 0 || line =~# '^\s*\(theorem\|define\|import\)\>'
    return 0
  endif
  let start = s:ItemStart(prev)
  let base = indent(start)
  " A line that doesn't start an item goes on with the one above. On a fresh line, only an
  " unfinished formula says so.
  let goes_on = line =~# '\S' ? !s:StartsItem(line) : s:Unfinished(getline(prev))
  if goes_on
    let by = line =~# '^\s*by\>' ? s:ByColumn(a:lnum, base) : -1
    return by >= 0 ? by : base + 2 * shiftwidth()
  endif
  let first = getline(start)
  if first =~# '^\s*\(theorem\|lemma\)\>.*:\s*\(--.*\)\=$'
    return base + shiftwidth()
  endif
  if first =~# '^\s*therefore\>'
    return max([base - shiftwidth(), 0])
  endif
  return base
endfunction

let &cpo = s:cpo_save
unlet s:cpo_save
