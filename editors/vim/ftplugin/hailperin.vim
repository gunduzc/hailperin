" Hailperin proof files: two spaces per level, `--` comments, and `:HailperinFmt` to lay out
" the whole buffer with `hailperin fmt`.
if exists('b:did_ftplugin')
  finish
endif
let b:did_ftplugin = 1

" Vim's own defaults while this file loads, whatever 'compatible' and 'cpoptions' are.
let s:cpo_save = &cpo
set cpo&vim

setlocal shiftwidth=2 softtabstop=2 expandtab
setlocal comments=:-- commentstring=--\ %s

if !exists('g:hailperin_cmd')
  let g:hailperin_cmd = 'hailperin'
endif

" The whole buffer: fmt aligns columns across a file, so a part can't be formatted alone.
function! s:Fmt() abort
  let view = winsaveview()
  let out = systemlist(g:hailperin_cmd . ' fmt -', getline(1, '$'))
  if v:shell_error
    echohl ErrorMsg | echo join(out, ' ') | echohl None
  else
    call setline(1, out)
    if line('$') > len(out)
      silent execute (len(out) + 1) . ',$delete _'
    endif
  endif
  call winrestview(view)
endfunction
command! -buffer HailperinFmt call s:Fmt()

let b:undo_ftplugin = 'setlocal shiftwidth< softtabstop< expandtab< comments< commentstring< | delcommand HailperinFmt'

let &cpo = s:cpo_save
unlet s:cpo_save
