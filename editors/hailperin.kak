# Hailperin proof files for Kakoune. Add `source /path/to/hailperin.kak` to
# your kakrc. `:format` runs `hailperin fmt` on the whole buffer (fmt aligns
# columns across a file, so a part can't be formatted alone), `:lint` runs the
# checker; options for `fmt` go on the formatcmd line, before the `-`.

hook global BufCreate .*\.hai %{ set-option buffer filetype hailperin }

hook global WinSetOption filetype=hailperin %{
  require-module hailperin
  add-highlighter window/hailperin ref hailperin
  set-option window comment_line '--'
  set-option window indentwidth 2
  set-option window formatcmd 'hailperin fmt -'
  set-option window lintcmd 'hailperin --lint'
  hook -once -always window WinSetOption filetype=.* %{ remove-highlighter window/hailperin }
}

provide-module hailperin %{
  add-highlighter shared/hailperin regions
  add-highlighter shared/hailperin/code default-region group
  add-highlighter shared/hailperin/comment region -- $ fill comment

  add-highlighter shared/hailperin/code/ regex \b[A-Z][A-Za-z0-9_]*\b 0:type
  add-highlighter shared/hailperin/code/ regex (\b[a-z][A-Za-z0-9_]*)\s*: 1:variable
  add-highlighter shared/hailperin/code/ regex \b(theorem|lemma|define|import|predicate|variable|assume|therefore|by)\b 0:keyword
  add-highlighter shared/hailperin/code/ regex \b(forall|exists|and|or|not|absurd)\b 0:operator
  add-highlighter shared/hailperin/code/ regex [-]> 0:operator
  add-highlighter shared/hailperin/code/ regex \b(imp_e|and_i|and_e|or_i|or_e|absurd_e|forall_e|exists_i|exists_e|reit|auto)\b 0:builtin
}
