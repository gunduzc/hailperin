(comment) @comment

["theorem" "lemma" "define" "import" "predicate" "variable" "assume" "therefore" "by"] @keyword
["forall" "exists" "and" "or" "not" "absurd"] @keyword.operator
"->" @operator
(rule) @function.builtin

(upper_name) @type
(theorem name: (lower_name) @function)
(lemma name: (lower_name) @function)
(step label: (lower_name) @label)
(assumption label: (lower_name) @label)
(path) @string.special

["(" ")"] @punctuation.bracket
[":" "." "="] @punctuation.delimiter
