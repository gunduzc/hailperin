// Tree-sitter grammar for Hailperin, after the grammar in SPEC.md. It is lenient where the
// checker is strict: a block's declarations, steps and lemmas may come in any order, so that a
// file being edited still highlights and indents.

const RULES = ['imp_e', 'and_i', 'and_e', 'or_i', 'or_e', 'absurd_e', 'forall_e', 'exists_i', 'exists_e', 'reit', 'auto'];

module.exports = grammar({
  name: 'hailperin',
  word: $ => $.lower_name,
  extras: $ => [/\s/, $.comment],
  conflicts: $ => [[$.justification], [$.atom], [$.predicate], [$.variable]],

  rules: {
    source_file: $ => seq(repeat($.import), repeat(choice($.predicate, $.definition, $.theorem))),

    comment: $ => token(seq('--', /.*/)),
    upper_name: $ => /[A-Z][A-Za-z0-9_]*/,
    lower_name: $ => /[a-z][A-Za-z0-9_]*/,
    path: $ => /(\.\.?|[a-z][A-Za-z0-9_]*)(\/(\.\.?|[a-z][A-Za-z0-9_]*))*/,

    import: $ => seq('import', field('path', $.path)),
    predicate: $ => seq('predicate', field('name', $.upper_name), repeat($.lower_name)),
    definition: $ => seq('define', field('name', $.upper_name), repeat($.parameter), '=', field('body', $._formula)),
    parameter: $ => choice(seq('(', $.upper_name, repeat1($.lower_name), ')'), $.upper_name, $.lower_name),

    theorem: $ => seq('theorem', field('name', $.lower_name), ':', repeat($.predicate), $._block),
    lemma: $ => seq('lemma', field('name', $.lower_name), ':', $._block),
    _block: $ => seq(repeat(choice($.variable, $.assumption, $.step, $.lemma)), $.therefore),

    variable: $ => seq('variable', repeat1($.lower_name)),
    assumption: $ => seq('assume', field('label', $.lower_name), ':', field('formula', $._formula)),
    step: $ => seq(field('label', $.lower_name), ':', field('formula', $._formula), 'by', $.justification),
    therefore: $ => seq('therefore', field('formula', $._formula)),

    justification: $ => seq($.rule, repeat($.argument)),
    rule: $ => choice(...RULES),
    argument: $ => seq($.lower_name, repeat($._template)),
    _template: $ => choice($.upper_name, seq('(', $._formula, ')')),

    _formula: $ => choice($.quantified, $.implication, $.disjunction, $.conjunction, $.negation, $._operand),
    quantified: $ => prec.right(0, seq(choice('forall', 'exists'), repeat1($.lower_name), '.', $._formula)),
    implication: $ => prec.right(1, seq($._formula, '->', $._formula)),
    disjunction: $ => prec.right(2, seq($._formula, 'or', $._formula)),
    conjunction: $ => prec.right(3, seq($._formula, 'and', $._formula)),
    negation: $ => prec(4, seq('not', $._formula)),
    _operand: $ => choice($.atom, 'absurd', seq('(', $._formula, ')')),
    atom: $ => seq($.upper_name, repeat(choice($.lower_name, $.upper_name, seq('(', $._formula, ')')))),
  },
});
