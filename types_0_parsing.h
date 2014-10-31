type AmberSymb  = left(ParType),
                  right(ParType),
                  comma,
                  semicolon,
                  question_mark,
                  equals,
                  pipe,
                  colon,
                  underscore,
                  circumflex,
                  dot,
                  tilde,
                  at,
                  ampersand,
                  bang,
                  hash,
                  dollar,
                  lower,
                  greater,
                  plus,
                  minus,
                  asterisk,
                  slash,
                  double_dot,
                  double_equals,
                  not_equal,
                  lower_eq,
                  greater_eq,
                  assign,
                  double_colon,
                  right_arrow,
                  double_right_arrow,
                  left_arrow,
                  //double_left_arrow, //????????
                  logical_or_operator,
                  triple_dot;

type PlainToken = AmberSymb,
                  lowercase_id(Atom),
                  mixedcase_id(Atom),
                  uppercase_id(Atom),
                  qualified_symbol(Atom),
                  label(Atom),
                  Int,
                  String,
                  Char,
                  operator(Operator),
                  builtin(BuiltIn);

type AnnotatedToken = annotated_token(token: PlainToken, line: NzNat, col: NzNat, index: Nat);

type PreAst     = [<AnnotatedToken, PreAst>]; //## TOO LOOSE...

////////////////////////////////////////////////////////////////////////////////

type TokenMatchingRule  = AmberSymb,
                          lowercase_id,
                          mixedcase_id,
                          uppercase_id,
                          qualified_symbol,
                          label,
                          integer,
                          string,
                          char,
                          operator,
                          builtin,
                          keyword(Atom);

type ParsingRule  = empty_rule,
                    atomic_rule(TokenMatchingRule),
                    optional_rule(ParsingRule),
                    rule_seq([ParsingRule^]),
                    rep_rule(rule: ParsingRule, at_least_one: Bool, separator: ParsingRule, save_sep: Bool),
                    rule_choice([RuleAltern^]),
                    rule_neg(ParsingRule),
                    block_rule(par_type: ParType, rule: ParsingRule),
                    rule_ref(Atom); //## MAKE IT MORE SPECIFIC

type RuleAltern   = (name: Atom?, rule: ParsingRule); //## DONT REALLY LIKE EITHER WAY TO DEFINE THIS TYPE

type RuleMatch    = null_match,
                    atomic_rule_match(AnnotatedToken),
                    rule_seq_match([RuleMatch^]),
                    rep_rule_match([RuleMatch]),
                    rule_choice_match(name: Atom, match: RuleMatch);
