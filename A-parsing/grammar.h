ParsingRule rule_id = atomic_rule(lowercase_id); //## I SHOULD EXCLUDE ALL THE KEYWORDS HERE...

ParsingRule rule_keyword(Atom kw) = atomic_rule(keyword(kw));

ParsingRule keyword_and       = rule_keyword(:and);
ParsingRule keyword_assert    = rule_keyword(:assert);
ParsingRule keyword_break     = rule_keyword(:break);
ParsingRule keyword_elif      = rule_keyword(:elif);
ParsingRule keyword_else      = rule_keyword(:else);
ParsingRule keyword_end       = rule_keyword(:end);
ParsingRule keyword_fail      = rule_keyword(:fail);
ParsingRule keyword_false     = rule_keyword(:false);
ParsingRule keyword_for       = rule_keyword(:for);
ParsingRule keyword_if        = rule_keyword(:if);
ParsingRule keyword_in        = rule_keyword(:in);
ParsingRule keyword_let       = rule_keyword(:let);
ParsingRule keyword_loop      = rule_keyword(:loop);
ParsingRule keyword_match     = rule_keyword(:match);
ParsingRule keyword_nil       = rule_keyword(:nil);
ParsingRule keyword_not       = rule_keyword(:not);
ParsingRule keyword_or        = rule_keyword(:or);
ParsingRule keyword_print     = rule_keyword(:print);
ParsingRule keyword_replace   = rule_keyword(:replace);
ParsingRule keyword_return    = rule_keyword(:return);
ParsingRule keyword_select    = rule_keyword(:select);
ParsingRule keyword_then      = rule_keyword(:then);
ParsingRule keyword_true      = rule_keyword(:true);
ParsingRule keyword_type      = rule_keyword(:type);
ParsingRule keyword_using     = rule_keyword(:using);
ParsingRule keyword_while     = rule_keyword(:while);
ParsingRule keyword_with      = rule_keyword(:with);

ParsingRule rule_ops([TokenMatchingRule^] ops) = rule_anon_choice([atomic_rule(op) : op <- ops]);

ParsingRule ops_prec_log      = rule_anon_choice([keyword_and, keyword_or]);
ParsingRule ops_prec_eq       = rule_ops([double_equals, not_equal]);
ParsingRule ops_prec_ord      = rule_ops([lower, greater, lower_eq, greater_eq]);
ParsingRule ops_prec_sum      = rule_ops([plus, minus, ampersand]);
ParsingRule ops_prec_prod     = rule_ops([asterisk, slash]);

ParsingRule rule_ref_type         = rule_ref(:type);
ParsingRule rule_ref_pretype      = rule_ref(:pretype);
ParsingRule rule_ref_expr         = rule_ref(:expr);
ParsingRule rule_ref_stmt         = rule_ref(:stmt);
ParsingRule rule_ref_ptrn         = rule_ref(:ptrn);
ParsingRule rule_ref_fndef        = rule_ref(:fndef);
ParsingRule rule_ref_fndef_proc   = rule_ref(:fndef_proc);
ParsingRule rule_ref_fndef_switch = rule_ref(:fndef_switch);

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

ParsingRule rule_amber_file = rep_rule(rule_declaration, true);

ParsingRule rule_declaration =
  rule_choice([
    (name: :typedef,        rule: rule_typedef),
    (name: :par_typedef,    rule: rule_par_typedef),
    (name: :fndef,          rule: rule_std_fndef(true)),
    (name: :fndef_proc,     rule: rule_proc_fndef(true)),
    (name: :fndef_switch,   rule: rule_switch_fndef),
    (name: :using_block_1,  rule: rule_using_block_1),
    (name: :using_block_2,  rule: rule_using_block_2)
  ]);

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

ParsingRule rule_using_block_1 =
  rule_seq([
    keyword_using,
    comma_sep_seq(rule_signature),
    brace_rule(rep_rule(rule_fndef, true))
  ]);

ParsingRule rule_using_block_2 =
  rule_seq([
    keyword_using,
    brace_rule(
      rule_seq([
        comma_sep_seq(rule_signature),
        atomic_rule(semicolon),
        rep_rule(rule_fndef, true)
      ])
    )
  ]);

ParsingRule rule_signature = rule_seq([rule_type, rule_id, optional_rule(par_rule(comma_sep_seq(rule_type)))]);

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

ParsingRule rule_typedef =
  rule_seq([
    keyword_type,
    atomic_rule(mixedcase_id),
    atomic_rule(equals),
    comma_sep_seq(rule_pretype),
    atomic_rule(semicolon)
  ]);

ParsingRule rule_par_typedef =
  rule_seq([
    keyword_type,
    atomic_rule(mixedcase_id),
    bracket_rule(comma_sep_seq(rule_type_var)),
    atomic_rule(equals),
    comma_sep_seq(rule_pretype),
    atomic_rule(semicolon)
  ]);

////////////////////////////////////////////////////////////////////////////////

ParsingRule rule_type =
  rule_seq([
    rule_choice([
      (name: :type_name_par,    rule: rule_type_name_par),
      (name: :type_name,        rule: rule_type_name),
      (name: :type_var,         rule: rule_type_var),
      (name: :type_union,       rule: rule_type_union),
      (name: :type_any_symbol,  rule: rule_type_any_symbol),
      (name: :type_integer,     rule: rule_type_integer),
      (name: :type_float,       rule: rule_type_float),
      (name: :type_seq,         rule: rule_type_seq),
      (name: :type_map,         rule: rule_type_map),
      (name: :type_record,      rule: rule_type_record),
      (name: :type_tuple,       rule: rule_type_tuple),
      (name: :type_any_tag_obj, rule: rule_type_any_tag_obj)
    ]),
    rep_rule(
      rule_choice([
        (name: :set,    rule: atomic_rule(asterisk)),
        (name: :ne_set, rule: atomic_rule(plus))
      ])
    )
  ]);

ParsingRule rule_pretype =
  rule_choice([
    (name: :type,             rule: rule_ref_type),
    (name: :type_empty_set,   rule: rule_type_empty_set),
    (name: :type_empty_seq,   rule: rule_type_empty_seq),
    (name: :type_empty_map,   rule: rule_type_empty_map),
    (name: :type_tag_obj,     rule: rule_type_tag_obj),
    (name: :type_tag_record,  rule: rule_type_tag_record),
    (name: :type_symbol,      rule: rule_type_symbol)
  ]);

ParsingRule rule_type_name        = atomic_rule(mixedcase_id);
ParsingRule rule_type_var         = atomic_rule(uppercase_id);
ParsingRule rule_type_name_par    = rule_seq([rule_type_name, bracket_rule(comma_sep_seq(rule_ref_type))]);
ParsingRule rule_type_union       = rule_seq([atomic_rule(lower), comma_sep_seq(rule_ref_pretype), atomic_rule(greater)]);
ParsingRule rule_type_any_symbol  = rule_seq([atomic_rule(lower), atomic_rule(plus), atomic_rule(greater)]);
ParsingRule rule_type_integer     = bracket_rule(rule_seq([int_type_bound, atomic_rule(double_dot), int_type_bound]));
ParsingRule rule_type_float       = rule_seq([atomic_rule(lower), atomic_rule(circumflex), atomic_rule(greater)]);
ParsingRule rule_type_seq         = bracket_rule(rule_seq([rule_ref_type, optional_rule(atomic_rule(circumflex))]));
ParsingRule rule_type_map         = par_rule(rule_seq([rule_ref_type, atomic_rule(double_right_arrow), rule_ref_type]));

ParsingRule rule_type_record      = par_rule(comma_sep_seq(record_field));

ParsingRule rule_type_tuple       = par_rule(comma_sep_seq(rule_ref_type, 2));

ParsingRule rule_type_any_tag_obj = par_rule(rule_seq([rule_type_any_symbol, atomic_rule(at), rule_ref_type]));

ParsingRule rule_type_empty_set   = empty_block_rule(brace);
ParsingRule rule_type_empty_seq   = empty_block_rule(bracket);
ParsingRule rule_type_empty_map   = empty_block_rule(parenthesis);

ParsingRule rule_type_symbol      = atomic_rule(lowercase_id);
ParsingRule rule_type_tag_obj     = rule_seq([rule_type_symbol, par_rule(rule_ref_pretype)]);
ParsingRule rule_type_tag_record  = rule_seq([rule_type_symbol, rule_type_record]);

////////////////////////////////////////////////////////////////////////////////

ParsingRule record_field = rule_seq([atomic_rule(label), rule_ref_pretype, optional_rule(atomic_rule(question_mark))]);

ParsingRule int_type_bound =
  rule_choice([
    (name: :asterisk,     rule: atomic_rule(asterisk)),
    (name: :integer,      rule: atomic_rule(integer)),
    (name: :neg_integer,  rule: rule_seq([atomic_rule(minus), atomic_rule(integer)]))
  ]);

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

ParsingRule rule_fndef =
  rule_choice([
    (name: :std,    rule: rule_std_fndef(true)),
    (name: :proc,   rule: rule_proc_fndef(true)),
    (name: :switch, rule: rule_switch_fndef)
  ]);

ParsingRule rule_std_fndef(Bool arity_0_allowed) =
  rule_seq([
    optional_rule(rule_type),
    rule_anon_choice([rule_id, atomic_rule(operator)]),
    maybe_optional_rule(par_rule(comma_sep_seq(rule_fn_arg)), arity_0_allowed),
    atomic_rule(equals),
    rule_expr,
    // optional_rule(rule_seq([keyword_let, rep_rule(rule_asgnm_stmt, true)])),
    atomic_rule(semicolon)
  ]);

ParsingRule rule_proc_fndef(Bool arity_0_allowed) =
  rule_seq([
    optional_rule(rule_type),
    rule_anon_choice([rule_id, atomic_rule(operator)]),
    maybe_optional_rule(par_rule(comma_sep_seq(rule_fn_arg)), arity_0_allowed),
    brace_rule(rep_rule(rule_stmt, true))
  ]);

ParsingRule rule_switch_fndef = //## rule_try_fndef? rule_match_fndef?
  rule_seq([
    optional_rule(rule_type),
    rule_anon_choice([rule_id, atomic_rule(operator)]),
    par_rule(comma_sep_seq(rule_fn_arg)),
    atomic_rule(colon),
    comma_sep_seq(rule_switch_case),
    atomic_rule(semicolon)
  ]);

ParsingRule rule_fn_arg =
  rule_choice([
    (name: :unknown,  rule: atomic_rule(underscore)),
    (name: :untyped,  rule: rule_id),
    (name: :typed,    rule: rule_seq([rule_type, optional_rule(rule_id)])),
    (name: :cls,      rule: rule_seq([rule_cls_type, rule_id]))
  ]);

ParsingRule rule_cls_type =
  par_rule(
    rule_seq([
      comma_sep_seq(rule_type),
      atomic_rule(right_arrow),
      rule_type
    ])
  );

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

ParsingRule rule_switch_ptrn = //## rule_try_ptrn? rule_match_ptrn?
  rule_seq([
    rule_choice([
      (name: :type,         rule: rule_type),
      //## THIS WOULDN'T MAKE MUCH SENSE AT THE ROOT, AND THERE'S NO POINT IN ALLOWING IT TO BE FOLLOWED BY ANOTHER
      //## PATTERN VARIABLE, BUT ON THE OTHER HAND LEAVING IT LIKE THAT IS SIMPLER AND DOESN'T DO ANY REAL HARM
      (name: :tag_only,     rule: rule_seq([atomic_rule(lowercase_id), empty_block_rule(parenthesis)])),
      (name: :tag_obj,      rule: rule_seq([atomic_rule(lowercase_id), par_rule(rule_ref_ptrn)])),
      (name: :tag_obj_any,  rule: rule_seq([atomic_rule(lowercase_id), atomic_rule(at), atomic_rule(lowercase_id)])),
      (name: :var,          rule: rule_seq([atomic_rule(lowercase_id), atomic_rule(question_mark)])),
      (name: :atom,         rule: atomic_rule(lowercase_id)),
      (name: :integer,      rule: rule_seq([optional_rule(atomic_rule(minus)), atomic_rule(integer)])),
      (name: :atom_any,     rule: atomic_rule(plus)),
      (name: :integer_any,  rule: atomic_rule(asterisk)),
      (name: :float,        rule: atomic_rule(circumflex)),
      (name: :any,          rule: atomic_rule(underscore)),
      // (name: :empty_seq,    rule: empty_block_rule(bracket)),
      (name: :seq,          rule: bracket_rule(atomic_rule(triple_dot))),
      // (name: :empty_set,    rule: empty_block_rule(brace)),
      (name: :set,          rule: brace_rule(atomic_rule(triple_dot))),
      // (name: :empty_map,    rule: empty_block_rule(parenthesis)),
      (name: :map,          rule: par_rule(atomic_rule(triple_dot)))
    ]),
    optional_rule(rule_seq([atomic_rule(lowercase_id), atomic_rule(question_mark)]))
  ]);

ParsingRule rule_clause_ptrn =
  rule_choice([
    (name: :any,      rule: atomic_rule(underscore)),
    (name: :tag_var,  rule: rule_seq([atomic_rule(lowercase_id), empty_block_rule(parenthesis), atomic_rule(lowercase_id)])),
    (name: :tag_only, rule: rule_seq([atomic_rule(lowercase_id), empty_block_rule(parenthesis)])),
    (name: :tag_obj,  rule: rule_seq([atomic_rule(lowercase_id), par_rule(atomic_rule(lowercase_id))])),
    // (name: :tag_var,  rule: rule_seq([atomic_rule(lowercase_id), empty_block_rule(parenthesis), atomic_rule(lowercase_id)])),
    (name: :var,      rule: atomic_rule(lowercase_id))
  ]);

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

ParsingRule rule_stmt =
  rule_choice([
    (name: :asgnm,        rule: rule_asgnm_stmt),
    (name: :ret,          rule: rule_ret_stmt),
    (name: :if_stmt,      rule: rule_if_stmt),
    (name: :loop_stmt,    rule: rule_loop_stmt),
    (name: :while_stmt,   rule: rule_while_stmt),
    (name: :let_stmt,     rule: rule_let_stmt),
    (name: :break_stmt,   rule: rule_break_stmt),
    (name: :for_stmt,     rule: rule_for_stmt),
    (name: :fail_stmt,    rule: rule_fail_stmt),
    (name: :assert_stmt,  rule: rule_assert_stmt),
    (name: :print_stmt,   rule: rule_print_stmt),
    (name: :imp_update,   rule: rule_imp_update_stmt),
    (name: :fn,           rule: rule_ref_fndef),
    (name: :fn_proc,      rule: rule_ref_fndef_proc),
    (name: :fn_case,      rule: rule_ref_fndef_switch)
  ]);

ParsingRule rule_asgnm_stmt =
  rule_seq([
    optional_rule(rule_type),
    comma_sep_seq(rule_id),
    atomic_rule(equals),
    rule_ref_expr,
    optional_rule(rule_seq([keyword_if, rule_ref_expr])),
    atomic_rule(semicolon)
  ]);

ParsingRule rule_ret_stmt =
  rule_seq([
    keyword_return,
    rule_ref_expr,
    optional_rule(rule_seq([keyword_if, rule_ref_expr])),
    atomic_rule(semicolon)
  ]);

ParsingRule rule_if_stmt =
  rule_seq([
    keyword_if,
    par_rule(rule_ref_expr),
    rep_rule(rule_ref_stmt, true),
    rep_rule(
      rule_seq([
        keyword_elif,
        par_rule(rule_ref_expr),
        rep_rule(rule_ref_stmt, true)
      ])
    ),
    optional_rule(
      rule_seq([
        keyword_else,
        rep_rule(rule_ref_stmt, true)
      ])
    ),
    atomic_rule(semicolon)
  ]);

ParsingRule rule_loop_stmt =
  rule_seq([
    keyword_loop,
    rep_rule(rule_ref_stmt, true),
    optional_rule(rule_seq([keyword_while, par_rule(rule_ref_expr)])),
    atomic_rule(semicolon)
  ]);

ParsingRule rule_while_stmt =
  rule_seq([
    keyword_while,
    par_rule(rule_ref_expr),
    rep_rule(rule_ref_stmt, true),
    atomic_rule(semicolon)
  ]);

ParsingRule rule_for_stmt =
  rule_seq([
    keyword_for,
    par_rule(rep_rule(rule_for_range, atomic_rule(semicolon), true, false)),
    rep_rule(rule_ref_stmt, true),
    atomic_rule(semicolon)
  ]);

ParsingRule rule_for_range =
  rule_choice([
    (name: :foreach,      rule: rule_seq([comma_sep_seq(rule_id), atomic_rule(colon), rule_ref_expr])),
    (name: :foreach_idx,  rule: rule_seq([comma_sep_seq(rule_id), atomic_rule(at), rule_id, atomic_rule(colon), rule_ref_expr])),
    (name: :for,          rule: rule_seq([rule_id, atomic_rule(equals), rule_ref_expr, atomic_rule(double_dot), rule_ref_expr]))
  ]);

ParsingRule rule_let_stmt =
  rule_seq([
    keyword_let,
    par_rule(comma_sep_seq(rule_seq([rule_id, atomic_rule(equals), rule_ref_expr]))),
    rep_rule(rule_ref_stmt, true),
    atomic_rule(semicolon)
  ]);

ParsingRule rule_break_stmt =
  rule_seq([
    keyword_break,
    optional_rule(rule_seq([keyword_if, rule_ref_expr])),
    atomic_rule(semicolon)
  ]);

ParsingRule rule_fail_stmt =
  rule_seq([
    keyword_fail,
    optional_rule(rule_seq([keyword_if, rule_ref_expr])),
    atomic_rule(semicolon)
  ]);

ParsingRule rule_assert_stmt = rule_seq([keyword_assert, rule_ref_expr, atomic_rule(semicolon)]);

ParsingRule rule_print_stmt =
  rule_seq([
    keyword_print,
    rule_ref_expr,
    optional_rule(rule_seq([keyword_if, rule_ref_expr])),
    atomic_rule(semicolon)
  ]);

ParsingRule rule_imp_update_stmt =
  rule_seq([
    rule_id,
    bracket_rule(rule_ref_expr),
    atomic_rule(assign),
    rule_ref_expr,
    atomic_rule(semicolon)
  ]);

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

ParsingRule rule_clause =
  rule_choice([
    (name: :in,   rule: rule_in_clause),
    (name: :eq,   rule: rule_seq([rule_id, atomic_rule(equals), rule_ref_expr]))
  ]);

ParsingRule rule_in_clause =
  rule_seq([
    rule_clause_ptrn,
    optional_rule(rule_seq([atomic_rule(double_right_arrow), rule_clause_ptrn])),
    atomic_rule(left_arrow),
    rule_ref_expr
  ]);

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

ParsingRule rule_expr = rule_expr_10;

ParsingRule rule_expr_10  = rule_seq([rule_expr_9, optional_rule(rule_seq([atomic_rule(at), rule_expr_9]))]);
ParsingRule rule_expr_9   = rep_rule(rule_expr_8, ops_prec_log, true, true);
ParsingRule rule_expr_8   = rule_seq([rule_expr_7, optional_rule(rule_seq([ops_prec_eq, rule_expr_7]))]);
ParsingRule rule_expr_7   = rule_seq([rule_expr_6, optional_rule(rule_seq([ops_prec_ord, rule_expr_6]))]);
ParsingRule rule_expr_6   = rep_rule(rule_expr_5, ops_prec_sum, true, true);
ParsingRule rule_expr_5   = rep_rule(rule_expr_4, ops_prec_prod, true, true);
ParsingRule rule_expr_4   = rule_seq([optional_rule(rule_anon_choice([atomic_rule(minus), keyword_not])), rule_expr_3]);
ParsingRule rule_expr_3   = rep_rule(rule_expr_2, atomic_rule(circumflex), true, false);
ParsingRule rule_expr_2   = rule_seq([rule_expr_1, optional_rule(rule_seq([atomic_rule(double_colon), rule_type]))]);
ParsingRule rule_expr_1   = rule_seq([rule_expr_0, rep_rule(rule_dot_or_sub), optional_rule(rule_dot_access(true))]);

ParsingRule rule_dot_or_sub             = rule_choice([(name: :dot, rule: rule_dot_access(false)), (name: :sub, rule: rule_subscript_op)]);
ParsingRule rule_subscript_op           = bracket_rule(rule_ref_expr);

ParsingRule rule_dot_access(Bool test)
{
  lr = atomic_rule(question_mark);
  lr = rule_neg(lr) if not test;
  return rule_seq([atomic_rule(dot), atomic_rule(lowercase_id), lr]);
}


ParsingRule rule_expr_0 =
  rule_choice([
    (name: :tag_obj,      rule: rule_seq([atomic_rule(qualified_symbol), par_rule(rule_ref_expr)])),

    (name: :integer,      rule: atomic_rule(integer)),
    (name: :symbol,       rule: atomic_rule(qualified_symbol)),
    (name: :string,       rule: atomic_rule(string)),
    (name: :float,        rule: atomic_rule(float)),

    (name: true,          rule: atomic_rule(keyword(true))),
    (name: false,         rule: atomic_rule(keyword(false))),
    (name: nil,           rule: atomic_rule(keyword(nil))),

    (name: :set,          rule: brace_rule(opt_comma_sep_seq(rule_subexpr))),
    (name: :map,          rule: par_rule(opt_comma_sep_seq(rule_map_entry))),
    (name: :record,       rule: rule_record_expr),
    (name: :seq,          rule: rule_seq_expr),
    (name: :seq_tail,     rule: rule_seq_tail_expr),

    (name: :tag_record,   rule: rule_tag_record_expr),

    (name: :builtin_call, rule: rule_seq([atomic_rule(builtin), par_rule(comma_sep_seq(rule_ref_expr))])),

    (name: :par_exprs,    rule: par_rule(comma_sep_seq(rule_ref_expr))),

    (name: :ex_qual,      rule: rule_ex_qual_expr),
    (name: :set_cp,       rule: rule_set_cp_expr),
    (name: :map_cp,       rule: rule_map_cp_expr),
    (name: :seq_cp,       rule: rule_seq_cp_expr),

    (name: :alt_cp,       rule: rule_alt_cp_expr),


    (name: :if_else,      rule: rule_if_expr),
    (name: :match_expr,   rule: rule_match_expr),
    (name: :proc,         rule: brace_rule(rep_rule(rule_ref_stmt, true))),

    (name: :select_expr,  rule: rule_select_expr),
    (name: :replace_expr, rule: rule_replace_expr),

    (name: :fn_call,      rule: rule_fn_call_expr),
    (name: :const_or_var, rule: rule_id),
    (name: :cls_par,      rule: atomic_rule(qual_var))
  ]);

ParsingRule rule_subexpr = rule_seq([rule_ref_expr, optional_rule(rule_seq([keyword_if, rule_ref_expr]))]);

ParsingRule rule_map_entry =
  rule_seq([
    rule_ref_expr,
    atomic_rule(double_right_arrow),
    rule_ref_expr,
    optional_rule(
      rule_seq([
        keyword_if,
        rule_ref_expr
      ])
    )
  ]);

ParsingRule rule_record_expr =
  par_rule(
    comma_sep_seq(
      rule_seq([
        atomic_rule(label),
        rule_ref_expr,
        optional_rule(rule_seq([keyword_if, rule_ref_expr]))
      ])
    )
  );

ParsingRule rule_seq_expr = bracket_rule(comma_sep_seq(rule_subexpr, false));

ParsingRule rule_seq_tail_expr =
  bracket_rule(
    rule_seq([
      rule_ref_expr,
      rule_seq([atomic_rule(pipe), comma_sep_seq(rule_ref_expr)]) //## MAYBE HERE I SHOULD ALLOW ALSO A CONDITIONAL EXPRESSION
    ])
  );

//## MAYBE I SHOULD ALLOW ALSO SYMBOLS FOR THE FIRST TOKEN, IN CASE THE SYMBOL NAME CONFLICTS WITH A KEYWORD
ParsingRule rule_tag_record_expr = rule_seq([atomic_rule(lowercase_id), rule_record_expr]);

ParsingRule rule_fn_call_expr =
  rule_seq([
    rule_anon_choice([rule_id, atomic_rule(operator)]),
    par_rule(
      rule_seq([
        comma_sep_seq(
          rule_seq([
            rule_neg(rule_actual_named_par),
            rule_ref_expr
          ])
        ),
        rep_rule(
          rule_seq([
            atomic_rule(comma),
            rule_actual_named_par
          ])
        )
      ])
    )
  ]);

ParsingRule rule_actual_named_par =
  rule_seq([
    rule_id,
    optional_rule(par_rule(comma_sep_seq(rule_id))),
    atomic_rule(equals),
    rule_ref_expr
  ]);

ParsingRule rule_ex_qual_expr =
  par_rule(
    rule_seq([
      atomic_rule(question_mark),
      comma_sep_seq(rule_clause),
      optional_rule(
        rule_seq([
          atomic_rule(colon),
          comma_sep_seq(rule_ref_expr)
        ])
      )
    ])
  );

ParsingRule rule_set_cp_expr =
  brace_rule(
    rule_seq([
      rule_ref_expr,
      atomic_rule(colon),
      comma_sep_seq(rule_clause),
      optional_rule(
        rule_seq([
          atomic_rule(comma),
          comma_sep_seq(rule_ref_expr)
        ])
      )
    ])
  );

ParsingRule rule_map_cp_expr =
  par_rule(
    rule_seq([
      rule_ref_expr,
      atomic_rule(double_right_arrow),
      rule_ref_expr,
      atomic_rule(colon),
      comma_sep_seq(rule_clause),
      optional_rule(rule_seq([atomic_rule(comma), comma_sep_seq(rule_ref_expr)]))
    ])
  );

ParsingRule rule_alt_cp_expr =
  rule_seq([
    keyword_for,
    par_rule(comma_sep_seq(rule_clause)),
    optional_rule(
      rule_seq([
        keyword_if,
        par_rule(comma_sep_seq(rule_ref_expr))
      ])
    ),
    rule_choice([
      (name: :set,  rule: brace_rule(rule_ref_expr)),
      (name: :map,  rule: par_rule(rule_seq([rule_ref_expr, atomic_rule(double_right_arrow), rule_ref_expr])))
    ])
  ]);

ParsingRule rule_seq_cp_expr =
  bracket_rule(
    rule_seq([
      rule_ref_expr,
      atomic_rule(colon),
      comma_sep_seq(rule_id),
      optional_rule(rule_seq([atomic_rule(at), rule_id])),
      atomic_rule(left_arrow),
      rule_ref_expr,
      optional_rule(rule_seq([atomic_rule(comma), rule_ref_expr]))
    ])
  );

ParsingRule rule_if_expr =
  rule_seq([
    keyword_if,
    comma_sep_seq(
      rule_seq([
        rule_ref_expr,
        keyword_then,
        rule_ref_expr
      ])
    ),
    keyword_else,
    rule_ref_expr,
    keyword_end
  ]);

ParsingRule rule_match_expr =
  rule_seq([
    keyword_match,
    par_rule(comma_sep_seq(rule_ref_expr)),
    comma_sep_seq(rule_switch_case),
    atomic_rule(semicolon)
  ]);

ParsingRule rule_switch_case =
  rule_seq([
    comma_sep_seq(rule_switch_ptrn),
    atomic_rule(equals),
    rule_ref_expr
  ]);

ParsingRule rule_select_expr =
  rule_seq([
    keyword_select,
    rule_type,
    keyword_in,
    rule_ref_expr,
    keyword_end
  ]);

ParsingRule rule_replace_expr =
  rule_seq([
    keyword_replace,
    rule_type,
    rule_id,
    keyword_in,
    rule_ref_expr,
    keyword_with,
    rule_ref_expr,
    keyword_end
  ]);
