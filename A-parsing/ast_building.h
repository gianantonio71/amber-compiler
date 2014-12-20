[PrgDecl] build_amber_file_ast(RuleMatch file) = [build_declaration_ast(m) : m <- rep_rule_nodes(file)];

PrgDecl build_declaration_ast(RuleMatch decl) =
  match (decl.name)
    typedef         = build_typedef_ast(decl.match),
    par_typedef     = build_par_typedef_ast(decl.match),
    fndef           = build_std_fndef_ast(decl.match),
    fndef_proc      = build_proc_fndef_ast(decl.match),
    fndef_switch    = build_switch_fndef_ast(decl.match),
    using_block_1   = build_using_block_1_ast(decl.match),
    using_block_2   = build_using_block_2_ast(decl.match);
  ;

////////////////////////////////////////////////////////////////////////////////

SynTypedef build_typedef_ast(RuleMatch typedef)
{
  nodes = rule_seq_nodes(typedef);
  assert is_annotated_token(nodes[0], lowercase_id(:type));
  name = build_basic_type_symbol_ast(nodes[1]);
  assert is_annotated_token(nodes[2], equals);
  pretypes = [build_pretype_ast(n) : n <- rep_rule_nodes(nodes[3])];
  assert is_annotated_token(nodes[4], semicolon);
  return syn_typedef(name, syn_union(pretypes));
}

SynParTypedef build_par_typedef_ast(RuleMatch par_typedef)
{
  nodes = rule_seq_nodes(par_typedef);
  assert is_annotated_token(nodes[0], lowercase_id(:type));
  name = build_basic_type_symbol_ast(nodes[1]);
  params = [build_type_var_ast(p) : p <- rep_rule_nodes(nodes[2])];
  assert is_annotated_token(nodes[3], equals);
  pretypes = [build_pretype_ast(n) : n <- rep_rule_nodes(nodes[4])];
  assert is_annotated_token(nodes[5], semicolon);
  return syn_par_typedef(name, params, syn_union(pretypes));
}

SynType build_pretype_ast(RuleMatch pretype) =
  match (pretype.name)
    type              = build_type_ast(pretype.match),
    type_empty_set    = empty_set_type,
    type_empty_seq    = empty_seq_type,
    type_empty_map    = empty_map_type,
    type_tag_obj      = build_tag_obj_type_ast(pretype.match),
    type_tag_record   = build_tag_record_type_ast(pretype.match),
    type_symbol       = build_symbol_type(pretype.match);
  ;

SynType build_type_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  basic_type_node = nodes[0];
  submatch = basic_type_node.match;
  res_type = match(basic_type_node.name)
                type_name         = build_type_ref_ast(submatch),
                type_name_par     = build_par_type_ref_ast(submatch),
                type_var          = build_type_var_ast(submatch),
                type_union        = build_type_union_ast(submatch),
                type_any_symbol   = atom_type,
                type_integer      = build_integer_type_ast(submatch),
                type_float        = float_type,
                type_seq          = build_seq_type_ast(submatch),
                type_map          = build_map_type_ast(submatch),
                type_record       = build_record_type_ast(submatch),
                type_tuple        = build_tuple_type_ast(submatch),
                type_any_tag_obj  = build_any_tag_obj_type(submatch);
              ;
  for (s : rep_rule_nodes(nodes[1]))
    res_type = syn_set_type(res_type, s.name == :ne_set);
  ;
  return res_type;
}

SynType build_tag_obj_type_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 2;
  tag_type = symb_type(_obj_(annotated_token(nodes[0]).token));
  obj_type = build_pretype_ast(nodes[1]);
  return syn_tag_obj_type(tag_type, obj_type);
}

SynType build_tag_record_type_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 2;
  tag_type = symb_type(_obj_(annotated_token(nodes[0]).token));
  obj_type = build_record_type_ast(nodes[1]);
  return tag_obj_type(tag_type, obj_type);
}

SymbType build_symbol_type(RuleMatch mtc) = symb_type(get_lowercase_id(mtc));

TypeRef build_type_ref_ast(RuleMatch mtc):
  atomic_rule_match(at?)  = type_ref(type_symbol(_obj_(at.token)));

SynType build_par_type_ref_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 2;
  ts = type_symbol(_obj_(annotated_token(nodes[0]).token));
  ps = [build_type_ast(n) : n <- rep_rule_nodes(nodes[1])];
  return syn_type_ref(ts, ps);
}

TypeVar build_type_var_ast(RuleMatch mtc) = type_var(get_lowercase_id(mtc));

SynType build_type_union_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 3;
  types = [build_pretype_ast(n) : n <- rep_rule_nodes(nodes[1])];
  return syn_union(types);
}

SynType build_integer_type_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 3;
  assert is_annotated_token(nodes[1], double_dot);
  min_node = nodes[0];
  max_node = nodes[2];
  min = bound(min_node.name, min_node.match);
  max = bound(max_node.name, max_node.match);
  return match (min, max)
           nil,   nil   = integer,
           nil,   *     = low_ints(max),
           *,     nil   = high_ints(min),
           *,     *     = syn_int_range(min, max);
         ;

  <Int, nil> bound(<asterisk, integer, neg_integer> bound_type, RuleMatch mtc):
    asterisk      = nil,
    integer       = annotated_token(mtc).token,
    neg_integer   = -annotated_token(right(rule_seq_nodes(mtc))).token;
}

SynType build_seq_type_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 2;
  elem_type = build_type_ast(nodes[0]);
  return syn_seq_type(elem_type, nodes[1] /= null_match);
}

SynType build_map_type_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 3;
  key_type = build_type_ast(nodes[0]);
  value_type = build_type_ast(nodes[2]);
  return syn_map_type(key_type, value_type);
}

SynRecordType build_record_type_ast(RuleMatch mtc)
{
  fields = [build_record_field_ast(n) : n <- rep_rule_nodes(mtc)];
  return syn_record_type(fields);

  (label: SymbObj, type: SynType, optional: Bool) build_record_field_ast(RuleMatch mtc)
  {
    nodes = rule_seq_nodes(mtc);
    assert length(nodes) == 3;
    label = object(_obj_(annotated_token(nodes[0]).token));
    type = build_pretype_ast(nodes[1]);
    optional = nodes[2] /= null_match;
    return (label: label, type: type, optional: optional);
  }
}

SynTupleType build_tuple_type_ast(RuleMatch mtc) = syn_tuple_type([build_type_ast(n) : n <- rep_rule_nodes(mtc)]);

SynType build_any_tag_obj_type(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 3;
  obj_type = build_type_ast(nodes[2]);
  return syn_any_tag_obj_type(obj_type);
}

////////////////////////////////////////////////////////////////////////////////

Maybe[SynType] build_maybe_type_ast(RuleMatch mtc) = if mtc /= null_match then just(build_type_ast(mtc)) else nil end;

////////////////////////////////////////////////////////////////////////////////

SynFnDef build_fndef_ast(RuleMatch mtc) =
  match (mtc.name)
    std     = build_std_fndef_ast(mtc.match),
    proc    = build_proc_fndef_ast(mtc.match),
    switch  = build_switch_fndef_ast(mtc.match);
  ;

SynFnDef build_std_fndef_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 6;
  ret_type  = build_maybe_type_ast(nodes[0]);
  return syn_fn_def(
    name:       build_fn_symbol_ast(nodes[1]),
    params:     build_fn_params_ast(nodes[2]),
    res_type:   value(ret_type) if ret_type /= nil,
    expr:       build_expr_ast(nodes[4]),
    local_fns:  []
  );
}

SynFnDef build_proc_fndef_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 4;
  ret_type = build_maybe_type_ast(nodes[0]);
  return syn_fn_def(
    name:       build_fn_symbol_ast(nodes[1]),
    params:     build_fn_params_ast(nodes[2]),
    res_type:   value(ret_type) if ret_type /= nil,
    expr:       build_proc_expr_ast(nodes[3]),
    local_fns:  []
  );
}

SynFnDef build_switch_fndef_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 6;
  ret_type = build_maybe_type_ast(nodes[0]);
  params = build_fn_params_ast(nodes[2]);
  cases = [build_switch_case_ast(n) : n <- rep_rule_nodes(nodes[4])];
  arity = syn_case_arity(cases[0]);
  // expr = syn_try_expr([fn_par(i) : i <- indexes(cases[0].patterns)], cases); //## REENABLE THIS ONCE ALL THE TESTING IS DONE
  expr = syn_try_expr([fn_par(i) : i <- inc_seq(arity)], cases);
  return syn_fn_def(
    name:       build_fn_symbol_ast(nodes[1]),
    params:     params,
    res_type:   value(ret_type) if ret_type /= nil,
    expr:       expr,
    local_fns:  []
  );
}

SynUsingBlock build_using_block_1_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 3;
  return build_using_block_ast(nodes[1], nodes[2]);
}

SynUsingBlock build_using_block_2_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  nodes = rule_seq_nodes(nodes[1]);
  assert length(nodes) == 3;
  return build_using_block_ast(nodes[0], nodes[2]);
}

SynUsingBlock build_using_block_ast(RuleMatch signatures, RuleMatch fndefs) =
  syn_using_block(
    [build_signature_ast(n) : n  <- rep_rule_nodes(signatures)],
    [build_fndef_ast(fd)    : fd <- rep_rule_nodes(fndefs)]
  );

SynSgn build_signature_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 3;
  return syn_sgn(
    build_fn_symbol_ast(nodes[1]),
    [build_type_ast(t) : t <- rep_rule_nodes(nodes[2])],
    build_type_ast(nodes[0])
  );
}

FnSymbol build_fn_symbol_ast(RuleMatch mtc) =
  match (get_token(mtc))
    lowercase_id(a?)  = fn_symbol(a),
    operator(op?)     = op_symbol(op);
  ;

[SynFnArg] build_fn_params_ast(RuleMatch mtc) = if mtc /= null_match then [build_fn_arg_ast(m) : m <- rep_rule_nodes(mtc)] else [] end; //## MAYBE rep_rule_nodes (AND seq_rule_nodes) SHOULD RETURN THE EMPTY SEQUENCE WHEN INVOKED WITH A null_match PARAMETER

SynFnArg build_fn_arg_ast(RuleMatch mtc) =
  match (mtc.name)
    unknown   = (),
    untyped   = (var: var(get_lowercase_id(mtc.match))),
    typed     = {
      nodes = rule_seq_nodes(mtc.match);
      assert length(nodes) == 2;
      return (type: build_type_ast(nodes[0]), var: var(get_lowercase_id(nodes[1])) if nodes[1] /= null_match);
    },
    cls       = {
      nodes = rule_seq_nodes(mtc.match);
      assert length(nodes) == 2;
      return (type: build_cls_type_ast(nodes[0]), var: var(get_lowercase_id(nodes[1])));
    };
  ;

SynClsType build_cls_type_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 3;
  in_types = [build_type_ast(n) : n <- rep_rule_nodes(nodes[0])];
  out_type = build_type_ast(nodes[2]);
  return syn_cls_type(in_types, out_type);
}

////////////////////////////////////////////////////////////////////////////////

SynExpr build_expr_ast(RuleMatch mtc) = build_expr_10_ast(mtc);

SynExpr build_expr_10_ast(RuleMatch mtc)
{
  // ParsingRule rule_expr_10  = rule_seq([rule_expr_9, optional_rule(rule_seq([atomic_rule(at), rule_expr_9]))]);
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 2;
  expr = build_expr_9_ast(nodes[0]);
  return expr if nodes[1] == null_match;
  right_expr = build_expr_9_ast(get_rule_seq_node(nodes[1], 1));
  return syn_tag_obj_expr(expr, right_expr);
}

SynExpr build_expr_9_ast(RuleMatch mtc)
{
  // ParsingRule rule_expr_9   = rep_rule(rule_expr_8, ops_prec_log, true, true);
  nodes = rep_rule_nodes(mtc);
  expr = build_expr_8_ast(nodes[0]);
  for (i : inc_seq(1, length(nodes), 2))
    right_expr = build_expr_8_ast(nodes[i+1]);
    op = get_lowercase_id(nodes[i]);
    if (op == :and)
      expr = syn_and(expr, right_expr);
    else
      assert op == :or;
      expr = syn_or(expr, right_expr);
    ;
  ;
  return expr;
}

SynExpr build_expr_8_ast(RuleMatch mtc)
{
  // ParsingRule rule_expr_8   = rule_seq([rule_expr_7, optional_rule(rule_seq([ops_prec_eq, rule_expr_7]))]);
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 2;
  expr = build_expr_7_ast(nodes[0]);
  return expr if nodes[1] == null_match;
  nodes = rule_seq_nodes(nodes[1]);
  op = get_token(nodes[0]);
  right_expr = build_expr_7_ast(nodes[1]);
  if (op == :double_equals)
    return syn_eq(expr, right_expr);
  else
    assert op == :not_equal;
    return syn_neq(expr, right_expr);
  ;
}

SynExpr build_expr_7_ast(RuleMatch mtc)
{
  // ParsingRule rule_expr_7   = rule_seq([rule_expr_6, optional_rule(rule_seq([ops_prec_ord, rule_expr_6]))]);
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 2;
  expr = build_expr_6_ast(nodes[0]);
  return expr if nodes[1] == null_match;
  nodes = rule_seq_nodes(nodes[1]);
  op = op_symbol(token_to_operator(get_token(nodes[0])));
  right_expr = build_expr_6_ast(nodes[1]);
  return syn_fn_call(op, [expr, right_expr]);
}

SynExpr build_expr_6_ast(RuleMatch mtc)
{
  // ParsingRule rule_expr_6   = rep_rule(rule_expr_5, ops_prec_sum, true, true);
  nodes = rep_rule_nodes(mtc);
  expr = build_expr_5_ast(nodes[0]);
  for (i : inc_seq(1, length(nodes), 2))
    op = op_symbol(token_to_operator(get_token(nodes[i])));
    right_expr = build_expr_5_ast(nodes[i+1]);
    expr = syn_fn_call(op, [expr, right_expr]);
  ;
  return expr;
}

SynExpr build_expr_5_ast(RuleMatch mtc)
{
  // ParsingRule rule_expr_5   = rep_rule(rule_expr_4, ops_prec_prod, true, true);
  nodes = rep_rule_nodes(mtc);
  expr = build_expr_4_ast(nodes[0]);
  for (i : inc_seq(1, length(nodes), 2))
    op = op_symbol(token_to_operator(get_token(nodes[i])));
    right_expr = build_expr_4_ast(nodes[i+1]);
    expr = syn_fn_call(op, [expr, right_expr]);
  ;
  return expr;
}

SynExpr build_expr_4_ast(RuleMatch mtc)
{
  // ParsingRule rule_expr_4   = rule_seq([optional_rule(rule_anon_choice([atomic_rule(minus), keyword_not])), rule_expr_3]);
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 2;
  expr = build_expr_3_ast(nodes[1]);
  prefix = nodes[0];
  if (prefix /= null_match)
    op = annotated_token(prefix).token;
    if (op == :minus)
      expr = syn_fn_call(op_symbol(:minus), [expr]);
    else
      assert op == lowercase_id(:not);
      expr = syn_not(expr);
    ;
  ;
  return expr;
}

SynExpr build_expr_3_ast(RuleMatch mtc)
{
  // ParsingRule rule_expr_3   = rep_rule(rule_expr_2, atomic_rule(circumflex), true, false);
  nodes = rep_rule_nodes(mtc);
  expr = build_expr_2_ast(last(nodes));
  for (i : dec_seq(length(nodes)-1))
    left_expr = build_expr_2_ast(nodes[i]);
    expr = syn_fn_call(op_symbol(:exp), [left_expr, expr]);
  ;
  return expr;
}

SynExpr build_expr_2_ast(RuleMatch mtc)
{
  // ParsingRule rule_expr_2   = rule_seq([rule_expr_1, optional_rule(rule_seq([atomic_rule(double_colon), rule_type]))]);
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 2;
  expr = build_expr_1_ast(nodes[0]);
  return expr if nodes[1] == null_match;
  type = build_type_ast(get_rule_seq_node(nodes[1], 1));
  return syn_membership(expr, type);
}

SynExpr build_expr_1_ast(RuleMatch mtc)
{
  // ParsingRule rule_expr_1   = rule_seq([rule_expr_0, rep_rule(rule_dot_or_sub), optional_rule(rule_dot_access(true))]);
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 3;
  expr = build_expr_0_ast(nodes[0]);
  for (r : rep_rule_nodes(nodes[1]))
    if (r.name == :dot)
      field = get_lowercase_id(r.match, 1);
      expr = syn_accessor(expr, field);
    else
      assert r.name == :sub;
      idx_expr = build_expr_ast(r.match);
      expr = syn_fn_call(op_symbol(:brackets), [expr, idx_expr]);
    ;
  ;
  if (nodes[2] /= null_match)
    field = get_lowercase_id(nodes[2], 1);
    expr = syn_accessor_test(expr, field);
  ;
  return expr;
}

SynExpr build_expr_0_ast(RuleMatch mtc) =
  match (mtc.name)
    tag_obj       = build_tag_obj_expr_ast(mtc.match),          // rule_seq([atomic_rule(qualified_symbol), par_rule(rule_ref_expr)])
    integer       = object(get_integer(mtc.match)),             // atomic_rule(integer)
    symbol        = object(get_qualified_symbol(mtc.match)),    // atomic_rule(qualified_symbol)
    string        = build_string_expr_ast(mtc.match),           // atomic_rule(string)
    float         = get_float_lit(mtc.match),                   // atomic_rule(float)
    true          = object(true),                               // atomic_rule(keyword(true))
    false         = object(false),                              // atomic_rule(keyword(false))
    nil           = object(nil),                                // atomic_rule(keyword(nil))
    set           = build_set_expr_ast(mtc.match),              // brace_rule(opt_comma_sep_seq(rule_subexpr))
    map           = build_map_expr_ast(mtc.match),              // par_rule(opt_comma_sep_seq(rule_map_entry))
    record        = build_record_expr_ast(mtc.match),           // rule_record_expr
    seq           = build_seq_expr_ast(mtc.match),              // rule_seq_expr
    seq_tail      = build_seq_tail_expr_ast(mtc.match),         // rule_seq_tail_expr
    tag_record    = build_tag_record_expr_ast(mtc.match),       // rule_tag_record_expr
    builtin_call  = build_builtin_call_expr_ast(mtc.match),     // rule_seq([atomic_rule(builtin), par_rule(comma_sep_seq(rule_ref_expr))])
    par_exprs     = build_tuple_or_par_expr_ast(mtc.match),     // par_rule(comma_sep_seq(rule_ref_expr))
    ex_qual       = build_ex_qual_expr_ast(mtc.match),          // rule_ex_qual_expr
    set_cp        = build_set_cp_expr_ast(mtc.match),           // rule_set_cp_expr
    map_cp        = build_map_cp_expr_ast(mtc.match),           // rule_map_cp_expr
    seq_cp        = build_seq_cp_expr_ast(mtc.match),           // rule_seq_cp_expr
    alt_cp        = build_alt_cp_expr_ast(mtc.match),           // rule_alt_cp_expr
    if_else       = build_if_else_expr_ast(mtc.match),          // rule_if_expr
    match_expr    = build_match_expr_ast(mtc.match),            // rule_match_expr
    proc          = build_proc_expr_ast(mtc.match),             // brace_rule(rep_rule(rule_ref_stmt, true))
    select_expr   = build_select_expr_ast(mtc.match),           // rule_select_expr
    replace_expr  = build_replace_expr_ast(mtc.match),          // rule_replace_expr
    fn_call       = build_fn_call_expr_ast(mtc.match),          // rule_fn_call_expr
    const_or_var  = const_or_var(get_lowercase_id(mtc.match)),  // rule_id
    cls_par       = cls_par(get_cls_par_idx(mtc.match));        // atomic_rule(qual_var))
  ;

SynTagObjExpr build_tag_obj_expr_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 2;
  return syn_tag_obj_expr(object(get_qualified_symbol(nodes[0])), build_expr_ast(nodes[1]));
}

SynSetExpr build_set_expr_ast(RuleMatch mtc) = syn_set_expr([build_subexpr_ast(n) : n <- rep_rule_nodes(mtc)]);

SynSeqExpr build_seq_expr_ast(RuleMatch mtc) = syn_seq_expr([build_subexpr_ast(n) : n <- rep_rule_nodes(mtc)]);

SynSeqExpr build_seq_tail_expr_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 2;
  seq_expr = build_expr_ast(nodes[0]);
  tail_exprs = [build_expr_ast(n) : n <- rep_rule_nodes(get_rule_seq_node(nodes[1], 1))];
  return seq_tail_expr(seq_expr, tail_exprs);
}

SynExpr build_tuple_or_par_expr_ast(RuleMatch mtc)
{
  exprs = [build_expr_ast(n) : n <- rep_rule_nodes(mtc)];
  assert length(exprs) > 0;
  return if length(exprs) == 1 then exprs[0] else syn_tuple_expr(exprs) end;
}

SynMapExpr build_map_expr_ast(RuleMatch mtc) = syn_map_expr([build_map_entry_ast(n) : n <- rep_rule_nodes(mtc)]);

SynMapExpr build_record_expr_ast(RuleMatch mtc) = syn_map_expr([build_record_field_ast(n) : n <- rep_rule_nodes(mtc)]);

SynTagObjExpr build_tag_record_expr_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 2;
  tag = object(get_lowercase_id(nodes[0]));
  obj = build_record_expr_ast(nodes[1]);
  return syn_tag_obj_expr(tag, obj);
}

SynExpr build_string_expr_ast(RuleMatch mtc) = tag_obj_expr(object(:string), seq_expr([object(ch) : ch <- _obj_(get_string(mtc))]));

SynExpr build_builtin_call_expr_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 2;
  builtin = get_builtin(nodes[0]);
  params = [build_expr_ast(n) : n <- rep_rule_nodes(nodes[1])];
  return syn_builtin_call(builtin, params);
}

SynExpr build_ex_qual_expr_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 3;
  clauses = [build_clause_ast(n) : n <- rep_rule_nodes(nodes[1])];
  exprs = build_sel_expr_asts(nodes[2]);
  return syn_ex_qual(clauses, exprs);
}

SynExpr build_set_cp_expr_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 4;
  expr = build_expr_ast(nodes[0]);
  clauses = [build_clause_ast(n) : n <- rep_rule_nodes(nodes[2])];
  exprs = build_sel_expr_asts(nodes[3]);
  return syn_set_comp(expr, clauses, exprs);
}

SynExpr build_map_cp_expr_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 6;
  key_expr = build_expr_ast(nodes[0]);
  value_expr = build_expr_ast(nodes[2]);
  clauses = [build_clause_ast(n) : n <- rep_rule_nodes(nodes[4])];
  exprs = build_sel_expr_asts(nodes[5]);
  return syn_map_comp(key_expr, value_expr, clauses, exprs);
}

SynLCExpr build_seq_cp_expr_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 7;

  expr     = build_expr_ast(nodes[0]);
  vars     = [var(get_lowercase_id(n)) : n <- rep_rule_nodes(nodes[2])];
  idx_var  = if nodes[3] == null_match then nil else {ns = rule_seq_nodes(nodes[3]); return just(var(get_lowercase_id(ns[1])));} end; //## UGLY UGLY UGLY
  src_expr = build_expr_ast(nodes[5]);
  sel_expr = if nodes[6] == null_match then nil else {ns = rule_seq_nodes(nodes[6]); return just(build_expr_ast(ns[1]));} end; //## UGLY UGLY UGLY

  return seq_comp(
    expr: expr,
    vars: vars,
    idx_var: value(idx_var) if idx_var /= nil,
    src_expr: src_expr,
    sel_expr: value(sel_expr) if sel_expr /= nil
  );
}

SynExpr build_alt_cp_expr_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 4;
  clauses = [build_clause_ast(n) : n <- rep_rule_nodes(nodes[1])];
  exprs = build_sel_expr_asts(nodes[2]);
  expr_match = nodes[3].match;
  if (nodes[3].name == :set)
    return syn_set_comp(build_expr_ast(expr_match), clauses, exprs);
  else
    key_expr = build_expr_ast(get_rule_seq_node(expr_match, 0));
    value_expr = build_expr_ast(get_rule_seq_node(expr_match, 2));
    return syn_map_comp(key_expr, value_expr, clauses, exprs);
  ;
}

SynExpr build_if_else_expr_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 5;
  branches = [build_if_then_branch_ast(n) : n <- rep_rule_nodes(nodes[1])];
  else_expr = build_expr_ast(nodes[3]);
  return syn_if_expr(branches, else_expr);

  build_if_then_branch_ast(RuleMatch mtc)
  {
    nodes = rule_seq_nodes(mtc);
    assert length(nodes) == 3;
    cond = build_expr_ast(nodes[0]);
    expr = build_expr_ast(nodes[2]);
    return (expr: expr, cond: cond);
  }
}

SynExpr build_match_expr_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 4;
  exprs = [build_expr_ast(n) : n <- rep_rule_nodes(nodes[1])];
  cases = [build_switch_case_ast(n) : n <- rep_rule_nodes(nodes[2])];
  return syn_try_expr(exprs, cases);
}

SynExpr build_proc_expr_ast(RuleMatch mtc) = syn_do_expr(build_stmts_ast(mtc));

SynExpr build_select_expr_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 5;
  sel_type = build_type_ast(nodes[1]);
  expr = build_expr_ast(nodes[3]);
  return syn_select_expr(sel_type, expr);
}

SynExpr build_replace_expr_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  sel_type = build_type_ast(nodes[1]);
  var = var(get_lowercase_id(nodes[2]));
  src_expr = build_expr_ast(nodes[4]);
  expr = build_expr_ast(nodes[6]);
  return syn_replace_expr(expr, src_expr, sel_type, var);
}

SynExpr build_fn_call_expr_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 2;
  fn_name = build_fn_symbol_ast(nodes[0]);

  nodes = rule_seq_nodes(nodes[1]);
  assert length(nodes) == 2;

  params = [build_expr_ast(rule_seq_nodes(n)[1]) : n <- rep_rule_nodes(nodes[0])];
  named_pars = [build_actual_named_par_ast(rule_seq_nodes(n)[1]) : n <- rep_rule_nodes(nodes[1])];

  return syn_fn_call(fn_name, params, named_pars);

  SynFnDef build_actual_named_par_ast(RuleMatch mtc)
  {
    nodes = rule_seq_nodes(mtc);
    assert length(nodes) == 4;

    name = build_fn_symbol_ast(nodes[0]);
    params = [(var: var(get_lowercase_id(n))) : n <- rep_rule_nodes(nodes[1])];
    expr = build_expr_ast(nodes[3]);

    return syn_fn_def(
      name:       name,
      params:     params,
      expr:       expr,
      local_fns:  []
    );
  }
}

////////////////////////////////////////////////////////////////////////////////

SynSubExpr build_subexpr_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 2;
  expr = build_expr_ast(nodes[0]);
  return expr if nodes[1] == null_match;
  nodes = rule_seq_nodes(nodes[1]);
  assert length(nodes) == 2;
  assert get_lowercase_id(nodes[0]) == :if;
  cond = build_expr_ast(nodes[1]);
  return cond_expr(expr, cond);
}

SynMapExprEntry build_map_entry_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 4;
  key = build_expr_ast(nodes[0]);
  value = build_expr_ast(nodes[2]);
  // return (key: key, value: value, cond: build_expr_ast(rule_seq_nodes(nodes[3])[1]) if nodes[3] /= null_match); //## REENABLE
  return (key: key, value: value) if nodes[3] == null_match;
  cond_nodes = rule_seq_nodes(nodes[3]);
  cond = build_expr_ast(cond_nodes[1]);
  return (key: key, value: value, cond: cond);
}

SynMapExprEntry build_record_field_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 3;
  label = object(get_label(nodes[0]));
  expr = build_expr_ast(nodes[1]);
  return (key: label, value: expr) if nodes[2] == null_match;
  nodes = rule_seq_nodes(nodes[2]);
  assert get_lowercase_id(nodes[0]) == :if;
  cond = build_expr_ast(nodes[1]);
  return (key: label, value: expr, cond: cond);
}

//## THIS FUNCTION IS EXTREMELY SPECIAL-PURPOSE, THINK OF A MORE SPECIFIC NAME.
[SynExpr] build_sel_expr_asts(RuleMatch mtc)
{
  return [] if mtc == null_match;
  nodes = rule_seq_nodes(mtc);
  return [build_expr_ast(n) : n <- rep_rule_nodes(nodes[1])];
}

////////////////////////////////////////////////////////////////////////////////

[SynStmt^] build_stmts_ast(RuleMatch mtc) = [build_stmt_ast(n) : n <- rep_rule_nodes(mtc)];

SynStmt build_stmt_ast(RuleMatch mtc) =
  match (mtc.name)
    asgnm       = build_asgnm_stmt_ast(mtc.match),
    ret         = build_ret_stmt_ast(mtc.match),
    if_stmt     = build_if_stmt_ast(mtc.match),
    loop_stmt   = build_loop_stmt_ast(mtc.match),
    while_stmt  = build_while_stmt_ast(mtc.match),
    let_stmt    = build_let_stmt_ast(mtc.match),
    break_stmt  = build_break_stmt_ast(mtc.match),
    for_stmt    = build_for_stmt_ast(mtc.match),
    fail_stmt   = build_fail_stmt_ast(mtc.match),
    assert_stmt = build_assert_stmt_ast(mtc.match),
    print_stmt  = build_print_stmt_ast(mtc.match),
    imp_update  = build_imp_update_stmt(mtc.match),
    fn          = syn_fn_def_stmt(build_std_fndef_ast(mtc.match)),
    fn_proc     = syn_fn_def_stmt(build_proc_fndef_ast(mtc.match)),
    fn_case     = syn_fn_def_stmt(build_switch_fndef_ast(mtc.match));
  ;

SynStmt build_asgnm_stmt_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 6;
  assert nodes[0] == null_match;
  vars = [var(get_lowercase_id(n)) : n <- rep_rule_nodes(nodes[1])];
  assert vars /= [];
  expr = build_expr_ast(nodes[3]);
  stmt = syn_asgnm_stmt(vars, expr);
  return stmt if nodes[4] == null_match;
  cond = build_expr_ast(get_rule_seq_node(nodes[4], 1));
  return syn_if_stmt(cond, [stmt]);
}

SynStmt build_ret_stmt_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 4;
  expr = build_expr_ast(nodes[1]);
  stmt = syn_ret_stmt(expr);
  return stmt if nodes[2] == null_match;
  cond = build_expr_ast(get_rule_seq_node(nodes[2], 1));
  return syn_if_stmt(cond, [stmt]);
}

SynStmt build_if_stmt_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 6;
  cond = build_expr_ast(nodes[1]);
  stmts = build_stmts_ast(nodes[2]);
  branches = [(cond: cond, body: stmts)];
  for (n : rep_rule_nodes(nodes[3]))
    cond = build_expr_ast(get_rule_seq_node(n, 1));
    stmts = build_stmts_ast(get_rule_seq_node(n, 2));
    branches = branches & [(cond: cond, body: stmts)];
  ;
  else_stmts = if nodes[4] /= null_match then build_stmts_ast(get_rule_seq_node(nodes[4], 1)) else [] end;
  return syn_if_stmt(branches, else_stmts);
}

SynStmt build_loop_stmt_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  stmts = build_stmts_ast(nodes[1]);
  return syn_inf_loop_stmt(stmts) if nodes[2] == null_match;
  cond = build_expr_ast(get_rule_seq_node(nodes[2], 1));
  return syn_loop_stmt(cond, stmts, true);
}

SynStmt build_while_stmt_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  cond = build_expr_ast(nodes[1]);
  stmts = build_stmts_ast(nodes[2]);
  return syn_loop_stmt(cond, stmts);
}

SynStmt build_let_stmt_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  asgnms = [build_let_asgnm_ast(n) : n <- rep_rule_nodes(nodes[1])];
  stmts = build_stmts_ast(nodes[2]);
  return syn_let_stmt(asgnms, stmts);

  SynFnDef build_let_asgnm_ast(RuleMatch mtc)
  {
    name = fn_symbol(get_lowercase_id(mtc, 0));
    expr = build_expr_ast(get_rule_seq_node(mtc, 2));
    return syn_fn_def(name: name, expr: expr, params: [], local_fns: []);
  }
}

SynStmt build_break_stmt_ast(RuleMatch mtc)
{
  if_node = get_rule_seq_node(mtc, 1);
  return break_stmt if if_node == null_match;
  cond = build_expr_ast(get_rule_seq_node(if_node, 1));
  return syn_if_stmt(cond, [break_stmt]);
}

SynStmt build_for_stmt_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  iters = [build_iter_ast(n) : n <- rep_rule_nodes(nodes[1])];
  stmts = build_stmts_ast(nodes[2]);
  return syn_for_stmt(iters, stmts);

  SynIter build_iter_ast(RuleMatch mtc)
  {
    nodes = rule_seq_nodes(mtc.match);
    if (mtc.name == :foreach)
      vars = [var(get_lowercase_id(n)) : n <- rep_rule_nodes(nodes[0])];
      expr = build_expr_ast(nodes[2]);
      return syn_seq_iter(vars, expr);
    elif (mtc.name == :foreach_idx)
      vars = [var(get_lowercase_id(n)) : n <- rep_rule_nodes(nodes[0])];
      idx_var = var(get_lowercase_id(nodes[2]));
      expr = build_expr_ast(nodes[4]);
      return syn_seq_iter(vars, idx_var, expr);
    else
      var = var(get_lowercase_id(nodes[0]));
      assert mtc.name == :for;
      start_expr = build_expr_ast(nodes[2]);
      end_expr = build_expr_ast(nodes[4]);
      return syn_range_iter(var, start_expr, end_expr);
    ;
  }
}

SynStmt build_fail_stmt_ast(RuleMatch mtc)
{
  if_node = get_rule_seq_node(mtc, 1);
  return fail_stmt if if_node == null_match;
  cond = build_expr_ast(get_rule_seq_node(if_node, 1));
  return syn_if_stmt(cond, [fail_stmt]);
}

SynStmt build_assert_stmt_ast(RuleMatch mtc) = syn_assert_stmt(build_expr_ast(get_rule_seq_node(mtc, 1)));

SynStmt build_print_stmt_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  expr = build_expr_ast(nodes[1]);
  stmt = syn_print_stmt(expr);
  return stmt if nodes[2] == null_match;
  cond = build_expr_ast(get_rule_seq_node(nodes[2], 1));
  return syn_if_stmt(cond, [stmt]);
}

SynStmt build_imp_update_stmt(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 5;
  var = var(get_lowercase_id(nodes[0]));
  idx_expr = build_expr_ast(nodes[1]);
  value_expr = build_expr_ast(nodes[3]);
  return syn_imp_update_stmt(var, idx_expr, value_expr);
}

////////////////////////////////////////////////////////////////////////////////

SynClause build_clause_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc.match);
  if (mtc.name == :eq)
    var  = var(get_lowercase_id(mtc.match, 0));
    expr = build_expr_ast(get_rule_seq_node(mtc.match, 2));
    return syn_eq_clause(var, expr);
  ;
  assert mtc.name == :in;
  ptrn = build_clause_ptrn_ast(nodes[0]);
  expr = build_expr_ast(nodes[3]);
  return syn_in_clause(ptrn, expr) if nodes[1] == null_match;
  nodes = rule_seq_nodes(nodes[1]);
  value_ptrn = build_clause_ptrn_ast(nodes[1]);
  return syn_map_in_clause(ptrn, value_ptrn, expr);
}

////////////////////////////////////////////////////////////////////////////////

SynPtrn build_clause_ptrn_ast(RuleMatch mtc) =
  match (mtc.name)
    // atomic_rule(underscore)
    any       = ptrn_any,
    // rule_seq([atomic_rule(lowercase_id), empty_block_rule(parenthesis), atomic_rule(lowercase_id)])
    tag_var   = syn_ptrn_var(var(get_lowercase_id(mtc.match, 2)), syn_ptrn_tag_obj(get_lowercase_id(mtc.match, 0))),
    // rule_seq([atomic_rule(lowercase_id), empty_block_rule(parenthesis)])
    tag_only  = syn_ptrn_tag_obj(get_lowercase_id(mtc.match, 0)),
    // rule_seq([atomic_rule(lowercase_id), par_rule(atomic_rule(lowercase_id))])
    tag_obj   = syn_ptrn_tag_obj(ptrn_symbol(get_lowercase_id(mtc.match, 0)), ptrn_var(var(get_lowercase_id(mtc.match, 1)), ptrn_any)),
    // atomic_rule(lowercase_id)
    var       = ptrn_var(var(get_lowercase_id(mtc.match)), ptrn_any);
  ;

////////////////////////////////////////////////////////////////////////////////

SynPtrn build_switch_ptrn_ast(RuleMatch mtc)  //## build_try_ptrn_ast? build_match_ptrn_ast?
{
  nodes = rule_seq_nodes(mtc);
  ptrn_match = nodes[0];
  var_match = nodes[1];
  ptrn = build_switch_ptrn_ast(ptrn_match.name, ptrn_match.match);
  ptrn = syn_ptrn_var(var(get_lowercase_id(var_match, 0)), ptrn) if var_match /= null_match;
  return ptrn;
}

SynPtrn build_switch_ptrn_ast(Atom name, RuleMatch mtc):  //## build_try_ptrn_ast? build_match_ptrn_ast?
  type          = syn_ptrn_type(build_type_ast(mtc)),                 //rule_type
  tag_only      = syn_ptrn_tag_obj(get_lowercase_id(mtc, 0)),         //rule_seq([atomic_rule(lowercase_id), empty_block_rule(parenthesis)])
  tag_obj       = build_switch_ptrn_tag_obj_ast(mtc),                 //rule_seq([atomic_rule(lowercase_id), par_rule(rule_ref_ptrn)])
  tag_obj_any   = build_switch_ptrn_tag_obj_any_ast(mtc),             //rule_seq([atomic_rule(lowercase_id), atomic_rule(at), atomic_rule(lowercase_id)])
  var           = ptrn_var(var(get_lowercase_id(mtc, 0)), ptrn_any),  //rule_seq([atomic_rule(lowercase_id), atomic_rule(question_mark)])
  atom          = ptrn_symbol(get_lowercase_id(mtc)),                 //atomic_rule(lowercase_id)
  integer       = syn_ptrn_integer(get_integer(mtc, 1)),              //rule_seq([optional_rule(atomic_rule(minus)), atomic_rule(integer)])
  float         = ptrn_float,                                         //atomic_rule(circumflex)
  atom_any      = ptrn_symbol,                                        //atomic_rule(plus)
  integer_any   = ptrn_integer,                                       //atomic_rule(asterisk)
  any           = ptrn_any,                                           //atomic_rule(underscore)
  seq           = syn_ptrn_seq,                                       //bracket_rule(atomic_rule(triple_dot))
  set           = syn_ptrn_set,                                       //brace_rule(atomic_rule(triple_dot))
  map           = syn_ptrn_map;                                       //par_rule(atomic_rule(triple_dot))

SynPtrn build_switch_ptrn_tag_obj_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 2;
  tag_ptrn = ptrn_symbol(get_lowercase_id(nodes[0]));
  return syn_ptrn_tag_obj(tag_ptrn, build_switch_ptrn_ast(nodes[1]));
}

SynPtrn build_switch_ptrn_tag_obj_any_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 3;
  tag_ptrn = ptrn_var(var(get_lowercase_id(nodes[0])), ptrn_symbol);
  obj_ptrn = ptrn_var(var(get_lowercase_id(nodes[2])), ptrn_any);
  return syn_ptrn_tag_obj(tag_ptrn, obj_ptrn);
}

////////////////////////////////////////////////////////////////////////////////

SynCase build_switch_case_ast(RuleMatch mtc)
{
  nodes = rule_seq_nodes(mtc);
  assert length(nodes) == 3;
  ptrns = [build_switch_ptrn_ast(n) : n <- rep_rule_nodes(nodes[0])];
  expr = build_expr_ast(nodes[2]);
  return syn_case(ptrns, expr);
}

////////////////////////////////////////////////////////////////////////////////

BasicTypeSymbol build_basic_type_symbol_ast(RuleMatch mtc) = type_symbol(get_lowercase_id(mtc));

////////////////////////////////////////////////////////////////////////////////

Operator token_to_operator(AmberSymb):
  asterisk    = :star,
  slash       = :slash,
  plus        = :plus,
  minus       = :minus,
  ampersand   = :amp,
  lower       = :lower,
  greater     = :greater,
  lower_eq    = :lower_eq,
  greater_eq  = :greater_eq;

////////////////////////////////////////////////////////////////////////////////

//## IN WHAT FILE SHOULD THESE GO?

Bool is_annotated_token(RuleMatch rule, PlainToken token):
  atomic_rule_match(at?)  = at.token == token,
  _                       = false;


AnnotatedToken annotated_token(RuleMatch):
  atomic_rule_match(at?)  = at;

PlainToken get_token(RuleMatch mtc) = annotated_token(mtc).token;

Nat get_integer(RuleMatch mtc)            = get_token(mtc);
FloatLit get_float_lit(RuleMatch mtc)     = get_token(mtc);
Atom get_lowercase_id(RuleMatch mtc)      = _obj_(get_token(mtc));
Atom get_qualified_symbol(RuleMatch mtc)  = _obj_(get_token(mtc));
Atom get_label(RuleMatch mtc)             = _obj_(get_token(mtc));
Atom get_builtin(RuleMatch mtc)           = _obj_(get_token(mtc));
String get_string(RuleMatch mtc)          = get_token(mtc);
Nat get_cls_par_idx(RuleMatch mtc)        = _obj_(get_token(mtc));


AnnotatedToken annotated_token(RuleMatch, Nat idx):
  rule_seq_match(ns?)   = annotated_token(ns[idx]),
  rep_rule_match(ns?)   = annotated_token(ns[idx]);

PlainToken get_token(RuleMatch mtc, Nat idx) = annotated_token(mtc, idx).token;

Nat get_integer(RuleMatch mtc, Nat idx)            = get_token(mtc, idx);
Atom get_lowercase_id(RuleMatch mtc, Nat idx)      = _obj_(get_token(mtc, idx));
Atom get_qualified_symbol(RuleMatch mtc, Nat idx)  = _obj_(get_token(mtc, idx));
Atom get_label(RuleMatch mtc, Nat idx)             = _obj_(get_token(mtc, idx));
Atom get_builtin(RuleMatch mtc, Nat idx)           = _obj_(get_token(mtc, idx));
String get_string(RuleMatch mtc, Nat idx)          = get_token(mtc, idx);

[RuleMatch^] rule_seq_nodes(RuleMatch):
  rule_seq_match(ns?) = ns;

RuleMatch get_rule_seq_node(RuleMatch, Nat idx):
  rule_seq_match(ns?) = ns[idx];

[RuleMatch] rep_rule_nodes(RuleMatch):
  null_match          = [],
  rep_rule_match(ns?) = ns;
