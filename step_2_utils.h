
Expr* ordinary_subexprs(Expr expr):
  object()        = {},
  seq_expr()      = union({subexprs(e) : e <- set(expr.head)}) & {expr.tail if expr.tail?},
  set_expr(ses)   = union({subexprs(e) : e <- ses}),
  map_expr(es)    = union({{e.key, e.value, e.cond if e.cond?} : e <- es}),
  tag_obj_expr()  = {expr.tag, expr.obj},
  Var             = {},
  fn_call()       = set(expr.params),
  cls_call()      = set(expr.params), //## BAD
  builtin_call()  = set(expr.params), //## BAD
  and_expr()      = {expr.left, expr.right},
  or_expr()       = {expr.left, expr.right}, //## BAD
  not_expr(e)     = {e},
  eq()            = {expr.left, expr.right}, //## BAD
  membership()    = {expr.obj},
  accessor()      = {expr.expr},
  accessor_test() = {expr.expr},
  if_expr()       = {expr.cond, expr.then, expr.else},
  // Expression that contain "special" subexpressions
  ex_qual()       = {},
  set_comp()      = {},
  map_comp()      = {},
  seq_comp()      = {expr.src_expr},
  select_expr()   = {expr.src_expr},
  replace_expr()  = {expr.src_expr}, //## BAD
  // Expression that require special treatment
  match_expr()    = set(expr.exprs),
  do_expr()       = {};
  //where_expr()    = {};

//## FIND BETTER NAME
Expr* subexprs(SubExpr expr):
  Expr      = {expr},
  CondExpr  = {expr.expr, expr.cond};

Expr* special_subexprs(Expr expr):
  ex_qual()       = {expr.sel_expr if expr.sel_expr?},
  set_comp()      = {expr.expr, expr.sel_expr if expr.sel_expr?},
  map_comp()      = {expr.key_expr, expr.value_expr, expr.sel_expr if expr.sel_expr?},
  seq_comp()      = {expr.expr, expr.sel_expr if expr.sel_expr?}, //## BAD
  select_expr()   = {expr.expr, expr.sel_expr if expr.sel_expr?}, //## BAD
  replace_expr()  = {expr.expr},
  _               = {};

Var* gen_vars(Expr expr):
  ex_qual()       = new_vars(expr.source),
  set_comp()      = new_vars(expr.source), //## BAD
  map_comp()      = new_vars(expr.source), //## BAD
  seq_comp()      = {expr.var, expr.idx_var if expr.idx_var?},
  select_expr()   = new_vars(expr.ptrn),
  replace_expr()  = new_vars(expr.ptrn),
  _               = {};

////////////////////////////////////////////////////////////////////////////////

//## IS THIS CODE OK? IN CALCULATING THE NEW VARS, IT DOESN'T
//## CONSIDER THE VARIABLES THAT ARE ALREADY DEFINED

Var* new_vars(Pattern ptrn):
  obj_ptrn()      = {},
  type_ptrn()     = {},
  ext_var_ptrn()  = {},
  var_ptrn()      = {ptrn.name} & if ptrn.ptrn? then new_vars(ptrn.ptrn) else {} end,
  tuple_ptrn()    = union({new_vars(f.ptrn) : f <- ptrn.fields}),
  tag_ptrn()      = new_vars(ptrn.tag) & new_vars(ptrn.obj);

Var* new_vars(Clause clause):
  in_clause()         = new_vars(clause.ptrn),
  not_in_clause()     = {},
  map_in_clause()     = new_vars(clause.key_ptrn) & new_vars(clause.value_ptrn),
  map_not_in_clause() = {},
  and_clause()        = new_vars(clause.left) & new_vars(clause.right),
  or_clause()         = intersection(new_vars(clause.left), new_vars(clause.right));

Var* new_vars(Statement stmt):
  assignment_stmt() = {stmt.var},
  if_stmt()         = intersection(new_vars(stmt.body), new_vars(stmt.else)),
  let_stmt()        = new_vars(stmt.body),  
  _                 = {};

Var* new_vars([Statement*] stmts) = seq_union([new_vars(s) : s <- stmts]);

///////////////////////////////////////////////////////////////////////////////

Var* extern_vars(Expr expr)
{
  ord_expr_evs  := union({extern_vars(e) : e <- ordinary_subexprs(expr)});
  spec_expr_evs := union({extern_vars(e) : e <- special_subexprs(expr)}) - gen_vars(expr);
  spec_case_evs := special_cases(expr);

  return ord_expr_evs & spec_expr_evs & spec_case_evs;

  special_cases(expr):
      Var            = {expr},
      fn_call()      = union({extern_vars(e) : k => e <- expr.named_params}),
      ex_qual()      = extern_vars(expr.source),
      set_comp()     = extern_vars(expr.source), //## BAD
      map_comp()     = extern_vars(expr.source), //## BAD
      do_expr(ss)    = extern_vars(ss),
      select_expr()  = extern_vars(expr.ptrn),
      replace_expr() = extern_vars(expr.ptrn), //## BAD

      //where_expr()   = extern_vars(expr.expr) &
      //                 union({extern_vars(fd.body) - set(fd.vars) : fd <- expr.fndefs}),

      match_expr()   = { vs := {};
                         for (c : expr.cases)
                           pvs := seq_union([new_vars(p) : p <- c.ptrns]);
                           vs  := vs & (extern_vars(c.expr) - pvs);
                         ;
                         return vs;
                       },

      _              = {};
}

Var* extern_vars(Pattern ptrn) = retrieve v from ext_var_ptrn(Var v) in ptrn end;

Var* extern_vars(Clause clause):
  in_clause()         = extern_vars(clause.src) & extern_vars(clause.ptrn),
  not_in_clause()     = extern_vars(clause.src) & extern_vars(clause.ptrn), //## BAD
  map_in_clause()     = extern_vars(clause.src) & extern_vars(clause.key_ptrn) & extern_vars(clause.value_ptrn),
  map_not_in_clause() = extern_vars(clause.src) & extern_vars(clause.key_ptrn) & extern_vars(clause.value_ptrn),
  and_clause()        = extern_vars(clause.left) & (extern_vars(clause.right) - new_vars(clause.left)),
  or_clause()         = extern_vars(clause.left) & extern_vars(clause.right);

Var* extern_vars([Statement*] stmts)
{
  //## BUG BUG WHY IS THIS FUNCTION NEVER CALLED?
  
  def_vs := {};
  ext_vs := {};
  for (s : stmts)
    ext_vs := ext_vs & (extern_vars(s) - def_vs);
    def_vs := def_vs & new_vars(s);                            
  ;
  return ext_vs;
}

Var* extern_vars(Statement s):
  assignment_stmt() = extern_vars(s.value),
  return_stmt(e)    = extern_vars(e),
  if_stmt()         = extern_vars(s.cond) & extern_vars(s.body) & extern_vars(s.else),
  loop_stmt(ss)     = extern_vars(ss),
  foreach_stmt()    = extern_vars(s.values) & (extern_vars(s.body) - {s.var, s.idx_var if s.idx_var?}),
  for_stmt()        = extern_vars(s.start_val) & extern_vars(s.end_val) & (extern_vars(s.body) - {s.var}),
  :break_stmt       = {},
  :fail_stmt        = {},
  assert_stmt(e)    = extern_vars(e),
  print_stmt(e)     = extern_vars(e);

//type ClsExpr  = cls_expr(params: [<var(Atom), nil>+], expr: Expr);

Var* extern_vars(ClsExpr e) = extern_vars(e.expr) - (set(e.params) - {nil});

////////////////////////////////////////////////////////////////////////////////

Bool can_fall_through([Statement*] stmts) = none([is_last_for_sure(s) : s <- stmts]);


Bool is_last_for_sure(Statement stmt):
  return_stmt()   = true,
  :fail_stmt      = true,
  if_stmt()       = at_least_one([is_last_for_sure(s) : s <- stmt.body]) and
                    at_least_one([is_last_for_sure(s) : s <- stmt.else]),
  loop_stmt(ss)   = none([can_break_loop(s) : s <- ss]),
  //:break_stmt     = //## NOT SURE HERE
  _               = false;


Bool can_break_loop(Statement stmt):
  :break_stmt = true,
  if_stmt()   = at_least_one([can_break_loop(s) : s <- stmt.body]) or at_least_one([can_break_loop(s) : s <- stmt.else]),
  let_stmt()  = at_least_one([can_break_loop(s) : s <- stmt.body]), // This should not be necessary for now, but if and when I remove the limitation on the let statement body, it will become
  _           = false;

////////////////////////////////////////////////////////////////////////////////

Bool flow_control_can_jump_out([Statement*] stmts) = flow_control_can_jump_out(stmts, false);

Bool flow_control_can_jump_out([Statement*] stmts, Bool inside_loop) = at_least_one([flow_control_can_jump_out(s, inside_loop) : s <- stmts]);

Bool flow_control_can_jump_out(Statement stmt, Bool inside_loop):
  assignment_stmt() = false,
  return_stmt()     = true,
  if_stmt()         = flow_control_can_jump_out(stmt.body, inside_loop) or flow_control_can_jump_out(stmt.else, inside_loop),
  loop_stmt(ss)     = flow_control_can_jump_out(ss, true),
  foreach_stmt()    = flow_control_can_jump_out(stmt.body, true),
  for_stmt()        = flow_control_can_jump_out(stmt.body, true),
  let_stmt()        = flow_control_can_jump_out(stmt.body, inside_loop),
  :break_stmt       = not inside_loop,
  :fail_stmt        = false,
  assert_stmt()     = false,
  print_stmt()      = false;

////////////////////////////////////////////////////////////////////////////////

Bool arity_is_correct(BuiltIn name, NzNat arity) = arity == arity_map[name]
                                                   let
                                                     arity_map := (
                                                       neg:         1,
                                                       add:         2,
                                                       str:         1,
                                                       symb:        1,
                                                       counter:     1,
                                                       at:          2,
                                                       len:         1,
                                                       slice:       3,
                                                       cat:         2,
                                                       rev:         1,
                                                       set:         1,
                                                       mset:        1,
                                                       isort:       1,
                                                       list_to_seq: 1
                                                     );
                                                   ;
