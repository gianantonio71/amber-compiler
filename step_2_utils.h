
Expr* ordinary_subexprs(Expr expr):
  object()        = {},
  seq_expr()      = union({subexprs(e) : e <- set(expr.head)}) & {expr.tail if expr.tail?},
  set_expr(ses?)  = union({subexprs(e) : e <- ses}),
  map_expr(es?)   = union({{e.key, e.value, e.cond if e.cond?} : e <- es}),
  tag_obj_expr()  = {expr.tag, expr.obj},
  Var             = {},
  fn_call()       = set(expr.params),
  cls_call()      = set(expr.params), //## BAD
  builtin_call()  = set(expr.params), //## BAD
  and_expr()      = {expr.left, expr.right},
  or_expr()       = {expr.left, expr.right}, //## BAD
  not_expr(e?)    = {e},
  eq()            = {expr.left, expr.right}, //## BAD
  membership()    = {expr.obj},
  cast_expr()     = {expr.expr},
  accessor()      = {expr.expr},
  accessor_test() = {expr.expr},
  if_expr()       = {expr.cond, expr.then, expr.else},
  // Expression that contain "special" subexpressions
  ex_qual()       = {},
  set_comp()      = {},
  map_comp()      = {},
  seq_comp()      = {expr.src_expr},
  select_expr()   = {expr.src_expr},
  // Expression that require special treatment
  replace_expr()  = {expr.src_expr},
  match_expr()    = set(expr.exprs),
  do_expr()       = {};

//## FIND BETTER NAME
Expr* subexprs(Expr expr)     = {expr};
Expr* subexprs(CondExpr expr) = {expr.expr, expr.cond};

Expr* special_subexprs(Expr expr):
  ex_qual()       = {expr.sel_expr if expr.sel_expr?},
  set_comp()      = {expr.expr, expr.sel_expr if expr.sel_expr?},
  map_comp()      = {expr.key_expr, expr.value_expr, expr.sel_expr if expr.sel_expr?},
  seq_comp()      = {expr.expr, expr.sel_expr if expr.sel_expr?}, //## BAD
  replace_expr()  = {expr.expr},
  _               = {};

Var* gen_vars(Expr expr):
  ex_qual()       = new_vars(expr.source),
  set_comp()      = new_vars(expr.source), //## BAD
  map_comp()      = new_vars(expr.source), //## BAD
  seq_comp()      = set(expr.vars) & {expr.idx_var if expr.idx_var?},
  replace_expr()  = {expr.var},
  _               = {};

////////////////////////////////////////////////////////////////////////////////

//## IS THIS CODE OK? IN CALCULATING THE NEW VARS, IT DOESN'T
//## CONSIDER THE VARIABLES THAT ARE ALREADY DEFINED

Var* new_vars(Pattern ptrn):
  ptrn_var()      = new_vars(ptrn.ptrn) & {ptrn.var},
  ptrn_tag_obj()  = new_vars(ptrn.tag) & new_vars(ptrn.obj),
  ptrn_union(ps?) = union({new_vars(p) : p <- ps}),
  _               = {};

Var* new_vars(Clause clause):
  in_clause()         = new_vars(clause.ptrn),
  map_in_clause()     = new_vars(clause.key_ptrn) & new_vars(clause.value_ptrn),
  and_clause()        = new_vars(clause.left) & new_vars(clause.right),
  or_clause()         = intersection(new_vars(clause.left), new_vars(clause.right));

Var* new_vars(Statement stmt):
  assignment_stmt() = set(stmt.vars),
  if_stmt()         = intersection({new_vars(stmt.body) if may_fall_through(stmt.body), new_vars(stmt.else) if may_fall_through(stmt.else)}),
  let_stmt()        = new_vars(stmt.body),
  _                 = {};

Var* new_vars([Statement] stmts) = seq_union([new_vars(s) : s <- stmts]);

///////////////////////////////////////////////////////////////////////////////

Var* extern_vars(Expr expr)
{
  ord_expr_evs  = union({extern_vars(e) : e <- ordinary_subexprs(expr)});
  spec_expr_evs = union({extern_vars(e) : e <- special_subexprs(expr)}) - gen_vars(expr);
  spec_case_evs = special_cases(expr);

  return ord_expr_evs & spec_expr_evs & spec_case_evs;

  special_cases(expr):
      Var            = {expr},
      fn_call()      = union({extern_vars(e) : k => e <- expr.named_params}),
      ex_qual()      = extern_vars(expr.source),
      set_comp()     = extern_vars(expr.source), //## BAD
      map_comp()     = extern_vars(expr.source), //## BAD
      do_expr(ss?)   = extern_vars(ss),
      match_expr()   = { vs = {};
                         for (c : expr.cases)
                           pvs = seq_union([new_vars(p) : p <- c.ptrns]);
                           vs  = vs & (extern_vars(c.expr) - pvs);
                         ;
                         return vs;
                       },

      _              = {};
}


Var* extern_vars(Clause clause):
  in_clause()         = extern_vars(clause.src),
  map_in_clause()     = extern_vars(clause.src),
  and_clause()        = extern_vars(clause.left) & (extern_vars(clause.right) - new_vars(clause.left)),
  or_clause()         = extern_vars(clause.left) & extern_vars(clause.right);


Var* extern_vars([Statement] stmts)
{
  //## BUG BUG WHY IS THIS FUNCTION NEVER CALLED?
  
  def_vs = {};
  ext_vs = {};
  for (s : stmts)
    ext_vs = ext_vs & (extern_vars(s) - def_vs);
    def_vs = def_vs & new_vars(s);                            
  ;
  return ext_vs;
}

Var* extern_vars(Statement s):
  assignment_stmt() = extern_vars(s.value),
  return_stmt(e?)   = extern_vars(e),
  if_stmt()         = extern_vars(s.cond) & extern_vars(s.body) & extern_vars(s.else),
  loop_stmt(ss?)    = extern_vars(ss),
  foreach_stmt()    = extern_vars(s.values) & (extern_vars(s.body) - (set(s.vars) & {s.idx_var if s.idx_var?})),
  for_stmt()        = extern_vars(s.start_val) & extern_vars(s.end_val) & (extern_vars(s.body) - {s.var}),
  break_stmt        = {},
  fail_stmt         = {},
  assert_stmt(e?)   = extern_vars(e),
  print_stmt(e?)    = extern_vars(e);

Var* extern_vars(ClsExpr e) = extern_vars(e.expr) - (set(e.params) - {nil});

////////////////////////////////////////////////////////////////////////////////

type StmtOutcome = fails, returns, breaks, falls_through;


StmtOutcome+ outcomes([Statement] stmts)
{
  outcomes = {:falls_through};
  for (s : stmts)
    outcomes = (outcomes - {:falls_through}) & outcomes(s);
    break if not in(:falls_through, outcomes);
  ;
  return outcomes;
}


StmtOutcome+ outcomes(Statement stmt):
  assignment_stmt() = {:fails, :falls_through},
  return_stmt()     = {:fails, :returns},
  if_stmt()         = {:fails} & outcomes(stmt.body) & outcomes(stmt.else),
  loop_stmt(body?)  = {
    outcomes = outcomes(body);
    // Failures and returns in the body are transferred to the loop.
    // Fall throughs in the body are neutralized by the loop, but they
    // create the possibility of an infinite loop, which counts as failure.
    outcomes = (outcomes - {:falls_through}) & {:fails} if in(:falls_through, outcomes);
    // A break in the body becomes a fall through for the loop itself
    outcomes = (outcomes - {:breaks}) & {:falls_through} if in(:breaks, outcomes);
    return outcomes;
  },
  foreach_stmt()    = {:fails, :falls_through} & outcomes(stmt.body) - {:breaks},
  for_stmt()        = {:fails, :falls_through} & outcomes(stmt.body) - {:breaks}, //## BAD: SAME AS ABOVE
  let_stmt()        = {:fails} & outcomes(stmt.body),
  break_stmt        = {:breaks},
  fail_stmt         = {:fails},
  assert_stmt()     = {:falls_through, :fails},
  print_stmt()      = {:falls_through, :fails};

////////////////////////////////////////////////////////////////////////////////

Bool may_fall_through(Statement stmt) = in(:falls_through, outcomes(stmt));

Bool may_fall_through([Statement] stmts) = in(:falls_through, outcomes(stmts));

////////////////////////////////////////////////////////////////////////////////

Bool arity_is_correct(BuiltIn name, NzNat arity) = arity == builtin_arity_map[name];

(BuiltIn => NzNat) builtin_arity_map = (
  neg:         1,
  add:         2,
  str:         1,
  symb:        1,
  at:          2,
  len:         1,
  slice:       3,
  cat:         2,
  mcat:        1,
  rev:         1,
  set:         1,
  mset:        1,
  isort:       1,
  list_to_seq: 1,
  tag:         1,
  obj:         1,
  in:          2,
  has_key:     2,
  lookup:      2,
  union:       1,
  merge:       1,
  rand_nat:    1,
  rand_elem:   1,
  counter:     1
);
