//## CLOSURES SHOULD NOT INHERIT THE IMPLICIT PARAMETERS FROM THE FUNCTION THEY ARE DEFINED IN

using
{
  (TypeName => AnonType)    typedefs,
  (TypeSymbol => UserType)  user_typedefs,
  TypeVar*                  type_vars,
  FnDef*                    fns_in_scope,
  (Var => NzNat)            cls_vars;


  True expr_is_wf(Expr expr, Var* scalar_vars)
  {
    return false if (? e <- ordinary_subexprs(expr) : not expr_is_wf(e, scalar_vars));
    gvs = scalar_vars & gen_vars(expr);
    return false if (? e <- special_subexprs(expr) : not expr_is_wf(e, gvs));
    return rest_is_wf(expr, scalar_vars);
    
    True rest_is_wf(Expr expr, Var* scalar_vars):
      Var              = in(expr, scalar_vars),
      fn_call()        = fn_call_is_wf(expr, fns_in_scope, scalar_vars),
      cls_call()       = has_key(cls_vars, expr.name) and cls_vars[expr.name] == length(expr.params), //## SHOULDN'T IT VERIFY THAT THE ACTUAL PARAMETER EXPRESSIONS ARE WELL FORMED?
      builtin_call()   = arity_is_correct(expr.name, length(expr.params)),
      membership()     = user_type_is_wf(expr.type, type_vars),
      cast_expr()      = user_type_is_wf(expr.type, type_vars),
      ex_qual()        = clause_is_wf(expr.source, scalar_vars),
      set_comp()       = clause_is_wf(expr.source, scalar_vars),
      map_comp()       = clause_is_wf(expr.source, scalar_vars),
      seq_comp()       = (not expr.idx_var? or expr.var /= expr.idx_var) and disjoint(gen_vars(expr), scalar_vars),
      match_expr()     = all([case_is_wf(c, scalar_vars, length(expr.exprs)) : c <- expr.cases]),
      do_expr(ss?)     = stmts_are_wf(ss, scalar_vars),
      select_expr()    = user_type_is_wf(expr.type, type_vars),
      replace_expr()   = user_type_is_wf(expr.type, type_vars) and not in(expr.var, scalar_vars),
      _                = true;
  }


  Bool fn_call_is_wf(Expr fn_call, FnDef* fndefs, Var* scalar_vars)   //## BAD BAD BAD THE FIRST PARAMETERS SHOULD BE OF A MORE SPECIFIC TYPE
  {
    return (? fd <- fndefs : could_match(fn_call, fd, scalar_vars));
    
    Bool could_match(Expr fn_call, FnDef fndef, Var* scalar_vars)     //## BAD BAD BAD THE FIRST PARAMETERS SHOULD BE OF A MORE SPECIFIC TYPE
    {
      return false if fn_call.name /= fndef.name;
      return false if length(fn_call.params) /= arity(fndef);
      
      for (i : indexes(fn_call.params))
        actual_par = fn_call.params[i];
        formal_par = fndef.params[i];
        if (formal_par.type?)
          return false if arity(actual_par) /= arity(formal_par.type);
        else
          return false if arity(actual_par) /= 0;
        ;
      ;
      
      for (v : keys(fndef.named_params))
        par_arity = arity(fndef.named_params[v]);
        if (has_key(fn_call.named_params, v))
          return false if arity(fn_call.named_params[v]) /= par_arity;
        elif (has_key(cls_vars, v))
          return false if cls_vars[v] /= par_arity;
        elif (in(v, scalar_vars))
          return false if par_arity /= 0;
        else
          return false;
        ;
      ;
      
      return true;  
    }
  }


  True case_is_wf(<(ptrns: [Pattern^], expr: Expr)> case, Var *scalar_vars, NzNat arg_count) //## UGLY UGLY
  {
    return false if length(case.ptrns) /= arg_count;
    
    vs = scalar_vars;
    
    for (p : case.ptrns)
      pvs = new_vars(p);
      //## BUG: HERE WE ARE ONLY CHECKING SCALAR VARIABLES. WHAT ABOUT CLOSURES?
      //## AND WHAT ABOUT NAMED PARAMETERS? THEY HAVE A DIFFERENT REPRESENTATION,
      //## EVEN THOUGH THEY LOOK THE SAME TO THE USER. IS THAT A PROBLEM?
      return false if not disjoint(pvs, vs);
      return false if p :: <var_ptrn(name: Var)>;  //## BAD BAD BAD
      vs  = vs & pvs;
    ;

    return expr_is_wf(case.expr, vs);  
  }

  //////////////////////////////////////////////////////////////////////////////

  True stmts_are_wf([Statement^] stmts, Var* scalar_vars) = stmts_are_wf(stmts, scalar_vars, false, true);

  True stmts_are_wf([Statement^] stmts, Var* scalar_vars, Bool is_inside_loop, Bool needs_return)
  {
    vs        = scalar_vars;
    reachable = true;

    for (s, i : stmts)
      return false if not reachable or not stmt_is_wf(s, vs, is_inside_loop);
      vs        = vs & new_vars(s);
      reachable = reachable and may_fall_through(s);
    ;

    return not needs_return or not reachable;
  }

  
  True stmt_is_wf(Statement stmt, Var* scalar_vars, Bool is_inside_loop):

    assignment_stmt() = expr_is_wf(stmt.value, scalar_vars), // and (not stmt.type? or user_type_is_wf(stmt.type)),
    
    return_stmt(e?)   = expr_is_wf(e, scalar_vars),
    
    break_stmt        = is_inside_loop,
    
    fail_stmt         = true,
    
    assert_stmt(e?)   = expr_is_wf(e, scalar_vars),
    
    print_stmt(e?)    = expr_is_wf(e, scalar_vars),

    if_stmt()         = expr_is_wf(stmt.cond, scalar_vars)                          and
                        stmts_are_wf(stmt.body, scalar_vars, is_inside_loop, false) and
                        (stmt.else == [] or stmts_are_wf(stmt.else, scalar_vars, is_inside_loop, false)),
    
    let_stmt()        = not (? _ => e <- stmt.asgnms : not expr_is_wf(e, scalar_vars)) and
                        stmts_are_wf(
                          stmt.body,
                          scalar_vars & keys(stmt.asgnms),
                          is_inside_loop,
                          false;
                          //## HUGE BUG HERE BUG BUG BUG
                          cls_vars = cls_vars & (v => length(e.params) : v => cls_expr() e <- stmt.asgnms) //## BAD BAD BUG WHAT HAPPENS IF THE LET STATEMENT REDEFINE A NAMED PARAM CHANGING ITS ARITY?
                        ),

                        //## THERE MUST BE A WAY OUT, A BREAK OR A RETURN
    loop_stmt(ss?)    = stmts_are_wf(ss, scalar_vars, true, false),
    
                        //## SHOULD THE LOOP VARIABLES BE READ-ONLY?
    foreach_stmt()    = { nvs = {stmt.var, stmt.idx_var if stmt.idx_var?};
                          return disjoint(nvs, scalar_vars)           and
                                 expr_is_wf(stmt.values, scalar_vars) and
                                 stmts_are_wf(stmt.body, scalar_vars & nvs, true, false);
                        },

                        //## SHOULD THE LOOP VARIABLES BE READ-ONLY?
    for_stmt()        = not in(stmt.var, scalar_vars)            and
                        expr_is_wf(stmt.start_val, scalar_vars)  and
                        expr_is_wf(stmt.end_val, scalar_vars)    and
                        stmts_are_wf(stmt.body, scalar_vars & {stmt.var}, true, false);

//////////////////////////////////////////////////////////////////////////////

True clause_is_wf(Clause clause, Var* ext_vars) = clause_is_wf(clause, ext_vars, {});

True clause_is_wf(Clause clause, Var* ext_vars, Var* loc_vars):

  in_clause()         = ptrn_is_wf(clause.ptrn, ext_vars, loc_vars) and
                        expr_is_wf(clause.src, ext_vars & loc_vars),

  map_in_clause()     = ptrn_is_wf(clause.key_ptrn, ext_vars, loc_vars)   and
                        ptrn_is_wf(clause.value_ptrn, ext_vars, loc_vars) and
                        expr_is_wf(clause.src, ext_vars & loc_vars),

  and_clause()        = clause_is_wf(clause.left, ext_vars, loc_vars) and
                        clause_is_wf(clause.right, ext_vars, loc_vars & new_vars(clause.left)),

  or_clause()         = clause_is_wf(clause.left, ext_vars, loc_vars) and
                        clause_is_wf(clause.right, ext_vars, loc_vars);

//////////////////////////////////////////////////////////////////////////////

True ptrn_is_wf(Pattern ptrn, Var* ext_vars, Var* loc_vars) = ptrn_is_wf(ptrn, ext_vars, loc_vars, ptrn_any);

True ptrn_is_wf(Pattern ptrn, Var* ext_vars, Var* loc_vars, Pattern bound_vars_ptrn):

  ptrn_tag_obj()  = ptrn_is_wf(ptrn.tag, ext_vars, loc_vars, ptrn_symbol) and
                    ptrn_is_wf(ptrn.obj, ext_vars, loc_vars, bound_vars_ptrn),

  ptrn_var()      = ptrn_is_wf(ptrn.ptrn, ext_vars, loc_vars, bound_vars_ptrn) and
                    not in(ptrn.var, ext_vars) and not in(ptrn.var, new_vars(ptrn.ptrn)) and
                    (not in(ptrn.var, loc_vars) or ptrn.ptrn == bound_vars_ptrn), //## THIS IS NOT CHECKED IN STAGE 1

  ptrn_union(ps?) = not (? p <- ps : not ptrn_is_wf(p, ext_vars, loc_vars, bound_vars_ptrn)),

  _               = true;
}
