
using
{
  (TypeSymbol => Type)  typedefs,
  TypeVar*              type_vars,
  FnDef*                fns_in_scope,
  //Var*                  scalar_vars,
  (Var => NzNat)        cls_vars;


  Tautology expr_is_wf(Expr expr, Var* scalar_vars)
  {
    return false if (? e <- ordinary_subexprs(expr) : not expr_is_wf(e, scalar_vars));
    gvs := scalar_vars & gen_vars(expr);
    return false if (? e <- special_subexprs(expr) : not expr_is_wf(e, gvs));
    return rest_is_wf(expr, scalar_vars);
    
    rest_is_wf(expr, scalar_vars):
      Var              = in(expr, scalar_vars),
      fn_call()        = fn_call_is_wf(expr, fns_in_scope, scalar_vars),
      cls_call()       = has_key(cls_vars, expr.name) and cls_vars[expr.name] == length(expr.params),
      builtin_call()   = arity_is_correct(expr.name, length(expr.params)),
      membership()     = type_is_wf(expr.type, type_vars),
      ex_qual()        = clause_is_wf(expr.source, scalar_vars),
      set_comp()       = clause_is_wf(expr.source, scalar_vars),
      map_comp()       = clause_is_wf(expr.source, scalar_vars),
      seq_comp()       = (not expr.idx_var? or expr.var /= expr.idx_var) and disjoint(gen_vars(expr), scalar_vars),
      match_expr()     = all([case_is_wf(c, scalar_vars, length(expr.exprs)) : c <- expr.cases]),
      do_expr(ss)      = stmts_are_wf(ss, scalar_vars),
      select_expr()    = ptrn_is_wf(expr.ptrn, scalar_vars),
      replace_expr()   = ptrn_is_wf(expr.ptrn, scalar_vars),
      //where_expr()     = { gen_params := for (fd <- expr.fndefs) {
      //                                     untyped_sgn(name: fd.name, arity: length(fd.vars))
      //                                   };
      //                     new_named_params := named_params & gen_params; //## BAD, IT'S NECESSARY BECAUSE OF A BUG OF THE INTERPRETER
      //                     return expr_is_wf(expr.expr, scalar_vars; named_params = new_named_params);
      //                   },
      _                = true;
  }


  Bool fn_call_is_wf(Expr fn_call, FnDef* fndefs, Var* scalar_vars)   //## BAD BAD BAD THE FIRST PARAMETERS SHOULD BE OF A MORE SPECIFIC TYPE
  {
    return (? fd <- fndefs : could_match(fn_call, fd, scalar_vars));
    
    Bool could_match(Expr fn_call, FnDef fndef, Var* scalar_vars)     //## BAD BAD BAD THE FIRST PARAMETERS SHOULD BE OF A MORE SPECIFIC TYPE
    {
      //print "could_match#1";
      return false if fn_call.name /= fndef.name;
      //print "could_match#2";
      return false if length(fn_call.params) /= arity(fndef);
      //print "could_match#3";
      
      for (i : indexes(fn_call.params))
        actual_par := fn_call.params[i];
        formal_par := fndef.params[i];
        if (formal_par.type?)
          return false if arity(actual_par) /= arity(formal_par.type);
        else
        //print "could_match#4";
          return false if arity(actual_par) /= 0;
        ;
        //print "could_match#5";
      ;
      
      for (v : keys(fndef.named_params))
        //print "could_match#6";
        par_arity := arity(fndef.named_params[v]);
        //print "could_match#7";
        if (has_key(fn_call.named_params, v))
          //print "could_match#8";
          return false if arity(fn_call.named_params[v]) /= par_arity;
          //print "could_match#9";
        elif (has_key(cls_vars, v))
          //print "could_match#10";
          return false if cls_vars[v] /= par_arity;
          //print "could_match#11";
        elif (in(v, scalar_vars))
          return false if par_arity /= 0;
        else
          return false;
        ;
      ;
      
      return true;  
    }
  }

// fn_call(name: FnSymbol, params: [ExtExpr*], named_params: (<named_par(Atom)> => ExtExpr)), //## NEW BAD BAD

//type FnDef      = fn_def(
//                    name:         FnSymbol,
//                    params:       [(var: var(Atom)?, type: ExtType?)*], //## BAD BAD
//                    named_params: (<named_par(Atom)> => ExtType), //## NEW BAD BAD THIS DOESN'T ALLOW FOR IMPLICIT PARAMETER WITH THE SAME NAME BUT DIFFERENT ARITIES. ALSO THE TYPE IS TOO LOOSE. INCLUDE A CHECK IN THE WELL-FORMEDNESS CHECKING LAYER
//                    res_type:     Type?,
//                    expr:         Expr
//                    //impl_env: Signature*,
//                  );

  Tautology case_is_wf(<(ptrns: [Pattern+], expr: Expr)> case, Var *scalar_vars, NzNat arg_count) //## UGLY UGLY
  {
    return false if length(case.ptrns) /= arg_count;
    
    vs := scalar_vars;
    
    for (p : case.ptrns)
      pvs := new_vars(p);
      // Passing an empty ext env here allows for detection of bound variables.
      return false if not disjoint(pvs, vs) or not ptrn_is_wf(p, {});
      return false if p :: <var_ptrn(name: Var)>;  //## BAD BAD BAD
      vs  := vs & pvs;
    ;

    return expr_is_wf(case.expr, vs);  
  }

  //////////////////////////////////////////////////////////////////////////////

  //Tautology clause_is_wf(Clause clause, Var* ext_vars) = clause_is_wf(clause, ext_vars, {});
  //
  //Tautology clause_is_wf(Clause clause, Var* ext_vars, Var* loc_vars): //## BAD BAD BAD

  //  in_clause()         = ptrn_is_wf(clause.ptrn, ext_vars) and
  //                        expr_is_wf(clause.src, ext_vars & loc_vars),

  //  not_in_clause()     = ptrn_is_wf(clause.ptrn, ext_vars) and
  //                        expr_is_wf(clause.src, ext_vars & loc_vars),
  //                        //## WHAT WAS THIS FOR?
  //                        //and disjoint(new_vars(clause.ptrn), vars_in_scope),

  //  map_in_clause()     = ptrn_is_wf(clause.key_ptrn, ext_vars)   and
  //                        ptrn_is_wf(clause.value_ptrn, ext_vars) and
  //                        expr_is_wf(clause.src, ext_vars & loc_vars),
  //  
  //  map_not_in_clause() = ptrn_is_wf(clause.key_ptrn, ext_vars)   and
  //                        ptrn_is_wf(clause.value_ptrn, ext_vars) and
  //                        expr_is_wf(clause.src, ext_vars & loc_vars),
  //                        //## WHAT WAS THIS FOR?
  //                        //and disjoint(new_vars(clause.ptrn), vars_in_scope),

  //  and_clause()        = clause_is_wf(clause.left, ext_vars, loc_vars) and
  //                        clause_is_wf(clause.right, ext_vars, loc_vars & new_vars(clause.left)),

  //  or_clause()         = clause_is_wf(clause.left, ext_vars, loc_vars) and
  //                        clause_is_wf(clause.right, ext_vars, loc_vars);

  Tautology clause_is_wf(Clause clause, Var* ext_vars):

    in_clause()         = ptrn_is_wf(clause.ptrn, ext_vars) and
                          expr_is_wf(clause.src, ext_vars),

    not_in_clause()     = ptrn_is_wf(clause.ptrn, ext_vars) and
                          expr_is_wf(clause.src, ext_vars),
                          //## WHAT WAS THIS FOR?
                          //and disjoint(new_vars(clause.ptrn), vars_in_scope),

    map_in_clause()     = ptrn_is_wf(clause.key_ptrn, ext_vars)   and
                          ptrn_is_wf(clause.value_ptrn, ext_vars) and
                          expr_is_wf(clause.src, ext_vars),
    
    map_not_in_clause() = ptrn_is_wf(clause.key_ptrn, ext_vars)   and
                          ptrn_is_wf(clause.value_ptrn, ext_vars) and
                          expr_is_wf(clause.src, ext_vars),
                          //## WHAT WAS THIS FOR?
                          //and disjoint(new_vars(clause.ptrn), vars_in_scope),

    and_clause()        = clause_is_wf(clause.left, ext_vars) and
                          clause_is_wf(clause.right, ext_vars & new_vars(clause.left)),

    or_clause()         = clause_is_wf(clause.left, ext_vars) and
                          clause_is_wf(clause.right, ext_vars);

  //////////////////////////////////////////////////////////////////////////////

  Tautology ptrn_is_wf(Pattern ptrn, Var* ext_vars):

    obj_ptrn()        = true,

    //## NOT SURE ABOUT TYPE VARS HERE. SHOULD I ALLOW THEM IN PATTERNS?
    //## IN ANY CASE, I DON'T THINK THIS IS CHECKED AT LEVEL 1, SO FIX THAT
    type_ptrn(t)      = type_is_wf(t, {}),

    ext_var_ptrn(v)   = in(v, ext_vars),

    var_ptrn()        = { return false if in(ptrn.name, ext_vars);
                          return true  if not ptrn.ptrn?;
                          return not in(ptrn.name, new_vars(ptrn.ptrn)) and
                                 ptrn_is_wf(ptrn.ptrn, ext_vars);
                        },

    //## WHICH ONE IS BETTER THE PREVIOUS ONE OR THIS ONE?
    //## I DON'T PARTICULARLY LIKE EITHER. IS THERE A BETTER WAY?
    //var_ptrn()        = not in(ptrn.name, ext_vars) and
    //                    ( not ptrn.ptrn? or
    //                      ( not in(ptrn.name, new_vars(ptrn.ptrn)) and
    //                        ptrn_is_wf(ptrn.ptrn, ext_vars)
    //                      )
    //                    ),

    tuple_ptrn()      = { ls := apply(ptrn.fields; f(b) = b.label);
                          return false if (? l => c <- ls : c > 1);
                          fs := ptrn.fields;
                          return false if (? b <- fs : not ptrn_is_wf(b.ptrn, ext_vars));
                          //## BAD BAD BAD
                          return not (? b1 <- fs, b2 <- fs : b1 /= b2,
                                        not disjoint(new_vars(b1.ptrn), new_vars(b2.ptrn)));
                        },

    tag_ptrn()        = { if (ptrn.tag :: <var_ptrn(Any)>) //## BAD BAD BAD
                            return false if in(ptrn.tag.name, new_vars(ptrn.obj));
                          ;
                          return ptrn_is_wf(ptrn.obj, ext_vars);                        
                        };

  //////////////////////////////////////////////////////////////////////////////

  Tautology stmts_are_wf([Statement+] stmts, Var* scalar_vars) = stmts_are_wf(stmts, scalar_vars, false, true);

  Tautology stmts_are_wf([Statement+] stmts, Var* scalar_vars, Bool is_inside_loop, Bool needs_return)
  {
    vs        := scalar_vars;
    reachable := true;

    for (s, i : stmts)
      return false if not reachable or not stmt_is_wf(s, vs, is_inside_loop);
      vs        := vs & new_vars(s);
      reachable := reachable and not is_last_for_sure(s);
    ;

    return not needs_return or not reachable;
  }

  
  Tautology stmt_is_wf(Statement stmt, Var* scalar_vars, Bool is_inside_loop):

    assignment_stmt() = expr_is_wf(stmt.value, scalar_vars), // and (not stmt.type? or type_is_wf(stmt.type)),
    
    return_stmt(e)    = expr_is_wf(e, scalar_vars),
    
    :break_stmt       = is_inside_loop,
    
    :fail_stmt        = true,
    
    assert_stmt(e)    = expr_is_wf(e, scalar_vars),
    
    print_stmt(e)     = expr_is_wf(e, scalar_vars),

    if_stmt()         = expr_is_wf(stmt.cond, scalar_vars)                          and
                        stmts_are_wf(stmt.body, scalar_vars, is_inside_loop, false) and
                        (stmt.else == [] or stmts_are_wf(stmt.else, scalar_vars, is_inside_loop, false)),
    
    let_stmt()        = not (? _ => e <- stmt.asgnms : not expr_is_wf(e, scalar_vars)) and
                        stmts_are_wf(
                          stmt.body,
                          scalar_vars & {v : v => Expr e <- stmt.asgnms},
                          is_inside_loop,
                          false;
                          //## HUGE BUG HERE BUG BUG BUG
                          cls_vars = cls_vars & (v => length(e.params) : v => ClsExpr e <- stmt.asgnms) //## BAD BAD BUG WHAT HAPPENS IF THE LET STATEMENT REDEFINE A NAMED PARAM CHANGING ITS ARITY?
                        ),

//                  let_stmt(asgnms: (<var(Atom)> => ExtExpr), body: [Statement+]), //## NEW BAD BAD

                        //## THERE MUST BE A WAY OUT, A BREAK OR A RETURN
    loop_stmt(ss)     = stmts_are_wf(ss, scalar_vars, true, false),
    
                        //## SHOULD THE LOOP VARIABLES BE READ-ONLY?
    foreach_stmt()    = { nvs := {stmt.var, stmt.idx_var if stmt.idx_var?};
                          return disjoint(nvs, scalar_vars)           and
                                 expr_is_wf(stmt.values, scalar_vars) and
                                 stmts_are_wf(stmt.body, scalar_vars & nvs, true, false);
                        },

                        //## SHOULD THE LOOP VARIABLES BE READ-ONLY?
    for_stmt()        = not in(stmt.var, scalar_vars)            and
                        expr_is_wf(stmt.start_val, scalar_vars)  and
                        expr_is_wf(stmt.end_val, scalar_vars)    and
                        stmts_are_wf(stmt.body, scalar_vars & {stmt.var}, true, false);
}
