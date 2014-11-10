
using
{
  (SynTypeSymbol => SynType)                typedefs,
  (symbol: BasicTypeSymbol, arity: NzNat)*  all_par_type_symbols;


  SynObjErr* fndef_wf_errors(SynFnDef fn_def, UntypedSgn* global_fns, BasicUntypedSgn* impl_pars) =
                  fndef_wf_errors(fn_def, global_fns, {}, impl_pars);

  //## global_fns IS A BAD NAME, THIS COULD BE A LOCAL FUNCTION, A FUNCTION IN A WHERE CLAUSE, 
  //## OR IT COULD BE DEFINED INSIDE A USING BLOCK
  SynObjErr* fndef_wf_errors(SynFnDef fn_def, UntypedSgn* global_fns, TypeVar* type_vars, BasicUntypedSgn* impl_pars)
  {
    vs = set([:fn_par(i) : i <- indexes(fn_def.params)]); //## BAD BAD BAD

    //## WHAT IF THE LOCAL FUNCTIONS ARE INSIDE A USING BLOCK? IT SHOULD NOT MATTER, BUT I'M NOT QUITE SURE
    all_fns = merge_and_override(global_fns, {untyped_sgn(lfd) : lfd <- set(fn_def.local_fns)});
    ts      = type_vars & select TypeVar in fn_def.params end;

    sgn_errs  = {};

    for (p : fn_def.params)
      if (p.type?)
        sgn_errs = sgn_errs & type_wf_errors(p.type; type_vars_in_scope = ts);
      ;

      if (p.var?)
        sgn_errs = sgn_errs & {:var_redef(p.var)} if in(p.var, vs);
        vs       = vs & {p.var};
      ;
    ;

    ret_type_errs = if fn_def.res_type?
                       then type_wf_errors(fn_def.res_type; type_vars_in_scope = ts)
                       else {}
                     end;

    loc_fns_errs  = seq_union([fndef_wf_errors(fn, all_fns, ts, impl_pars) : fn <- fn_def.local_fns]);
    
    expr_errs     = expr_wf_errors(fn_def.expr, vs; fns_in_scope = all_fns, type_vars_in_scope = ts, impl_params = impl_pars);

    return sgn_errs & ret_type_errs & loc_fns_errs & expr_errs;
  }
}

////////////////////////////////////////////////////////////////////////////////

using
{
  (SynTypeSymbol => SynType)                typedefs,
  (symbol: BasicTypeSymbol, arity: NzNat)*  all_par_type_symbols,
  TypeVar*                                  type_vars_in_scope,
  UntypedSgn*                               fns_in_scope,
  BasicUntypedSgn*                          impl_params;


  SynObjErr* expr_wf_errors(SynExpr expr, Var* def_vars):
    object()            = {},

    //seq_expr(head: [SynSubExpr], tail: SynExpr?)
    seq_expr()          = union({expr_wf_errors(e, def_vars) : e <- set(expr.head)}) &
                          if expr.tail? then expr_wf_errors(expr.tail, def_vars) else {} end,

    //set_expr(SynSubExpr*)
    set_expr(es?)       = union({expr_wf_errors(e, def_vars) : e <- es}),
    
    //map_expr((key: SynExpr, value: SynExpr, cond: SynExpr?)*)
    map_expr(es?)       = union({expr_wf_errors(se, def_vars) : e <- es, se <- {e.key, e.value, e.cond if e.cond?}}),
    
    //tag_obj_expr(tag: SynExpr, obj: SynExpr)
    tag_obj_expr()      = expr_wf_errors(expr.tag, def_vars) & expr_wf_errors(expr.obj, def_vars),

    Var                 = {:undef_var(expr) if not in(expr, def_vars)},

    const_or_var(a?)    = { return {} if in(:var(a), def_vars) or is_def(:fn_symbol(a), 0, fns_in_scope, impl_params);
                            return if is_almost_def(:fn_symbol(a), 0, fns_in_scope)
                                     then {:almost_def_const(a)}
                                     else {:undef_var_or_const(a)}
                                   end;
                          },

    //where_expr(expr: SynExpr, fndefs: [SynFnDef^]),
    
    //where_expr()        = { ips = impl_params & {untyped_sgn(fd) : fd <- set(expr.fndefs)};
    //                        expr_errs  = expr_wf_errors(expr.expr, def_vars; impl_params = ips);
    //                        fndef_errs = fndefs_wf_errors(set(expr.fndefs), def_vars);
    //                        return expr_errs & fndef_errs;
    //                      },

    // fn_call(name: FnSymbol, params: [ExtSynExpr], named_params: [SynFnDef]), //## NEW

    fn_call()           = { ips = impl_params & {untyped_sgn(fd) : fd <- set(expr.named_params)};
    
                            errs = exprs_wf_errors(expr.params, def_vars);

                            //## I DON'T UNDERSTAND WHAT I HAVE DONE HERE
                            if (not is_def(expr.name, length(expr.params), fns_in_scope, ips))
                              err_info = (name: expr.name, arity: length(expr.params));
                              almost_def = is_almost_def(expr.name, length(expr.params), fns_in_scope);
                              errs = errs & {if almost_def then :almost_def_fn(err_info) else :undef_fn(err_info) end};
                            ;
                            
                            np_errs = fndefs_wf_errors(set(expr.named_params), def_vars);
                            //## I SHOULD ALSO CHECK THAT THE NAMED PARAMS THAT I SUPPLY
                            //## ARE ONLY THE ONES THAT ARE REQUIRED BY THE FUNCTION I CALL
                            return errs & np_errs;
                          },

                          //## BAD BAD THIS EXPRESSION IS TOO SIMILAR TO THE ONE ABOVE
    builtin_call()      = exprs_wf_errors(expr.params, def_vars) &
                          {wrong_num_of_params(name: expr.name, arity: length(expr.params))
                             if not arity_is_correct(expr.name, length(expr.params))},

    and()               = expr_wf_errors(expr.left, def_vars) & expr_wf_errors(expr.right, def_vars),
    or()                = expr_wf_errors(expr.left, def_vars) & expr_wf_errors(expr.right, def_vars), //## BAD
    not(e?)             = expr_wf_errors(e, def_vars),
    
    eq()                = expr_wf_errors(expr.left, def_vars) & expr_wf_errors(expr.right, def_vars), //## BAD
    neq()               = expr_wf_errors(expr.left, def_vars) & expr_wf_errors(expr.right, def_vars), //## BAD

    membership()        = expr_wf_errors(expr.obj, def_vars) & type_wf_errors(expr.type),
    cast_expr()         = expr_wf_errors(expr.expr, def_vars) & type_wf_errors(expr.type),

    accessor()          = expr_wf_errors(expr.expr, def_vars),
    accessor_test()     = expr_wf_errors(expr.expr, def_vars), //## BAD

    ex_qual()           = clauses_wf_errors(expr.source, def_vars) &
                          exprs_wf_errors(expr.sel_exprs, def_vars & syn_new_vars(expr.source)),

    set_comp()          = { vs = def_vars & syn_new_vars(expr.source);  //## BAD, A LET EXPRESSION WOULD BE NICER 
                            return clauses_wf_errors(expr.source, def_vars) &
                                   exprs_wf_errors(expr.sel_exprs, vs) &
                                   expr_wf_errors(expr.expr, vs);
                          },

                          //## BAD BAD BAD THIS EXPRESSION IS TOO SIMILAR TO THE ONES ABOVE
    map_comp()          = { vs = def_vars & syn_new_vars(expr.source);
                            return clauses_wf_errors(expr.source, def_vars) &
                                   exprs_wf_errors(expr.sel_exprs, vs) &
                                   expr_wf_errors(expr.key_expr, vs) &
                                   expr_wf_errors(expr.value_expr, vs);
                          },

    seq_comp()          = { vs   = def_vars & set(expr.vars) & {expr.idx_var if expr.idx_var?};
                            errs = expr_wf_errors(expr.src_expr, def_vars) & expr_wf_errors(expr.expr, vs);
                            errs = errs & expr_wf_errors(expr.sel_expr, vs) if expr.sel_expr?;
                            errs = errs & {:rep_asgn_var(v) : v <- dupl_elems(expr.vars)};
                            return errs;
                          },

    if_expr()           = expr_wf_errors(expr.else, def_vars) &
                          union(
                            for (b <- set(expr.branches), e <- {b.cond, b.expr})
                              {expr_wf_errors(e, def_vars)}
                          ),

    match_expr()        = exprs_wf_errors(expr.exprs, def_vars) & cases_wf_errors(expr.cases, def_vars),

    do_expr(ss?)        = stmts_wf_errors(ss, def_vars),
    
    select_expr()       = type_wf_errors(expr.type) & expr_wf_errors(expr.src_expr, def_vars),
    
    // retrieve_expr()     = { vs   = def_vars & syn_new_vars(expr.ptrn);
    //                         errs = ptrn_wf_errors(expr.ptrn, def_vars);
    //                         errs = errs & expr_wf_errors(expr.src_expr, def_vars);
    //                         errs = errs & expr_wf_errors(expr.expr, vs);
    //                         errs = errs & expr_wf_errors(expr.cond, vs) if expr.cond?;
    //                         return errs;
    //                       },
    
    replace_expr()      = {:var_redef(expr.var) if in(expr.var, def_vars)} &
                          type_wf_errors(expr.type) &
                          expr_wf_errors(expr.src_expr, def_vars) &
                          expr_wf_errors(expr.src_expr, def_vars & {expr.var}),
    
    is_expr()           = type_wf_errors(expr.type) & expr_wf_errors(expr.expr, def_vars),
    
                          //## A LET EXPRESSION WOULD BE NICER HERE
    where_expr()        = { ips = impl_params & {untyped_sgn(fd) : fd <- set(expr.fndefs)};
                            expr_errs  = expr_wf_errors(expr.expr, def_vars; impl_params = ips);
                            fndef_errs = fndefs_wf_errors(set(expr.fndefs), def_vars);
                            return expr_errs & fndef_errs;
                          },
    
    let_expr()          = stmts_wf_errors(expr.stmts & [:return_stmt(expr.expr)], def_vars) &
                          expr_wf_errors(expr.expr, def_vars & syn_new_vars(expr.stmts));

  //////////////////////////////////////////////////////////////////////////////

  SynObjErr* fndefs_wf_errors(SynFnDef* fndefs, Var* def_vars)
  {
    dup_errs = for (fd1 <- fndefs, fd2 <- fndefs)
                  if (fd1 /= fd2, untyped_sgn(fd1) == untyped_sgn(fd2)) {
                    :dup_closure_def(untyped_sgn(fd1))
                  };

    return dup_errs & union({fndef_wf_errors(fd, def_vars) : fd <- fndefs});
  }

  SynObjErr* fndef_wf_errors(SynFnDef fndef, Var* def_vars)
  {
    vs       = def_vars;
    sgn_errs = {};
    
    for (p : fndef.params)
      assert not p.type?;

      if (p.var?)
        sgn_errs = sgn_errs & {:var_redef(p.var)} if in(p.var, vs);
        vs       = vs & {p.var};
      ;
    ;
    
    return sgn_errs & expr_wf_errors(fndef.expr, vs);
  }
  
  //////////////////////////////////////////////////////////////////////////////

  SynObjErr* exprs_wf_errors([SynSubExpr] exprs, Var* vs) = seq_union([expr_wf_errors(e, vs) : e <- exprs]);

  SynObjErr* expr_wf_errors(SynCondExpr se, Var* vs) = expr_wf_errors(se.expr, vs) &
                                                       expr_wf_errors(se.cond, vs);

  //////////////////////////////////////////////////////////////////////////////
  
  SynObjErr* stmts_wf_errors([SynStmt^] stmts, Var* def_vars)
  {
    errs = stmts_wf_errors(stmts, def_vars, def_vars, false);
    errs = errs & {:no_ret_stmt} if not never_falls_through(stmts);
    return errs;
  }


  SynObjErr* stmts_wf_errors([SynStmt] stmts, Var* all_def_vars, Var* readonly_vars, Bool inside_loop)
  {
    vs        = all_def_vars;
    reachable = true;
    errs      = {};
    for (s : stmts)
      errs      = errs & {:unreachable_code} if not reachable;
      errs      = errs & stmt_wf_errors(s, vs, readonly_vars, inside_loop);
      vs        = vs & syn_new_vars(s);
      reachable = reachable and not syn_is_last_for_sure(s);
    ;

    return errs;
  }


  SynObjErr* stmt_wf_errors(SynStmt stmt, Var* all_def_vars, Var* readonly_vars, Bool inside_loop):
  
    //## BUG: SHOULD ALSO CHECK THAT THE VARIABLES ARE ALL DIFFERENT
    assignment_stmt()   = expr_wf_errors(stmt.value, all_def_vars) &
                          {:asgnm_readonly_var(v) : v <- set(stmt.vars), in(v, readonly_vars)} &
                          {:rep_asgn_var(v) : v <- dupl_elems(stmt.vars)},

    return_stmt(e?)     = expr_wf_errors(e, all_def_vars),

    assert_stmt(e?)     = expr_wf_errors(e, all_def_vars),
    print_stmt(e?)      = expr_wf_errors(e, all_def_vars),

    fail_stmt           = {},

    break_stmt          = {:break_outside_loop if not inside_loop},

    inf_loop_stmt(ss?)  = stmts_wf_errors(ss, all_def_vars, readonly_vars, true) &
                          {:no_way_out_loop if not has_top_level_break(ss) and not has_return(ss)},

    if_stmt()           = { errs_cond = [expr_wf_errors(b.cond, all_def_vars) : b <- stmt.branches];
                            errs_body = [stmts_wf_errors(b.body, all_def_vars, readonly_vars, inside_loop) : b <- stmt.branches];
                            errs_else = stmts_wf_errors(stmt.else, all_def_vars, readonly_vars, inside_loop);
                            return seq_union(errs_cond) & seq_union(errs_body) & errs_else;
                          },

    loop_stmt()         = { vs = all_def_vars;
                            vs = vs & syn_new_vars(stmt.body) if stmt.skip_first;
                            errs_cond = expr_wf_errors(stmt.cond, vs);
                            errs_body = stmts_wf_errors(stmt.body, all_def_vars, readonly_vars, true);
                            return errs_cond & errs_body;
                          },

    for_stmt()          = { vs   = all_def_vars;
                            errs = {};
                            for (it : stmt.loops)
                              errs = errs & iter_wf_errors(it, vs);
                              vs   = vs & syn_new_vars(it);
                            ;
                            return errs & stmts_wf_errors(stmt.body, vs, readonly_vars, true);
                          },

    let_stmt()          = { asgnms_errs = fndefs_wf_errors(set(stmt.asgnms), all_def_vars);

                            new_impl_params = impl_params & set([untyped_sgn(fd) : fd <- stmt.asgnms]);
                            stmts_errs  = stmts_wf_errors(
                                             stmt.body,
                                             all_def_vars,
                                             readonly_vars,
                                             inside_loop;
                                             impl_params = new_impl_params
                                           );

                            //## I SHOULD ALSO CHECK THAT I'M NOT DEFINING NEW IMPLICIT PARAMS
                            //## BUT ONLY REDEFINING EXISTING ONES. I'LL CATCH MOST ERRORS ANYWAY
                            //## THOUGH AS I'M PASSING ONTO THE BODY STATEMENTS THE SAME IMPLICIT
                            //## ENVIRONMENT THAT I GET AS INPUT
                            return asgnms_errs & stmts_errs;
                          };


  SynObjErr* iter_wf_errors(SynIter iter, Var* def_vars):
  
    seq_iter()    = expr_wf_errors(iter.values, def_vars) &
                    {:rep_asgn_var(v) : v <- dupl_elems(iter.vars)} &
                    {:var_redef(iter.v) : v <- set(iter.vars), in(v, def_vars)} &
                    {:var_redef(iter.idx_var) if iter.idx_var? and in(iter.idx_var, def_vars)},
                    
    range_iter()  = expr_wf_errors(iter.start_val, def_vars) &
                    expr_wf_errors(iter.end_val, def_vars)   &
                    {:var_redef(iter.var) if in(iter.var, def_vars)};

  //////////////////////////////////////////////////////////////////////////////

  SynObjErr* case_wf_errors(SynCase syn_case, Var* def_vars)
  {
    //## ALSO CHECK THAT THERE ARE NO SHARED VARIABLE AMONG PATTERNS
    //## AND ALSO THAT THEY DON'T HAVE BOUND VARIABLES
    vs   = def_vars;
    errs = {};
    for (p : syn_case.patterns)
      pvs  = syn_new_vars(p);
      errs = errs & {:already_def_ptrn_var(v) : v <- intersection(pvs, vs)};
      // errs = errs & {:free_var_in_try_expr(p.name)} if p :: <ptrn_var(name: Var)>; //## BAD BAD
      errs = errs & ptrn_wf_errors(p, {}); //## BAD BAD THIS WOULD GENERATE A WEIRD ERROR MESSAGE...
      vs   = vs & pvs;
    ;
    
    return errs & expr_wf_errors(syn_case.expr, vs);
  }

  SynObjErr* cases_wf_errors([SynCase^] cs, Var* vs) = seq_union([case_wf_errors(c, vs) : c <- cs]);
  
  //////////////////////////////////////////////////////////////////////////////

  SynObjErr* clause_wf_errors(SynClause clause, Var* ext_vars) = clause_wf_errors(clause, {}, ext_vars);

  SynObjErr* clause_wf_errors(SynClause clause, Var* loc_vars, Var* ext_vars):

    //in_clause(ptrn: Pattern, src: SynExpr)
    in_clause()         = ptrn_wf_errors(clause.ptrn, ext_vars) &
                          expr_wf_errors(clause.src, loc_vars & ext_vars),

    //map_in_clause(key_ptrn: Pattern, value_ptrn: Pattern, src: SynExpr)
    map_in_clause()     = ptrn_wf_errors(clause.key_ptrn, ext_vars)   &
                          ptrn_wf_errors(clause.value_ptrn, ext_vars) &
                          expr_wf_errors(clause.src, loc_vars & ext_vars),

    //eq_clause(var: Var, expr: SynExpr)
    eq_clause()         = expr_wf_errors(clause.expr, loc_vars & ext_vars) &
                          {:already_def_ptrn_var(clause.var) if in(clause.var, loc_vars & ext_vars)},
    
    //and_clause([SynClause^])
    and_clause(cs?)     = { vs   = loc_vars;
                            errs = {};
                            for (c : cs)
                              errs = errs & clause_wf_errors(c, vs, ext_vars);
                              vs   = vs & syn_new_vars(c);
                            ;
                            return errs;
                          },
    
    //or_clause(left: SynClause, right: SynClause)
    or_clause()         = clause_wf_errors(clause.left, loc_vars, ext_vars) &
                          clause_wf_errors(clause.right, loc_vars, ext_vars);


  SynObjErr* clauses_wf_errors([SynClause^] clauses, Var* def_vars) =
                                                    clause_wf_errors(:and_clause(clauses), def_vars);

  //////////////////////////////////////////////////////////////////////////////

  //## loc_vars AND ext_vars SHOULD PROBABLY BE IMPLICIT VARS

  SynObjErr* ptrn_wf_errors(SynPtrn ptrn, Var* ext_vars):
    ptrn_symbol       = {},
    ptrn_integer      = {},
    ptrn_seq          = {},
    ptrn_set          = {},
    ptrn_map          = {},
    ptrn_tag_obj      = {},
    ptrn_any          = {},
    ptrn_symbol()     = {},
    ptrn_integer()    = {},
    ptrn_tag_obj()    = {
      errs = ptrn_wf_errors(ptrn.tag, ext_vars) & ptrn_wf_errors(ptrn.obj, ext_vars);
      tag_vars = syn_new_vars(ptrn.tag);
      obj_vars = syn_new_vars(ptrn.obj);
      common_vars = intersection(tag_vars, obj_vars);
      errs = errs & {:dupl_ptrn_vars(common_vars)} if common_vars /= {};
      return errs;
    },
    ptrn_var()        = {
      vs = syn_new_vars(ptrn.ptrn);
      var_errs  = {:dupl_ptrn_vars({ptrn.name}) if in(ptrn.var, vs), :var_redef({ptrn.var}) if in(ptrn.var, ext_vars)};
      ptrn_errs = ptrn_wf_errors(ptrn.ptrn, ext_vars);

      return var_errs & ptrn_errs;
    },
    ptrn_type(type?)  = type_wf_errors(type);
}

////////////////////////////////////////////////////////////////////////////////

Bool syn_is_last_for_sure(SynStmt stmt):
  return_stmt()       = true,
  fail_stmt           = true,
  if_stmt()           = all([at_least_one([syn_is_last_for_sure(s) : s <- b.body]) : b <- stmt.branches])
                        and at_least_one([syn_is_last_for_sure(s) : s <- stmt.else]),
  inf_loop_stmt(ss?)  = none([syn_can_break_loop(s) : s <- ss]),
  //:break_stmt         = //## NOT SURE HERE
  let_stmt()          = at_least_one([syn_is_last_for_sure(s) : s <- stmt.body]),
  _                   = false;


Bool syn_can_break_loop(SynStmt stmt):
  break_stmt  = true,
  if_stmt()   = at_least_one([at_least_one([syn_can_break_loop(s) : s <- b.body]) : b <- stmt.branches])
                or at_least_one([syn_can_break_loop(s) : s <- stmt.else]),
  _           = false;


Bool has_top_level_break([SynStmt] stmts)
{
  for (s : stmts)
    return true if s == :break_stmt;
    
    if (s :: <if_stmt(Any)>) //## BAD BAD BAD
      //## BAD BAD BAD A LOOP SHOULD NOT BE NECESSARY HERE
      for (b : s.branches)
        return true if has_top_level_break(b.body);
      ;
      return true if has_top_level_break(s.else);
    ;
  ;
  
  return false;    
}

//## BUG BUG BUG IF THE RETURN STATEMENT IS INSIDE A NESTED,
//## DO EXPRESSION IT EXITS THAT AND NOT THE MAIN ONE
Bool has_return([SynStmt] stmts) = select <return_stmt(Any)> in stmts end /= {}; //## BAD BAD BAD

Bool never_falls_through(SynStmt stmt):
  return_stmt()       = true,
  fail_stmt           = true,
  
  inf_loop_stmt(ss?)  = not has_top_level_break(ss),
  
  if_stmt()           = { for (b : stmt.branches) //## BAD BAD BAD A LOOP SHOULDN'T BE NEEDED
                            return false if not never_falls_through(b.body);
                          ;
                          return never_falls_through(stmt.else);
                        },

  let_stmt()          = never_falls_through(stmt.body),

  //## WHY DID I DO THIS? IT MAKES NO SENSE...
  //loop_stmt()       = never_falls_through(stmt.body),
  //for_stmt()        = never_falls_through(stmt.body), //## BAD
  
  _                   = false;
  

//## BAD BAD BAD A LOOP SHOULDN'T BE NEEDED
Bool never_falls_through([SynStmt] stmts)
{
  for (s : stmts)
    return true if never_falls_through(s);
  ;
  return false;
}

