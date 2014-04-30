
using
{
  (TypeSymbol => SynType)   typedefs,
  [BasicTypeSymbol, NzNat]* all_par_type_symbols;


  SynObjErr* fndef_wf_errors(SynFnDef fn_def, UntypedSgn* global_fns, BasicUntypedSgn* impl_pars) =
                  fndef_wf_errors(fn_def, global_fns, {}, impl_pars);

  //## global_fns IS A BAD NAME, THIS COULD BE A LOCAL FUNCTION, A FUNCTION IN A WHERE CLAUSE, 
  //## OR IT COULD BE DEFINED INSIDE A USING BLOCK
  SynObjErr* fndef_wf_errors(SynFnDef fn_def, UntypedSgn* global_fns, TypeVar* type_vars, BasicUntypedSgn* impl_pars)
  {
    vs := set([:fn_par(i) : i <- inc_seq(length(fn_def.params))]); //## BAD BAD BAD

    //## WHAT IF THE LOCAL FUNCTIONS ARE INSIDE A USING BLOCK? IT SHOULD NOT MATTER, BUT I'M NOT QUITE SURE
    all_fns := merge_and_override(global_fns, {untyped_sgn(lfd) : lfd <- set(fn_def.local_fns)});
    ts      := type_vars & select TypeVar in fn_def.params end;

    sgn_errs  := {};

    for (p : fn_def.params)
      if (p.type?)
        sgn_errs := sgn_errs & type_wf_errors(p.type; type_vars_in_scope = ts);
      ;

      if (p.var?)
        sgn_errs := sgn_errs & {:var_redef(p.var)} if in(p.var, vs);
        vs       := vs & {p.var};
      ;
    ;

    ret_type_errs := if fn_def.res_type?
                       then type_wf_errors(fn_def.res_type; type_vars_in_scope = ts)
                       else {}
                     end;

    loc_fns_errs  := seq_union([fndef_wf_errors(fn, all_fns, ts, impl_pars) : fn <- fn_def.local_fns]);
    
    expr_errs     := expr_wf_errors(fn_def.expr, vs; fns_in_scope = all_fns, type_vars_in_scope = ts, impl_params = impl_pars);

    return sgn_errs & ret_type_errs & loc_fns_errs & expr_errs;
  }
}

////////////////////////////////////////////////////////////////////////////////

using
{
  (TypeSymbol => SynType)   typedefs,
  [BasicTypeSymbol, NzNat]* all_par_type_symbols,
  TypeVar*                  type_vars_in_scope,
  UntypedSgn*               fns_in_scope,
  BasicUntypedSgn*          impl_params;


  SynObjErr* expr_wf_errors(SynExpr expr, Var* def_vars):
    object()            = {},

    //seq_expr(head: [SynSubExpr*], tail: SynExpr?)
    seq_expr()          = union({expr_wf_errors(e, def_vars) : e <- set(expr.head)}) &
                          if expr.tail? then expr_wf_errors(expr.tail, def_vars) else {} end,

    //set_expr(SynSubExpr*)
    set_expr(es)        = union({expr_wf_errors(e, def_vars) : e <- es}),
    
    //map_expr((key: SynExpr, value: SynExpr, cond: SynExpr?)*)
    map_expr(es)        = union({expr_wf_errors(se, def_vars) : e <- es, se <- {e.key, e.value, e.cond if e.cond?}}),
    
    //tag_obj_expr(tag: SynExpr, obj: SynExpr)
    tag_obj_expr()      = expr_wf_errors(expr.tag, def_vars) & expr_wf_errors(expr.obj, def_vars),

    Var                 = {:undef_var(expr) if not in(expr, def_vars)},

    const_or_var(a)     = { return {} if in(:var(a), def_vars) or is_def(:fn_symbol(a), 0, fns_in_scope, impl_params);
                            return if is_almost_def(:fn_symbol(a), 0, fns_in_scope)
                                     then {:almost_def_const(a)}
                                     else {:undef_var_or_const(a)};;
                          },

    //where_expr(expr: SynExpr, fndefs: [SynFnDef+]),
    
    //where_expr()        = { ips := impl_params & {untyped_sgn(fd) : fd <- set(expr.fndefs)};
    //                        expr_errs  := expr_wf_errors(expr.expr, def_vars; impl_params = ips);
    //                        fndef_errs := fndefs_wf_errors(set(expr.fndefs), def_vars);
    //                        return expr_errs & fndef_errs;
    //                      },

    // fn_call(name: FnSymbol, params: [ExtSynExpr*], named_params: [SynFnDef*]), //## NEW

    fn_call()           = { ips := impl_params & {untyped_sgn(fd) : fd <- set(expr.named_params)};
    
                            errs := exprs_wf_errors(expr.params, def_vars);

                            //## I DON'T UNDERSTAND WHAT I HAVE DONE HERE
                            if (not is_def(expr.name, length(expr.params), fns_in_scope, ips))
                              err_info := (name: expr.name, arity: length(expr.params));
                              almost_def := is_almost_def(expr.name, length(expr.params), fns_in_scope);
                              errs := errs & {if almost_def then :almost_def_fn(err_info) else :undef_fn(err_info) end};
                            ;
                            
                            np_errs := fndefs_wf_errors(set(expr.named_params), def_vars);
                            //## I SHOULD ALSO CHECK THAT THE NAMED PARAMS THAT I SUPPLY
                            //## ARE ONLY THE ONES THAT ARE REQUIRED BY THE FUNCTION I CALL
                            return errs & np_errs;
                          },

                          //## BAD BAD THIS EXPRESSION IS TOO SIMILAR TO THE ONE ABOVE
    builtin_call()      = exprs_wf_errors(expr.params, def_vars) &
                          {:wrong_num_of_params(name: expr.name, arity: length(expr.params))
                             if not arity_is_correct(expr.name, length(expr.params))},

    and()               = expr_wf_errors(expr.left, def_vars) & expr_wf_errors(expr.right, def_vars),
    or()                = expr_wf_errors(expr.left, def_vars) & expr_wf_errors(expr.right, def_vars), //## BAD
    not(e)              = expr_wf_errors(e, def_vars),
    
    eq()                = expr_wf_errors(expr.left, def_vars) & expr_wf_errors(expr.right, def_vars), //## BAD
    neq()               = expr_wf_errors(expr.left, def_vars) & expr_wf_errors(expr.right, def_vars), //## BAD

    membership()        = expr_wf_errors(expr.obj, def_vars) & type_wf_errors(expr.type),

    accessor()          = expr_wf_errors(expr.expr, def_vars),
    accessor_test()     = expr_wf_errors(expr.expr, def_vars), //## BAD

    ex_qual()           = clauses_wf_errors(expr.source, def_vars) &
                          exprs_wf_errors(expr.sel_exprs, def_vars & syn_new_vars(expr.source)),

    set_comp()          = { vs := def_vars & syn_new_vars(expr.source);  //## BAD, A LET EXPRESSION WOULD BE NICER 
                            return clauses_wf_errors(expr.source, def_vars) &
                                   exprs_wf_errors(expr.sel_exprs, vs) &
                                   expr_wf_errors(expr.expr, vs);
                          },

                          //## BAD BAD BAD THIS EXPRESSION IS TOO SIMILAR TO THE ONES ABOVE
    map_comp()          = { vs := def_vars & syn_new_vars(expr.source);
                            return clauses_wf_errors(expr.source, def_vars) &
                                   exprs_wf_errors(expr.sel_exprs, vs) &
                                   expr_wf_errors(expr.key_expr, vs) &
                                   expr_wf_errors(expr.value_expr, vs);
                          },

    seq_comp()          = { vs   := def_vars & {expr.var, expr.idx_var if expr.idx_var?};
                            errs := expr_wf_errors(expr.src_expr, def_vars) & expr_wf_errors(expr.expr, vs);
                            errs := errs & expr_wf_errors(expr.sel_expr, vs) if expr.sel_expr?;
                            return errs;
                          },

    if_expr()           = expr_wf_errors(expr.else, def_vars) &
                          union(
                            for (b <- set(expr.branches), e <- {b.cond, b.expr})
                              {expr_wf_errors(e, def_vars)}
                          ),

    match_expr()        = exprs_wf_errors(expr.exprs, def_vars) & cases_wf_errors(expr.cases, def_vars),

    do_expr(ss)         = stmts_wf_errors(ss, def_vars),
    
    select_expr()       = type_wf_errors(expr.type) & expr_wf_errors(expr.src_expr, def_vars),
    
    retrieve_expr()     = { vs   := def_vars & new_vars(expr.ptrn);
                            errs := ptrn_wf_errors(expr.ptrn, def_vars);
                            errs := errs & expr_wf_errors(expr.src_expr, def_vars);
                            errs := errs & expr_wf_errors(expr.expr, vs);
                            errs := errs & expr_wf_errors(expr.cond, vs) if expr.cond?;
                            return errs;
                          },
    
    replace_expr()      = ptrn_wf_errors(expr.ptrn, def_vars) &
                          expr_wf_errors(expr.src_expr, def_vars) &
                          expr_wf_errors(expr.src_expr, def_vars & new_vars(expr.ptrn)),
    
    is_expr()           = type_wf_errors(expr.type) & expr_wf_errors(expr.expr, def_vars),
    
                          //## A LET EXPRESSION WOULD BE NICER HERE
    where_expr()        = { ips := impl_params & {untyped_sgn(fd) : fd <- set(expr.fndefs)};
                            expr_errs  := expr_wf_errors(expr.expr, def_vars; impl_params = ips);
                            fndef_errs := fndefs_wf_errors(set(expr.fndefs), def_vars);
                            return expr_errs & fndef_errs;
                          },
    
    let_expr()          = stmts_wf_errors(expr.stmts & [:return_stmt(expr.expr)], def_vars) &
                          expr_wf_errors(expr.expr, def_vars & syn_new_vars(expr.stmts));

  //////////////////////////////////////////////////////////////////////////////

  SynObjErr* fndefs_wf_errors(SynFnDef* fndefs, Var* def_vars)
  {
    dup_errs := for (fd1 <- fndefs, fd2 <- fndefs)
                  if (fd1 /= fd2, untyped_sgn(fd1) == untyped_sgn(fd2)) {
                    :dup_closure_def(untyped_sgn(fd1))
                  };

    return dup_errs & union({fndef_wf_errors(fd, def_vars) : fd <- fndefs});
  }

  SynObjErr* fndef_wf_errors(SynFnDef fndef, Var* def_vars)
  {
    vs       := def_vars;
    sgn_errs := {};
    
    for (p : fndef.params)
      assert not p.type?;

      if (p.var?)
        sgn_errs := sgn_errs & {:var_redef(p.var)} if in(p.var, vs);
        vs       := vs & {p.var};
      ;
    ;
    
    return sgn_errs & expr_wf_errors(fndef.expr, vs);
  }
  
  //////////////////////////////////////////////////////////////////////////////

  SynObjErr* exprs_wf_errors([SynSubExpr*] exprs, Var* vs) = seq_union([expr_wf_errors(e, vs) : e <- exprs]);

  SynObjErr* expr_wf_errors(SynCondExpr se, Var* vs) = expr_wf_errors(se.expr, vs) &
                                                       expr_wf_errors(se.cond, vs);

  //////////////////////////////////////////////////////////////////////////////
  
  SynObjErr* stmts_wf_errors([SynStmt+] stmts, Var* def_vars)
  {
    errs := stmts_wf_errors(stmts, def_vars, def_vars, false);
    errs := errs & {:no_ret_stmt} if not never_falls_through(stmts);
    return errs;
  }


  SynObjErr* stmts_wf_errors([SynStmt*] stmts, Var* all_def_vars, Var* readonly_vars, Bool inside_loop)
  {
    vs        := all_def_vars;
    reachable := true;
    errs      := {};

    for (s : stmts)
      errs      := errs & {:unreachable_code} if not reachable;
      errs      := errs & stmt_wf_errors(s, vs, readonly_vars, inside_loop);
      vs        := vs & syn_new_vars(s);
      reachable := reachable and not syn_is_last_for_sure(s);
    ;

    return errs;
  }


  SynObjErr* stmt_wf_errors(SynStmt stmt, Var* all_def_vars, Var* readonly_vars, Bool inside_loop):
  
    assignment_stmt() = expr_wf_errors(stmt.value, all_def_vars) &
                        {:asgnm_readonly_var(stmt.var) if in(stmt.var, readonly_vars)},

    return_stmt(e)    = expr_wf_errors(e, all_def_vars),

    assert_stmt(e)    = expr_wf_errors(e, all_def_vars),
    print_stmt(e)     = expr_wf_errors(e, all_def_vars),

    :fail_stmt        = {},

    :break_stmt       = {:break_outside_loop if not inside_loop},

    inf_loop_stmt(ss) = stmts_wf_errors(ss, all_def_vars, readonly_vars, true) &
                        {:no_way_out_loop if not has_top_level_break(ss) and not has_return(ss)},

    if_stmt()         = { errs_cond := [expr_wf_errors(b.cond, all_def_vars) : b <- stmt.branches];
                          errs_body := [stmts_wf_errors(b.body, all_def_vars, readonly_vars, inside_loop) : b <- stmt.branches];
                          errs_else := stmts_wf_errors(stmt.else, all_def_vars, readonly_vars, inside_loop);
                          return seq_union(errs_cond) & seq_union(errs_body) & errs_else;
                        },

    loop_stmt()       = { vs := all_def_vars;
                          vs := vs & syn_new_vars(stmt.body) if stmt.skip_first;
                          errs_cond := expr_wf_errors(stmt.cond, vs);
                          errs_body := stmts_wf_errors(stmt.body, all_def_vars, readonly_vars, true);
                          return errs_cond & errs_body;
                        },

    for_stmt()        = { vs   := all_def_vars;
                          errs := {};
                          for (it : stmt.loops)
                            errs := errs & iter_wf_errors(it, vs);
                            vs   := vs & syn_new_vars(it);
                          ;
                          return errs & stmts_wf_errors(stmt.body, vs, readonly_vars, true);
                        },

    let_stmt()        = { asgnms_errs := fndefs_wf_errors(set(stmt.asgnms), all_def_vars);
                          
                          new_impl_params := impl_params & set([untyped_sgn(fd) : fd <- stmt.asgnms]);
                          stmts_errs  := stmts_wf_errors(
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
                    { :var_redef(iter.var) if in(iter.var, def_vars),
                      :var_redef(iter.idx_var) if iter.idx_var? and in(iter.idx_var, def_vars)
                    },
                    
    range_iter()  = expr_wf_errors(iter.start_val, def_vars) &
                    expr_wf_errors(iter.end_val, def_vars)   &
                    {:var_redef(iter.var) if in(iter.var, def_vars)};

  //////////////////////////////////////////////////////////////////////////////

  SynObjErr* case_wf_errors(SynCase syn_case, Var* def_vars)
  {
    //## ALSO CHECK THAT THERE ARE NO SHARED VARIABLE AMONG PATTERNS
    //## AND ALSO THAT THEY DON'T HAVE BOUND VARIABLES
    vs   := def_vars;
    errs := {};
    for (p : syn_case.patterns)
      pvs  := new_vars(p);
      errs := errs & {:already_def_ptrn_var(v) : v <- intersection(pvs, vs)};
      errs := errs & {:free_var_in_try_expr(p.name)} if p :: <ptrn_var(name: Var)>; //## BAD BAD
      errs := errs & ptrn_wf_errors(p, {}); //## BAD BAD THIS WOULD GENERATE A WEIRD ERROR MESSAGE...
      vs   := vs & pvs;
    ;
    
    return errs & expr_wf_errors(syn_case.expr, vs);
  }

  SynObjErr* cases_wf_errors([SynCase+] cs, Var* vs) = seq_union([case_wf_errors(c, vs) : c <- cs]);
  
  //////////////////////////////////////////////////////////////////////////////

  SynObjErr* clause_wf_errors(SynClause clause, Var* ext_vars) = clause_wf_errors(clause, {}, ext_vars);

  SynObjErr* clause_wf_errors(SynClause clause, Var* loc_vars, Var* ext_vars):

    //in_clause(ptrn: Pattern, src: SynExpr)
    in_clause()         = ptrn_wf_errors(clause.ptrn, ext_vars) &
                          expr_wf_errors(clause.src, loc_vars & ext_vars),

    //## IN AN EXCLUSION CLAUSE, CAN THE PATTERN HAVE FREE VARIABLES, APART FROM THE ANONYMOUS ONE?
    //## HOW IS THE ANONYMOUS VAR (_) REPRESENTED, ANYWAY?

    //not_in_clause(ptrn: Pattern, src: SynExpr)
    not_in_clause()     = { ptrn_errs := ptrn_wf_errors(clause.ptrn, ext_vars);
                            vs := new_vars(clause.ptrn) - loc_vars;
                            ptrn_errs := ptrn_errs & {:unbound_vars_in_excl_clause(vs)} if vs /= {};
                            expr_errs := expr_wf_errors(clause.src, ext_vars);
                            return ptrn_errs & expr_errs;
                          },

    //map_in_clause(key_ptrn: Pattern, value_ptrn: Pattern, src: SynExpr)
    map_in_clause()     = ptrn_wf_errors(clause.key_ptrn, ext_vars)   &
                          ptrn_wf_errors(clause.value_ptrn, ext_vars) &
                          expr_wf_errors(clause.src, loc_vars & ext_vars),

    //map_not_in_clause(key_ptrn: Pattern, value_ptrn: Pattern, src: SynExpr)
    map_not_in_clause() = { ptrn_errs := ptrn_wf_errors(clause.key_ptrn, ext_vars) &
                                         ptrn_wf_errors(clause.value_ptrn, ext_vars);
                            vs := new_vars(clause.key_ptrn) & new_vars(clause.value_ptrn) - loc_vars;
                            ptrn_errs := ptrn_errs & {:unbound_vars_in_excl_clause(vs)} if vs /= {};
                            expr_errs := expr_wf_errors(clause.src, ext_vars);
                            return ptrn_errs & expr_errs;
                          },

    //eq_clause(var: Var, expr: SynExpr)
    eq_clause()         = expr_wf_errors(clause.expr, loc_vars & ext_vars) &
                          {:already_def_ptrn_var(clause.var) if in(clause.var, loc_vars & ext_vars)},
    
    //and_clause([SynClause+])
    and_clause(cs)      = { vs   := loc_vars;
                            errs := {};
                            for (c : cs)
                              errs := errs & clause_wf_errors(c, vs, ext_vars);
                              vs   := vs & syn_new_vars(c);
                            ;
                            return errs;
                          },
    
    //or_clause(left: SynClause, right: SynClause)
    or_clause()         = clause_wf_errors(clause.left, loc_vars, ext_vars) &
                          clause_wf_errors(clause.right, loc_vars, ext_vars);


  SynObjErr* clauses_wf_errors([SynClause+] clauses, Var* def_vars) =
                                                    clause_wf_errors(:and_clause(clauses), def_vars);

  //////////////////////////////////////////////////////////////////////////////

  //## loc_vars AND ext_vars SHOULD PROBABLY BE IMPLICIT VARS

  SynObjErr* ptrn_wf_errors(Pattern ptrn, Var* ext_vars):

    obj_ptrn()      = {},

    type_ptrn(type) = type_wf_errors(type),

    ext_var_ptrn(v) = {:undef_bound_ptrn_var(v) if not in(v, ext_vars)},

    var_ptrn()      = { vs := if ptrn.ptrn? then new_vars(ptrn.ptrn) else {} end;
                        var_errs  := if in(ptrn.name, vs) then :dupl_ptrn_vars({ptrn.name}) else {} end;
                        ptrn_errs := if ptrn.ptrn? then ptrn_wf_errors(ptrn.ptrn, ext_vars) else {} end;
                        return var_errs & ptrn_errs;
                      },

    tuple_ptrn()    = { //## BAD BAD BAD THERE SHOULD BE A WAY TO DO THIS
                        //## WITHOUT CONVERTING THE SEQUENCE TO AN ARRAY FIRST
                        bs   := rand_sort(ptrn.fields);
                        len  := length(bs);
                        ls   := [b.label : b <- bs];
                        bvs  := [new_vars(b.ptrn) : b <- bs];

                        dupl_labs := {};
                        dupl_vars := {};
                        for (i1 = 0..len-2 ; i2 = i1+1..len-1)
                          dupl_labs := dupl_labs & {ls[i1]} if ls[i1] == ls[i2];
                          vs := intersection(bvs[i1], bvs[i2]);
                          dupl_vars := dupl_vars & vs if vs /= {};
                        ;

                        dupl_lab_errs := if dupl_labs == {} then {} else :dupl_ptrn_labels(dupl_labs) end;
                        dupl_var_errs := if dupl_vars == {} then {} else :dupl_ptrn_vars(dupl_vars) end;
                        sub_ptrn_errs := union({ptrn_wf_errors(f.ptrn, ext_vars) : f <- ptrn.fields});
                          
                        return dupl_lab_errs & dupl_var_errs & sub_ptrn_errs;
                      },

    //tag_ptrn(tag: <obj_ptrn(Symbol), var_ptrn(name: Var)>, obj: Pattern)
    tag_ptrn()      = { errs := ptrn_wf_errors(ptrn.obj, ext_vars);
                        tag_ptrn := ptrn.tag;
                        if (tag_ptrn :: <var_ptrn(name: Var)>) //## BAD BAD BAD
                          var := tag_ptrn.name;
                          obj_vs := new_vars(ptrn.obj);
                          errs := errs & {:dupl_ptrn_vars({var})} if in(var, obj_vs);
                        ;
                        return errs;
                      };
}

////////////////////////////////////////////////////////////////////////////////

Bool syn_is_last_for_sure(SynStmt stmt):
  return_stmt()     = true,
  :fail_stmt        = true,
  if_stmt()         = all([at_least_one([syn_is_last_for_sure(s) : s <- b.body]) : b <- stmt.branches])
                      and at_least_one([syn_is_last_for_sure(s) : s <- stmt.else]),
  inf_loop_stmt(ss) = none([syn_can_break_loop(s) : s <- ss]),
  //:break_stmt     = //## NOT SURE HERE
  _                 = false;


Bool syn_can_break_loop(SynStmt stmt):
  :break_stmt = true,
  if_stmt()   = at_least_one([at_least_one([syn_can_break_loop(s) : s <- b.body]) : b <- stmt.branches])
                or at_least_one([syn_can_break_loop(s) : s <- stmt.else]),
  _           = false;


Bool has_top_level_break([SynStmt*] stmts)
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
Bool has_return([SynStmt*] stmts) = select <return_stmt(Any)> in stmts end /= {}; //## BAD BAD BAD

Bool never_falls_through(SynStmt stmt):
  return_stmt()     = true,
  :fail_stmt        = true,
  
  inf_loop_stmt(ss) = not has_top_level_break(ss),
  
  if_stmt()         = { for (b : stmt.branches) //## BAD BAD BAD A LOOP SHOULDN'T BE NEEDED
                          return false if not never_falls_through(b.body);
                        ;
                        return never_falls_through(stmt.else);
                      },

  //## WHY DID I DO THIS? IT MAKES NO SENSE...
  //loop_stmt()       = never_falls_through(stmt.body),
  //for_stmt()        = never_falls_through(stmt.body), //## BAD
  
  _                 = false;
  

//## BAD BAD BAD A LOOP SHOULDN'T BE NEEDED
Bool never_falls_through([SynStmt*] stmts)
{
  for (s : stmts)
    return true if never_falls_through(s);
  ;
  return false;
}

