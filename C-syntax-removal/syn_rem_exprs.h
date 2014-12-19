//## THIS IS PROBABLY THE CRAPPIEST CODE IN THE WHOLE PROJECT

using
{
  BasicUntypedSgn*            clss_in_scope,
  <named_par(Atom)>*          named_params,
  BasicUntypedSgn*            local_fns,
  FnSymbol                    curr_outer_fn,
  (TypeName => AnonType)      typedefs,
  ((FnSymbol, Nat) => [Nat])  fn_param_arities;


  Expr desugar_expr(SynExpr expr, Var* def_vars):

    object()        = expr,

    float_lit()     = expr,
    
    seq_expr(es?)   = seq_expr([desugar_expr(e, def_vars) : e <- es]),

    seq_tail_expr() = seq_tail_expr(
                        seq:  desugar_expr(expr.seq, def_vars),
                        tail: [desugar_expr(e, def_vars) : e <- expr.tail]
                      ),
    
    set_expr(es?)   = :set_expr({desugar_expr(e, def_vars) : e <- es}),
    
    map_expr(es?)   = :map_expr(
                        for (e <- es) {(
                          key:   desugar_expr(e.key, def_vars),
                          value: desugar_expr(e.value, def_vars),
                          cond:  desugar_expr(e.cond, def_vars) if e.cond?
                        )}
                      ),

    tag_obj_expr()  = tag_obj_expr(
                        tag: desugar_expr(expr.tag, def_vars),
                        obj: desugar_expr(expr.obj, def_vars)
                      ),

    Var             = expr,
    
    cls_par(n?)     = fn_par(n),

    const_or_var(a?)  = { return :var(a) if in(:var(a), def_vars);
                          return :named_par(a) if in(:named_par(a), named_params);
                          sgn = untyped_sgn(name: :fn_symbol(a), arity: 0);
                          //## THIS IS A STRANGE LIMITATION
                          //## IS IT HERE FOR A REASON, OR IS IT ONLY TEMPORARY?
                          assert not in(sgn, local_fns);
                          return fn_call(name: :fn_symbol(a), params: [], named_params: ());
                          //if (in(sgn, named_params))
                          //  return cls_call(name: fn, params: []);
                          //else
                          //  return fn_call(name: fn, params: [], named_params: ());
                          //;
                        },

    fn_call()       = { assert length(expr.params) > 0;
    
                        //## BAD (BUG?): THIS IS NOT VALID IF THE PARAMETER IS A CLOSURE
                        //## VARIABLE OR IF IT'S THE NAME OF A FUNCTION. RIGHT NOW IT
                        //## SHOULD NOT FAIL, BUT ONLY BECAUSE THE const_or_var() DOESN'T
                        //## DO ANY CHECKING AT THE MOMENT
                        ps  = [desugar_expr(e, def_vars) : e <- expr.params];
                        sgn = untyped_sgn(name: expr.name, arity: length(expr.params));
                        nps = syn_fn_defs_to_named_params(expr.named_params, def_vars);

                        // Closures first
                        if (in(sgn, clss_in_scope))
                          assert nps == ();
                          ps = [desugar_expr(e, def_vars) : e <- expr.params];
                          return cls_call(name: cls_var(_obj_(expr.name)), params: ps);
                        ;

                        // Then local functions
                        if (in(sgn, local_fns))
                          fs = nested_fn_symbol(outer: curr_outer_fn, inner: expr.name);
                          ps = [desugar_expr(e, def_vars) : e <- expr.params];
                          return fn_call(name: fs, params: ps, named_params: nps);
                        ;
                         
                        // Then named parameters
                        np  = :named_par(_obj_(expr.name));
                        if (in(np, named_params))
                          assert nps == ();
                          return cls_call(name: np, params: ps);
                        ;
                        
                        // And last global functions.
                        // Since here we may have to deal with closure parameters,
                        // we have to transform the plain expressions into closures
                        // if required.

                        pas = fn_param_arities[(expr.name, length(expr.params))];
                        // ps = [if a == 0 then p else cls_expr(a, p) end : p, a <- zip(ps, pas)];
                        fps = [];
                        for (op, dp, a : zip(expr.params, ps, pas))
                          if (a == 0)
                            fp = dp;
                          elif (not op :: ConstOrVar)
                            fp = cls_expr(a, dp);
                          else
                            symb = _obj_(op);
                            if (in(var(symb), def_vars) or in(named_par(symb), named_params))
                              fp = cls_expr(a, dp);
                            else
                              sgn = untyped_sgn(fn_symbol(symb), a);
                              if (in(sgn, clss_in_scope))
                                fp = cls_var(symb);
                              else
                                // assert in(sgn, fns_in_scope);
                                fp = fn_ptr(fn_symbol(symb), a);
                              ;
                            ;
                          ;
                          fps = fps & [fp];
                        ;
                        return fn_call(name: expr.name, params: fps, named_params: nps);
                      },

    builtin_call()  = builtin_call(
                        name: expr.name,
                        params: [desugar_expr(e, def_vars) : e <- expr.params]
                      ),

    and()           = and_expr(
                        left:  desugar_expr(expr.left, def_vars),
                        right: desugar_expr(expr.right, def_vars)
                      ),

    or()            = or_expr(
                        left:  desugar_expr(expr.left, def_vars),
                        right: desugar_expr(expr.right, def_vars)
                      ),

    not(e?)         = :not_expr(desugar_expr(e, def_vars)),
    
    eq()            = eq(
                        left:  desugar_expr(expr.left, def_vars),
                        right: desugar_expr(expr.right, def_vars)
                      ),

    neq()           = :not_expr(                      
                        eq(
                          left:  desugar_expr(expr.left, def_vars),
                          right: desugar_expr(expr.right, def_vars)
                        )
                      ),

    membership()    = membership(obj: desugar_expr(expr.obj, def_vars), type: expr.type),
    cast_expr()     = cast_expr(expr: desugar_expr(expr.expr, def_vars), type: expr.type),

    accessor()      = accessor(expr: desugar_expr(expr.expr, def_vars), field: expr.field),
    accessor_test() = accessor_test(expr: desugar_expr(expr.expr, def_vars), field: expr.field),

    ex_qual()       = { vs = def_vars & syn_new_vars(expr.source);
                        se = [desugar_expr(e, vs) : e <- expr.sel_exprs];
                        return ex_qual(
                                 source:   mk_and_clause(expr.source, def_vars),  //## TODO
                                 sel_expr: mk_and_expr(se) if se /= []
                               );
                      },

    set_comp()      = { vs = def_vars & syn_new_vars(expr.source);
                        se = [desugar_expr(e, vs) : e <- expr.sel_exprs];
                        return set_comp(
                                 expr:     desugar_expr(expr.expr, vs),
                                 source:   mk_and_clause(expr.source, def_vars),
                                 sel_expr: mk_and_expr(se) if se /= []
                               );
                      },

    map_comp()      = { vs = def_vars & syn_new_vars(expr.source);
                        se = [desugar_expr(e, vs) : e <- expr.sel_exprs];
                        return map_comp(
                                 key_expr:   desugar_expr(expr.key_expr, vs),
                                 value_expr: desugar_expr(expr.value_expr, vs),
                                 source:     mk_and_clause(expr.source, def_vars),
                                 sel_expr:   mk_and_expr(se) if se /= []
                               );
                      },

    seq_comp()      = { vs = def_vars & set(expr.vars) & {expr.idx_var if expr.idx_var?};
                        return seq_comp(
                                 expr:     desugar_expr(expr.expr, vs),
                                 vars:     expr.vars,
                                 idx_var:  expr.idx_var if expr.idx_var?,
                                 src_expr: desugar_expr(expr.src_expr, def_vars),
                                 sel_expr: desugar_expr(expr.sel_expr, vs) if expr.sel_expr?
                               );
                      },

    if_expr()       = { res = desugar_expr(expr.else, def_vars);
                        for (b : reverse(expr.branches))
                          res = if_expr(
                                   cond: desugar_expr(b.cond, def_vars),
                                   then: desugar_expr(b.expr, def_vars),
                                   else: res
                                 );
                        ;
                        return res;
                      },

    match_expr()    = { n  = length(expr.cases[0].patterns);
                        es = [desugar_expr(e, def_vars) : e <- subseq(expr.exprs, 0, n)];
                        cs = [{ ps = [desugar_ptrn(p) : p <- c.patterns];
                                 vs = def_vars & seq_union([new_vars(p) : p <- ps]);
                                 return (ptrns: ps, expr: desugar_expr(c.expr, vs));
                               } : c <- expr.cases];
                        return match_expr(exprs: es, cases: cs);
                      },

    do_expr(ss?)    = :do_expr(desugar_stmts(ss, def_vars)), //##  IMPLEMENT

    select_expr()   = select_expr(type: expr.type, src_expr: desugar_expr(expr.src_expr, def_vars)),
    
    replace_expr()  = replace_expr(
                        expr:     desugar_expr(expr.expr, def_vars & {expr.var}),
                        src_expr: desugar_expr(expr.src_expr, def_vars),
                        type:     expr.type,
                        var:      expr.var
                      ),
    
    let_expr()      = :do_expr(desugar_stmts(expr.stmts & [:return_stmt(expr.expr)], def_vars));

  ////////////////////////////////////////////////////////////////////////////////

  CondExpr desugar_expr(SynCondExpr cexpr, Var* def_vars) =
    cond_expr(
      expr: desugar_expr(cexpr.expr, def_vars),
      cond: desugar_expr(cexpr.cond, def_vars)
    );

  
  Expr mk_and_expr([Expr^] exprs)  // REMOVE DUPLICATES?
  {
    len       = length(exprs);
    rev_exprs = reverse(exprs);
    expr      = rev_exprs[0];
    for (i = 1..len-1)
      expr = and_expr(left: rev_exprs[i], right: expr);
    ;
    return expr;  
  }

  ////////////////////////////////////////////////////////////////////////////////

  Clause mk_and_clause([SynClause^] clauses, Var* def_vars)
  {
    vs = def_vars;
    cs = [];
    for (c : clauses)
      cs = cs & [desugar_clause(c, vs)];
      vs = vs & syn_new_vars(c);
    ;

    rev_cs = reverse(cs);
    clause = rev_cs[0];
    for (i = 1..length(clauses)-1)
      clause = and_clause(left: rev_cs[i], right: clause);
    ;

    return clause;
  }

  //## REMEMBER TO CHECK THAT ALL VAR_PTRN() WITH A "BOUND" VARIABLE
  //## DON'T HAVE A PATTERN ASSOCIATED WITH THAT VARIABLE
  
  //## THIS IS A HACK TO GET AROUND A BUG IN THE REPLACE COMMAND IN THE INTERPRETER
  // Pattern replace_bound_vars(Pattern ptrn, Var* def_vars) =
  //   replace var_ptrn() p in ptrn with
  //     if in(p.name, def_vars) then :ext_var_ptrn(p.name) else p end
  //   end;
    

  Clause desugar_clause(SynClause clause, Var* def_vars):

    in_clause()         = in_clause(
                            ptrn: desugar_ptrn(clause.ptrn),
                            src:  desugar_expr(clause.src, def_vars)
                          ),
                      
    map_in_clause()     = map_in_clause(
                            key_ptrn:   desugar_ptrn(clause.key_ptrn),
                            value_ptrn: desugar_ptrn(clause.value_ptrn),
                            src:        desugar_expr(clause.src, def_vars)
                          ),
    
    eq_clause()         = { assert not in(clause.var, def_vars);
                            
                            return in_clause(
                                     ptrn: ptrn_var(clause.var, ptrn_any),
                                     src:  :set_expr({desugar_expr(clause.expr, def_vars)})
                                   );
                          },

    and_clause(cs?)     = mk_and_clause(cs, def_vars),
    
    or_clause()         = or_clause(
                            left:  desugar_clause(clause.left, def_vars),
                            right: desugar_clause(clause.right, def_vars)
                          );

  ////////////////////////////////////////////////////////////////////////////////

  [Statement] desugar_stmts([SynStmt] stmts, Var* def_vars)
  {
    vs = def_vars;
    ss = [];
    for (s : stmts)
      ss = ss & [desugar_stmt(s, vs)];
      vs = vs & syn_new_vars(s);
    ;
    return ss;
  }

  Statement desugar_stmt(SynStmt stmt, Var* def_vars):

    assignment_stmt()   = assignment_stmt(vars: stmt.vars, value: desugar_expr(stmt.value, def_vars)),
    
    return_stmt(e?)     = :return_stmt(desugar_expr(e, def_vars)),
    
    break_stmt          = :break_stmt,
    
    fail_stmt           = :fail_stmt,
    
    assert_stmt(e?)     = :assert_stmt(desugar_expr(e, def_vars)),
    
    print_stmt(e?)      = :print_stmt(desugar_expr(e, def_vars)),

    inf_loop_stmt(ss?)  = :loop_stmt(desugar_stmts(ss, def_vars)),

    if_stmt() =
    {
      res = desugar_stmts(stmt.else, def_vars);
      for (b : reverse(stmt.branches))
        cond = desugar_expr(b.cond, def_vars);
        body = desugar_stmts(b.body, def_vars);
        res  = [if_stmt(cond: cond, body: body, else: res)];
      ;
      assert res :: Seq and length(res) == 1;
      return res[0]; //## BAD BAD BAD
    },

    // let_stmt(asgnms: [SynFnDef^], body: [SynStmt^]), //## NEW
    // let_stmt(asgnms: (<var(Atom)> => ExtExpr), body: [Statement^]), //## NEW BAD BAD
    
    //type SynFnDef       = syn_fn_def(
    //                        name:       FnSymbol,
    //                        params:     [(type: SynType?, var: var(Atom)?)],
    //                        res_type:   SynType?,
    //                        expr:       SynExpr,
    //                        local_fns:  [SynFnDef]
    //                      );

    let_stmt() =
    {
      nps    = named_params & set([:named_par(_obj_(fd.name)) : fd <- stmt.asgnms]); //## BAD BAD BAD
      body   = desugar_stmts(stmt.body, def_vars ,named_params = nps);
      asgnms = syn_fn_defs_to_named_params(stmt.asgnms, def_vars);
      return let_stmt(asgnms: asgnms, body: body);
    },
    
    loop_stmt() =
    {
      cond      = desugar_expr(stmt.cond, def_vars);
      exit_stmt = if_stmt(cond: :not_expr(cond), body: [:break_stmt], else: []);
      body      = desugar_stmts(stmt.body, def_vars);
      if (stmt.skip_first)
        body = body & [exit_stmt];
      else
        body = [exit_stmt] & body;
      ;
      return :loop_stmt(body);
    },

    for_stmt() =
    {
      //## ALSO MAKE SURE SYNTAX CHECK GETS IT RIGHT
      iters  = stmt.loops;
      vs     = def_vars;
      for_vs = [];
      for (it : iters)
        ivs  = match (it)
                 seq_iter()   = set(it.vars),
                 range_iter() = {it.var};
               ;
        vs     = vs & ivs & {it.idx_var if it.idx_var?};
        for_vs = for_vs & [vs];
      ;
      res = desugar_stmts(stmt.body, vs);
      for (it @ i : reverse(iters))
        vs = rev_at(for_vs, i);
        if (it :: <seq_iter(Any)>) //## BAD BAD BAD
          vals = desugar_expr(it.values, vs);
          res  = [ foreach_stmt(
                      vars:    it.vars,
                      idx_var: it.idx_var if it.idx_var?,
                      values:  vals,
                      body:    res
                    )
                  ];
        else
          assert it :: <range_iter(Any)>; //## BAD BAD BAD
          start_val = desugar_expr(it.start_val, vs);
          end_val   = desugar_expr(it.end_val, vs);
          res = [for_stmt(var: it.var, start_val: start_val, end_val: end_val, body: res)];
        ;
      ;
      assert res :: Seq and length(res) == 1;
      return res[0]; //## BAD BAD BAD
    };

  ////////////////////////////////////////////////////////////////////////////////

  Pattern desugar_ptrn(SynPtrn ptrn):
    ptrn_seq                = ptrn_seq,
    ptrn_set                = ptrn_set,
    ptrn_map                = ptrn_map,
    ptrn_integer(int_obj?)  = ptrn_integer(int_obj),
    ptrn_tag_obj()          = ptrn_tag_obj(ptrn.tag, desugar_ptrn(ptrn.obj)),
    ptrn_var()              = ptrn_var(ptrn.var, desugar_ptrn(ptrn.ptrn)),
    ptrn_type(type?)        = {
      if (not user_type_can_be_converted_into_pattern(type, typedefs))
        // print type;
        assert type /= :type_ref(:type_symbol(:set)); //## WHY THIS?
      ;
      return user_type_to_pattern(type, typedefs);
    },
    _                       = ptrn;

  ////////////////////////////////////////////////////////////////////////////////

  //## FIND BETTER NAME
  (<named_par(Atom)> => ExtExpr) syn_fn_defs_to_named_params([SynFnDef] fds, Var* def_vars) =
    (:named_par(_obj_(fd.name)) => syn_fn_def_to_expr(fd, def_vars) : fd <- set(fds));

  ExtExpr syn_fn_def_to_expr(SynFnDef fd, Var* def_vars)
  {
    ps = [p.var : p <- fd.params];
    expr = desugar_expr(fd.expr, def_vars & set(ps));
    expr = cls_expr(params: ps, expr: expr) if fd.params /= [];
    return expr;
  }
}
