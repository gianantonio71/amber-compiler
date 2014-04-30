
Program rem_syntax(SynPrg prg)
{
  norm_prg := replace Type t in prg with norm_type(t) end;
  decls    := set(untag(norm_prg));
  
  tdefs     := {d : SynTypedef d <- decls};
  par_tdefs := {d : SynParTypedef d <- decls};
  fndefs    := {d : SynFnDef d <- decls};
  ublocks   := {d : SynUsingBlock d <- decls};

  inst_tdefs := create_type_map(norm_prg);
  
  desugared_fndefs := union({syn_fndef_to_fndefs(fd, {}) : fd <- fndefs});
  
  desugared_block_fndefs := union(
                              for (ub <- ublocks, fd <- set(ub.fn_defs), sgns = set(ub.signatures)) {
                                syn_fndef_to_fndefs(fd, sgns)
                              }
                            );

  return program(tdefs: inst_tdefs, fndefs: desugared_fndefs & desugared_block_fndefs);
}

//  nps    := closures & set([if arity(fd) == 0 then :named_par(untag(fd.name)) else untyped_sgn(fd) end : fd <- stmt.asgnms]); //## BAD BAD BAD



FnDef* syn_fndef_to_fndefs(SynFnDef fndef, SynSgn* named_params)
{
  //named_params := {if arity(np) == 0 then :named_par(np.name) else np end : np <- named_params}; //## BAD BAD BAD
  
  lfns := {untyped_sgn(lfd) : lfd <- set(fndef.local_fns)};

  main_fn := mk_fndef(fndef, fndef.name, fndef.name, named_params, lfns);
  
  loc_fns := for (fd <- set(fndef.local_fns)) {
               mk_fndef(fd, nested_fn_symbol(outer: fndef.name, inner: fd.name), fndef.name, named_params, lfns)
             };
  
  return {main_fn} & loc_fns;

  //## BAD BAD BAD TOO MANY PARAMETERS
  FnDef mk_fndef(SynFnDef fndef, FnSymbol fn_name, FnSymbol outer_fn, SynSgn* named_params, BasicUntypedSgn* lfns) =
    fn_def(
      name:         fn_name,
      params:       fndef.params,
      named_params: syn_sgns_to_named_params(named_params),
      res_type:     fndef.res_type if fndef.res_type?,
                    // No need to include fn_par(i) among the variables
      expr:         desugar_expr(
                      fndef.expr,
                      {p.var : p <- set(fndef.params) ; p.var?};
                      named_params  = {:named_par(untag(np.name)) : np <- named_params}, //## BAD BAD BAD
                      local_fns     = lfns,
                      curr_outer_fn = outer_fn
                    )
    );
  
  (<named_par(Atom)> => ExtType) syn_sgns_to_named_params(SynSgn* syn_sgns) =
    //## THIS FAILS IF THERE ARE TWO IMPLICIT PARAMS WITH THE SAME NAME BUT DIFFERENT ARITIES.
    //## MAKE SURE THIS IS CHECKED IN THE WELL-FORMEDNESS CHECKING PHASE
    (:named_par(untag(ss.name)) => if ss.params == []
                                     then ss.res_type
                                     else cls_type(in_types: ss.params, out_type: ss.res_type)
                                   end : ss <- syn_sgns); //## BAD UGLY UGLY UGLY
}

//type SynSgn         = syn_sgn(
//                        name:     FnSymbol,
//                        params:   [Type*],
//                        res_type: Type
//                      );

//type ClsType  = cls_type(in_types: [Type+], out_type: Type);

//type FnDef      = fn_def(
//                    name:         FnSymbol,
//                    params:       [(var: var(Atom)?, type: ExtType?)*], //## BAD BAD
//                    named_params: (<var(Atom)> => ExtType),             //## NEW BAD BAD
//                    res_type:     Type?,
//                    expr:         Expr
//                    //impl_env: Signature*, //## NEW
//                  );

// fn_call(name: FnSymbol, params: [ExtSynExpr*], named_params: [SynFnDef*]), //## NEW
// fn_call(name: FnSymbol, params: [ExtExpr*], named_params: (<var(Atom)> => ExtExpr)), //## NEW BAD BAD


//type SynFnDef       = syn_fn_def(
//                        name:       FnSymbol,
//                        params:     [(type: SynType?, var: var(Atom)?)*],
//                        res_type:   SynType?,
//                        expr:       SynExpr,
//                        local_fns:  [SynFnDef*]
//                      );

//type ClsExpr  = cls_expr(params: [<var(Atom)>+], expr: Expr);


