
Program rem_syntax(SynPrg prg)
{
  norm_prg = replace SynExtType t in prg with syn_type_to_user_type(t) end;

  decls    = set(_obj_(norm_prg));
  
  tdefs         = {d : typedef()       d <- decls};
  par_tdefs     = {d : par_typedef()   d <- decls};
  fndefs        = {d : syn_fn_def()    d <- decls};
  proc_defs     = {d : proc_def()      d <- decls};
  ublocks       = {d : using_block()   d <- decls};
  subtype_decls = {d : subtype_decl()  d <- decls};

  assert tdefs & par_tdefs & fndefs & proc_defs & ublocks & subtype_decls == decls;

  inst_tdefs = create_type_map(norm_prg);

  anon_tdefs = normalize_and_anonymize_types(inst_tdefs);

  fn_param_arities = get_fn_param_arities(fndefs, ublocks);

  desugared_fndefs = union({syn_fndef_to_fndefs(fd, {}, anon_tdefs, fn_param_arities) : fd <- fndefs});
  
  desugared_proc_defs = {syn_proc_def_to_proc_def(pd, anon_tdefs, fn_param_arities) : pd <- proc_defs};

  desugared_block_fndefs = union(
                              for (ub <- ublocks, fd <- set(ub.fn_defs), sgns = set(ub.signatures)) {
                                syn_fndef_to_fndefs(fd, sgns, anon_tdefs, fn_param_arities)
                              }
                            );

  return program(
    tdefs:          inst_tdefs,
    anon_tdefs:     anon_tdefs,
    subtype_decls:  subtype_decls,
    fndefs:         desugared_fndefs & desugared_block_fndefs,
    proc_defs:      desugared_proc_defs
  );
}

((FnSymbol, Nat) => [Nat]) get_fn_param_arities(SynFnDef* fndefs, SynUsingBlock* ublocks)
{
  all_fds = fndefs & union({set(ub.fn_defs) : ub <- ublocks});
  arities = merge_values({get_fn_param_arities(fd) : fd <- all_fds});
  return (sgn => only_element(pas) : sgn => pas <- arities);

  ((FnSymbol, Nat) => [Nat]) get_fn_param_arities(SynFnDef fd) =
    ((fd.name, arity(fd)) => [arity(p) : p <- fd.params]);
}

FnDef* syn_fndef_to_fndefs(SynFnDef fndef, SynSgn* named_params,
  (TypeName => AnonType) typedefs, ((FnSymbol, Nat) => [Nat]) fn_param_arities)
{
  //named_params = {if arity(np) == 0 then :named_par(np.name) else np end : np <- named_params}; //## BAD BAD BAD
  
  lfns = {untyped_sgn(lfd) : lfd <- set(fndef.local_fns)};

  main_fn = mk_fndef(fndef, fndef.name, fndef.name, named_params, lfns, typedefs, fn_param_arities);
  
  loc_fns = for (fd <- set(fndef.local_fns)) {
     mk_fndef(
      fd,
      nested_fn_symbol(outer: fndef.name, inner: fd.name),
      fndef.name,
      named_params,
      lfns,
      typedefs,
      fn_param_arities
    )
  };
  
  return {main_fn} & loc_fns;

  //## BAD BAD BAD TOO MANY PARAMETERS
  FnDef mk_fndef(SynFnDef fndef, FnSymbol fn_name, FnSymbol outer_fn, SynSgn* named_params,
    BasicUntypedSgn* lfns, (TypeName => AnonType) typedefs, ((FnSymbol, Nat) => [Nat]) fn_param_arities) =
      fn_def(
        name:         fn_name,
        params:       [desugar_fn_par(p) : p <- fndef.params], //## [(type: syn_type_to_user_type(p.type) if p.type?, var: p.var if p.var?) : p <- fndef.params],
        named_params: syn_sgns_to_named_params(named_params),
        res_type:     fndef.res_type if fndef.res_type?,
                      // No need to include fn_par(i) among the variables
        expr:         desugar_expr(
                        fndef.expr,
                        {p.var : p <- set(fndef.params), p.var? and (not p.type? or p.type :: SynType)},
                        clss_in_scope     = {untyped_sgn(p.var, p.type) : p <- set(fndef.params), p.var? and p.type? and p.type :: SynClsType},
                        named_params      = {:named_par(_obj_(np.name)) : np <- named_params}, //## BAD BAD BAD
                        local_fns         = lfns,
                        curr_outer_fn     = outer_fn,
                        typedefs          = typedefs,
                        fn_param_arities  = fn_param_arities
                      )
      );

  FnFrmPar desugar_fn_par(SynFnArg arg)
  {
    if (arg.type? and arg.type :: UserClsType)
      assert arg.var?;
      var = cls_var(_obj_(arg.var));
      return non_scalar_par(var, arg.type);
    ;
    return scalar_par(var: arg.var if arg.var?, type: arg.type if arg.type?);
  }
  
  (<named_par(Atom)> => UserExtType) syn_sgns_to_named_params(SynSgn* syn_sgns) =
    //## THIS FAILS IF THERE ARE TWO IMPLICIT PARAMS WITH THE SAME NAME BUT DIFFERENT ARITIES.
    //## MAKE SURE THIS IS CHECKED IN THE WELL-FORMEDNESS CHECKING PHASE
    (:named_par(_obj_(ss.name)) => if ss.params == []
                                     then ss.res_type //##syn_type_to_user_type(ss.res_type)
                                     else user_cls_type(ss.params, ss.res_type)
                                     //## else user_cls_type(in_types: [syn_type_to_user_type(p) : p <- ss.params], out_type: syn_type_to_user_type(ss.res_type))
                                   end : ss <- syn_sgns); //## BAD UGLY UGLY UGLY
}


ProcDef2 syn_proc_def_to_proc_def(SynProcDef pd, (TypeName => AnonType) typedefs, ((FnSymbol, Nat) => [Nat]) fn_param_arities)
{
  body = desugar_stmts(
    pd.body,
    set([p.var : p <- pd.params]),
    clss_in_scope = {},
    named_params = {},
    local_fns = {},
    curr_outer_fn = nil, //## BAD BAD BAD CHEATING. FIX FIX FIX FIX FIX FIX FIX FIX FIX FIX FIX
    typedefs = typedefs,
    fn_param_arities = fn_param_arities
  );

  return proc_def(
    name:       pd.name,
    params:     pd.params,
    res_type:   pd.res_type,
    body:       body
  );
}