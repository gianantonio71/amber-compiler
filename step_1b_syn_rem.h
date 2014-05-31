
Program rem_syntax(SynPrg prg)
{
  norm_prg := replace SynType t in prg with syn_type_to_raw_type(t) end;

  decls    := set(untag(norm_prg));
  
  tdefs         := {d : SynTypedef d <- decls};
  par_tdefs     := {d : SynParTypedef d <- decls};
  fndefs        := {d : SynFnDef d <- decls};
  ublocks       := {d : SynUsingBlock d <- decls};
  subtype_decls := {d : SynSubtypeDecl d <- decls};

  inst_tdefs := create_type_map(norm_prg);
  
  desugared_fndefs := union({syn_fndef_to_fndefs(fd, {}) : fd <- fndefs});
  
  desugared_block_fndefs := union(
                              for (ub <- ublocks, fd <- set(ub.fn_defs), sgns = set(ub.signatures)) {
                                syn_fndef_to_fndefs(fd, sgns)
                              }
                            );

  return program(tdefs: inst_tdefs, subtype_decls: subtype_decls, fndefs: desugared_fndefs & desugared_block_fndefs);
}


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
      params:       fndef.params, //## [(type: syn_type_to_raw_type(p.type) if p.type?, var: p.var if p.var?) : p <- fndef.params],
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
                                     then ss.res_type //##syn_type_to_raw_type(ss.res_type)
                                     else cls_type(in_types: ss.params, out_type: ss.res_type)
                                     //## else cls_type(in_types: [syn_type_to_raw_type(p) : p <- ss.params], out_type: syn_type_to_raw_type(ss.res_type))
                                   end : ss <- syn_sgns); //## BAD UGLY UGLY UGLY
}


RawType syn_type_to_raw_type(SynType type):
  LeafType          = type,
  TypeRef           = type,
  TypeVar           = type,
  ne_seq_type()     = ne_seq_type(syn_type_to_raw_type(type.elem_type)),
  ne_set_type()     = ne_set_type(syn_type_to_raw_type(type.elem_type)),
  ne_map_type()     = ne_map_type(syn_type_to_raw_type(type.key_type), syn_type_to_raw_type(type.value_type)),
  tuple_type(fs)    = tuple_type((f.label => (type: syn_type_to_raw_type(f.type), optional: f.optional) : f <- fs)),
  tag_obj_type()    = tag_obj_type(type.tag_type, syn_type_to_raw_type(type.obj_type)),
  union_type(ts)    = union_type({syn_type_to_raw_type(t) : t <- ts});
