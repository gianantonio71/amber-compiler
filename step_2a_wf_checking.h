type True = true;


True prg_is_wf(Program prg)
{
  //## NOT SURE THAT CHECKING THE TYPE DEFINITIONS HERE MAKES ANY SENSE.
  //## AT THIS POINT WE'VE ALREADY CREATED THE "PURE" TYPE MAP, AND THAT
  //## WOULD HAVE PROBABLY FAILED ALREADY IF THE CONDITIONS CHECKED HERE
  //## DIDN'T HOLD.

  //## COULD THE FOLLOWING BE PART OF A MORE GENERAL AND ELEGANT CONSTRAINT?
  // No top-level reference cycles
  tl_ref_map      = (s => top_level_refs(t) : s => t <- prg.tdefs);
  tl_ref_deep_map = transitive_closure(tl_ref_map);
  return false if (? s => es <- tl_ref_deep_map : in(s, es));

  // Every Type must be well formed
  return false if (? s => t <- prg.tdefs : not user_type_is_wf(t, select TypeVar in s end; typedefs=prg.anon_tdefs, user_typedefs=prg.tdefs));

  // Now checking that all functions are OK
  return fndefs_are_wf(prg.fndefs; typedefs=prg.anon_tdefs, user_typedefs=prg.tdefs);

  // Local functions
  TypeSymbol* top_level_refs(UserType type):
    type_ref(s?)    = {s},
    union_type(ts?) = union({top_level_refs(t) : t <- ts}),
    _               = {};
}


using (TypeName => AnonType) typedefs, (TypeSymbol => UserType) user_typedefs
{
  True fndefs_are_wf(FnDef* fndefs)
  {
    sgns = {(name: fd.name, arity: arity(fd)) : fd <- fndefs};
    grouped_fns = {{fd : fd <- fndefs, fd.name == s.name and arity(fd) == s.arity} : s <- sgns};  //## BAD BAD BAD INEFFICIENT
    return false if (? g <- grouped_fns : not are_compatible(g));
    return not (? fd <- fndefs : not fndef_is_wf(fd, fndefs));
  }
  
  True are_compatible(FnDef* fndefs)
  {
    //## BAD BAD BAD INEFFICIENT
    return not (? fd1 <- fndefs, fd2 <- fndefs : fd1 /= fd2, not are_comp(fd1, fd2));
    
    True are_comp(FnDef fd1, FnDef fd2)
    {
      assert arity(fd1) == arity(fd2);
      
      for (p1 @ i : fd1.params)
        p2 = fd2.params[i];
        return true if p1.type? and p2.type? and are_compatible(p1.type, p2.type, typedefs);
      ;
      
      return fd1.named_params == fd2.named_params;
    }
  }

  True fndef_is_wf(FnDef fndef, FnDef* fndefs)
  {
    //## BAD BAD BAD THIS IS CHEATING...
    tvars = select TypeVar in fndef.params end & select TypeVar in fndef.named_params end;
    for (p : fndef.params)
      return false if p.type? and not user_type_is_wf(p.type, tvars);
    ;
    
    return false if fndef.res_type? and not user_type_is_wf(fndef.res_type, tvars);
    
    return false if has_duplicates([p.var : p <- fndef.params, p.var?] & rand_sort({v : v => _ <- fndef.named_params}));

    return expr_is_wf(
             fndef.expr,
             scalar_vars(fndef);
             type_vars    = tvars,
             fns_in_scope	= fndefs,
             cls_vars = cls_vars(fndef)
           );
  }
  
  //True sgn_is_wf(Signature sgn)
  //{
  //  tvars = select TypeVar in sgn.params end; //## BAD BAD BAD CHEATING
  //  return false if not all([type_is_wf(t, typedefs, tvars) : t <- sgn.params]);
  //  return type_is_wf(sgn.res_type, typedefs, tvars);
  //}
}
