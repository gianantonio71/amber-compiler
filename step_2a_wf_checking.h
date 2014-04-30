type Tautology = true;


Tautology prg_is_wf(Program prg) = types_are_wf(prg.tdefs) and fndefs_are_wf(prg.fndefs; typedefs = prg.tdefs);



using (TypeSymbol => Type) typedefs
{
  Tautology fndefs_are_wf(FnDef* fndefs)
  {
    sgns := {(name: fd.name, arity: arity(fd)) : fd <- fndefs};
    grouped_fns := {{fd : fd <- fndefs ; fd.name == s.name and arity(fd) == s.arity} : s <- sgns};  //## BAD BAD BAD INEFFICIENT
    return false if (? g <- grouped_fns : not are_compatible(g));
    return not (? fd <- fndefs : not fndef_is_wf(fd, fndefs));
  }
  
  Tautology are_compatible(FnDef* fndefs)
  {
    //## BAD BAD BAD INEFFICIENT
    return not (? fd1 <- fndefs, fd2 <- fndefs : fd1 /= fd2, not are_comp(fd1, fd2));
    
    Tautology are_comp(FnDef fd1, FnDef fd2)
    {
      assert arity(fd1) == arity(fd2);
      
      for (p1, i : fd1.params)
        p2 := fd2.params[i];
        return true if p1.type? and p2.type? and are_compatible(p1.type, p2.type);
      ;
      
      return fd1.named_params == fd2.named_params;
    }
  }

  Tautology fndef_is_wf(FnDef fndef, FnDef* fndefs)
  {
    //## BAD BAD BAD THIS IS CHEATING...
    tvars := select TypeVar in fndef.params end & select TypeVar in fndef.named_params end;
    for (p : fndef.params)
      return false if p.type? and not type_is_wf(p.type, tvars);
    ;
    
    return false if fndef.res_type? and not type_is_wf(fndef.res_type, tvars);
    
    return false if has_duplicates([p.var : p <- fndef.params, p.var?] & rand_sort({v : v => _ <- fndef.named_params}));

    return expr_is_wf(
             fndef.expr,
             scalar_vars(fndef);
             type_vars    = tvars,
             fns_in_scope	= fndefs,
             cls_vars = cls_vars(fndef)
           );
  }
  
  //Tautology sgn_is_wf(Signature sgn)
  //{
  //  tvars := select TypeVar in sgn.params end; //## BAD BAD BAD CHEATING
  //  return false if not all([type_is_wf(t, typedefs, tvars) : t <- sgn.params]);
  //  return type_is_wf(sgn.res_type, typedefs, tvars);
  //}
}
