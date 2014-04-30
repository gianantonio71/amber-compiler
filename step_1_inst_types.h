//## DOES IT MAKE SENSE TO MAKE INSTANTIATIONS CONTAINING TYPE VARIABLES?
//## ARE THEY REALLY NEEDEED? AND WOULD IT BE ANY USEFUL TO CREATE THE
//## SAME INSTANTIATIONS BUT WITH THE TYPE VARIABLES REPLACED BY ANY?

(TypeSymbol => SynType) create_type_map(SynPrg prg)
{
  tdef_map     := (td.name => td.type : SynTypedef td <- set(untag(prg)));
  par_tdef_map := inst_req_par_types(prg);
  
  return tdef_map & par_tdef_map;
}


(ParTypeSymbol => SynType) inst_req_par_types(SynPrg prg)
{
  decls     := set(untag(prg));
  
  tdefs     := {d : SynTypedef d <- decls};
  par_tdefs := {d : SynParTypedef d <- decls};
  fndefs    := {d : SynFnDef d <- decls};
  ublocks   := {d : SynUsingBlock d <- decls};
  
  symbs_to_inst     := get_type_symbols_to_instantiate(fndefs & ublocks & tdefs);
  inst_symbs_so_far := {};
  inst_par_tdefs    := ();

  while (symbs_to_inst /= {})
  
    new_insts := (s => inst_par_type(s, par_tdefs) : s <- symbs_to_inst);
    
    inst_symbs_so_far := inst_symbs_so_far & symbs_to_inst;
    inst_par_tdefs    := inst_par_tdefs & new_insts;
    
    symbs_to_inst     := get_type_symbols_to_instantiate({t : s => t <- new_insts}) - inst_symbs_so_far;
  ;

  return inst_par_tdefs;
}


ParTypeSymbol* get_type_symbols_to_instantiate(Any obj)
{
  src        := obj;
  type_symbs := {};

  loop
    new_type_symbs := select ParTypeSymbol in obj end - type_symbs;
    return type_symbs if new_type_symbs == {};
    type_symbs := type_symbs & new_type_symbs;
    src := {ts.params : ts <- new_type_symbs};
  ;
} 


SynType inst_par_type(ParTypeSymbol symb, SynParTypedef* par_tdefs)
{
  arity := length(symb.params);
  //## BUG BUG CAN THIS POSSIBLY FAIL?
  par_tdef := only_element({d : d <- par_tdefs ; d.name == symb.symbol, length(d.params) == arity});
  return replace TypeVar v in par_tdef.type with symb.params[index_first(v, par_tdef.params)] end;
}
