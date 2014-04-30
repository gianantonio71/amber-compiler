
type UserErr      = dup_tdef(BasicTypeSymbol),
                    dup_par_tdef(name: BasicTypeSymbol, arity: NzNat),
                    incomp_fndefs(name: FnSymbol, arity: Nat, params: [ObjPartSet*]+),
                    tdef_err(type: TypeSymbol, errs: TDefUserErr*),
                    fndef_err(name: FnSymbol, params: [<SynType, nil>*], errs: SynObjErr*),
                    ublock_err(errs: UBlockErr*);

type TDefUserErr  = undef_type_name(BasicTypeSymbol),
                    undef_par_type_name(name: BasicTypeSymbol, arity: NzNat),
                    undef_type_var(TypeVar),
                    //incompatible_types_in_set_type(SynType++),
                    incompatible_types_in_union_type(SynType++);

//:rep_labels_in_map(SymbObj*)

type UBlockErr    = TDefUserErr,
                    dupl_type_pars(Var+);

type SynObjErr    = TDefUserErr,
                    undef_var(Var),
                    undef_var_or_const(Atom),
                    almost_def_const(Atom),
                    undef_fn(name: FnSymbol, arity: NzNat),
                    almost_def_fn(name: FnSymbol, arity: NzNat),
                    no_ret_stmt,
                    no_way_out_loop,
                    break_outside_loop,
                    var_redef(Var),
                    asgnm_readonly_var(Var),
                    
                    dup_closure_def(BasicUntypedSgn),

                    free_var_in_try_expr(Var), //## THIS COULD BE MORE LIKE A WARNING...
                    
                    undef_bound_ptrn_var(Var),
                    already_def_ptrn_var(Var),
                    loc_bound_var_with_ptrn(Var),
                    //incomp_ptrn_branches(SynPtrnBranch+),
                    mult_vars_in_mult_ptrn_branch,
                    nested_mult_ptrn_branch,
                    vars_repeated_in_diff_branches(Var*),
                    
                    unreachable_code,
                    
                    diff_vars_in_or_clause(Var+),  //## IS THIS STILL USED?
                    
                    //## NOT CHECKED YET
                    nested_local_fn(outer_fn: BasicUntypedSgn, inner_fn: BasicUntypedSgn);


//## NOT SURE IF IT IS CHECKED OR NOT:
//##   FUNCTION AND CLOSURE PARAMETERS MUSTN'T BE DUPLICATED

//## ERRORS LEFT TO CHECK:
//##   FUNCTIONS WITH INCOMPATIBLE SIGNATURES
//##   NO RECURSION FOR FUNCTIONS WITH NO RETURN TYPE (IS THIS THE RIGHT PLACE TO CHECK?)
//##   NO ASSIGNMENT TO FOR LOOP VARIABLES
//##   IN FUNCTIONS INSIDE USING BLOCKS THE IMPLICIT PARAMETER CHECKING IS BROKEN.
//##     SEE CHECKS FOR THE CORE REPRESENTATION
//##   SEE THE FUNCTION THAT CHECKS SYN_CASES

//## IN A MATCH EXPRESSION, THE NUMBER OF PATTERNS IN ANY OF THE CASES
//## MUST BE THE SAME AS THE NUMBER OF EXPRESSIONS

//## CAN A CLOSURE REFER TO ITSELF? THERE'S THE RISK THAT IT MIGHT INTENDED TO REFER
//## TO THE CLOSURE WITH THE SAME NAME/ARITY PREVIOSLY IN SCOPE...

//## BUG IN well-formedness checking: it doesn't check that two functions
//## with the same name/arity have the same "hidden" parameters

//## NOT SURE IF THEY ARE CHECKED OR NOT:
//##   THE ONLY PLACE WHERE A TYPE IN A FUNCTION CAN CONTAIN A TYPE VAR IS IN ITS SIGNATURE, NOT THE BODY


//## BUG BUG BUG: IF A TYPE REFERENCE IS "DANGLING", THE PROGRAM CRASHES

UserErr* wf_errors(SynPrg prg)
{
  decls       := set(untag(prg));
  
  tdefs       := {d : SynTypedef d <- decls};
  par_tdefs   := {d : SynParTypedef d <- decls};
  fndefs      := {d : SynFnDef d <- decls};
  ublocks     := {d : SynUsingBlock d <- decls};
  
  all_def_fns := {untyped_sgn(fd) : fd <- fndefs} &
                 for (ub <- ublocks, fd <- set(ub.fn_defs)) {
                   untyped_sgn(fd, set(ub.signatures))
                 };

  inst_tdefs  := create_type_map(prg);
  
  dup_tdef_errs := for (td1 <- tdefs, td2 <- tdefs)
                     if (td1 /= td2 and td1.name == td2.name)
                       {:dupl_tdef(td1.name)};

  dup_par_tdef_errs := for (td1 <- tdefs, td2 <- tdefs)
                         if (td1 /= td2 and td1.name == td2.name and length(td1.params) == length(td2.params)) {
                           :dupl_par_tdef(name: td1.name, arity: length(td1.params))
                         };

  all_fndefs  := fndefs & union({set(ub.fn_defs) : ub <- ublocks});
  
  //## BAD BAD BAD THIS IS VERY INEFFICIENT...
  fn_groups   := for (n <- {untyped_sgn(fd) : fd <- all_fndefs})
                  (n => {fd : fd <- all_fndefs ; untyped_sgn(fd) == n});

  //## BAD BAD BAD, INEFFICIENT
  incomp_fn_sgns := for (s => fns <- fn_groups, fd1 <- fns, fd2 <- fns)
                      if (fd1 /= fd2, not syn_fns_are_compatible(fd1, fd2; typedefs = inst_tdefs)) {
                        :incomp_fndefs(
                          name:   s.name,
                          arity:  s.arity,
                          params: {par_parts(fd; typedefs = inst_tdefs) : fd <- {fd1, fd2}}
                        )
                      }
                    ;

  //## DOES THIS HAVE TO BE DONE BEFORE CREATING THE TYPE MAP, THAT IS, CAN
  //## THE CREATION OF THE TYPE MAP FAIL IN THE PRESENCE OF ONE OF THESE ERRORS?
  undef_type_symb_errs := undef_type_symbol_errs(fndefs, ublocks; typedefs = inst_tdefs);

  //## ALSO CHECK FOR TOP-LEVEL CYCLES IN THE OBJECT GRAPH

  errs_so_far := dup_tdef_errs & dup_par_tdef_errs & incomp_fn_sgns & undef_type_symb_errs;
  return errs_so_far if errs_so_far /= {};

  let (fns_in_scope         = all_def_fns,
       typedefs             = inst_tdefs,
       all_par_type_symbols = {[p.name, length(p.params)] : p <- par_tdefs})

    decl_errs := tdef_errs(tdefs)                     &
                 par_tdef_errs(par_tdefs)             &
                 inst_tdef_errs(inst_tdefs)           &
                 fn_def_errs(fndefs, all_def_fns, {}) &
                 ublock_errors(ublocks, all_def_fns);
  ;

  return decl_errs;
}


using (TypeSymbol => SynType) typedefs
{
  //## THIS IS ALL WRONG. IT SHOULD BE DONE BEFORE CREATING THE TYPE MAP
  UserErr* undef_type_symbol_errs(SynFnDef* fndefs, SynUsingBlock* ublocks)
  {
    used_type_symbs := all_type_symbols([fndefs, ublocks, values(typedefs)]);
    def_type_symbs  := keys(typedefs);
    
    missing_type_symbs := used_type_symbs - def_type_symbs;
    
    //## USING THE WRONG ERROR TYPE HERE.
    //## TO FIX THIS PROBLEM I SHOULD DO THE ERROR CHECKING SOMEWHERE ELSE
    return {tdef_err(type: ts, errs: {make_err_obj(ts)}) : ts <- missing_type_symbs};
    
    TDefUserErr make_err_obj(TypeSymbol ts):
      BasicTypeSymbol   = :undef_type_name(ts),
      ParTypeSymbol     = undef_par_type_name(name: ts.name, arity: length(ts.params));
    
    TypeSymbol* all_type_symbols(Any obj)
    {
      type_symbs := select TypeSymbol in obj end;
      
      loop
        new_type_symbs := union({all_type_symbols(ts.params) : ParTypeSymbol ts <- type_symbs});
        new_type_symbs := new_type_symbs - type_symbs;
        return type_symbs if new_type_symbs == {};
        type_symbs := type_symbs & new_type_symbs;
      ;    
    }
  }

  Bool syn_fns_are_compatible(SynFnDef fd1, SynFnDef fd2)
  {
    assert fd1.name == fd2.name;
    assert arity(fd1) == arity(fd2);
    
    for (p1, i : fd1.params)
      p2 := fd2.params[i];
      return true if p1.type? and p2.type? and are_part_compatible(p1.type, p2.type);
    ;
    
    return false;

    // Types are supposed to have already passed the "no direct ref cycles" test
    //## IMPLEMENT THE ABOVE TEST

    Bool are_part_compatible(SynType t1, SynType t2) = are_disjoint(partitions(t1), partitions(t2));

    //Bool are_part_compatible(SynType t1, SynType t2):
      //IntType,  IntType   = separated(t1, t2),
      //_,        _         = are_disjoint(partitions(t1), partitions(t2));
  }

  [ObjPartSet*] par_parts(SynFnDef fd) = [if p.type? then partitions(p.type) else :all_objs end : p <- fd.params];
}



using (TypeSymbol => SynType) typedefs, [BasicTypeSymbol, NzNat]* all_par_type_symbols
{
  UserErr* tdef_errs(SynTypedef* tdefs) =
    for (td <- tdefs, es = type_wf_errors(td.type; type_vars_in_scope = {}))
      if (es /= {}) {
        :tdef_err(
          type: td.name,
          errs: es
        )
      };

  //## NOT SURE THIS IS THE RIGHT WAY TO CHECK FOR UNDEFINED TYPE VARIABLES
  UserErr* par_tdef_errs(SynParTypedef* par_tdefs) =
    for (td <- par_tdefs, es = type_wf_errors(td.type; type_vars_in_scope = set(td.params)))
      if (es /= {}) {
        :tdef_err(
          type: td.name,
          errs: es
        )
      };

  UserErr* inst_tdef_errs((TypeSymbol => SynType) inst_tdefs) =
    for (s => t <- inst_tdefs, es = type_wf_errors(t; type_vars_in_scope = select TypeVar in s end))
      if (es /= {}) {
        :tdef_err(
          type: s,
          errs: es
        )
      };

  UserErr* fn_def_errs(SynFnDef* fndefs, UntypedSgn* global_fns, BasicUntypedSgn* impl_pars) =
    for (fd <- fndefs, es = fndef_wf_errors(fd, global_fns, impl_pars))
    if (es /= {}) {
      :fndef_err(
        name: fd.name,
        params:  [if p.type? then p.type else :nil end : p <- fd.params],
        errs:    es
      )
    };


  UserErr* ublock_errors(SynUsingBlock* ublocks, UntypedSgn* global_fns) =
    union({block_wf_errors(b, global_fns) : b <- ublocks});

  UserErr* block_wf_errors(SynUsingBlock ublock, UntypedSgn* global_fns)
  {
    //## UGLY UGLY
    block_errs := seq_union([sgn_wf_errors(s) : s <- ublock.signatures]);
    err        := if block_errs == {} then {} else {:ublock_err(errs: block_errs)} end;
    req_fns    := {untyped_sgn(s) : s <- set(ublock.signatures)};
    all_fns    := merge_and_override(global_fns, {untyped_sgn(s) : s <- set(ublock.signatures)});
    return err & fn_def_errs(set(ublock.fn_defs), all_fns, req_fns);
  }

  TDefUserErr* sgn_wf_errors(SynSgn sgn)
  {
    type_vars := select TypeVar in sgn end; //## BAD BAD BAD THIS IS ALL WRONG.
    in_errs   := seq_union([type_wf_errors(t; type_vars_in_scope = type_vars) : t <- sgn.params]);
    out_errs  := type_wf_errors(sgn.res_type; type_vars_in_scope = type_vars);
    return in_errs & out_errs;
  }
}
