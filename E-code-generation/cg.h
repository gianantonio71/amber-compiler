
ProcDef* gen_prg_code(Program prg)
{
  simpl_prg  = generate_dispatch_functions(prg);
  
  memb_tests = {mk_named_type_memb_test_fn(tn, prg.tdefs) : tn <- keys(simpl_prg.tdefs)}; // where type_map = simpl_prg.tdefs;;
                
  // fndefs     = {gen_fn_code(fd; type_map = simpl_prg.tdefs) : fd <- simpl_prg.fndefs};
  fndefs     = {gen_fn_code(fd) : fd <- simpl_prg.fndefs};

  proc_defs  = {gen_proc_code(pd) : pd <- simpl_prg.proc_defs};

  return memb_tests & fndefs & proc_defs;
  //return {normalize_var_numbers(pd) : pd <- memb_tests & fndefs};
}


//ProcDef normalize_var_numbers(ProcDef pd)
//{
//  body = pd.body;
//  
//  // This should go first, just to be on the safeside
//  int_vars = rand_sort(select IntVar in body end);
//  body = replace IntVar v in body with ivar(first_index(v, int_vars)) end;
//
//  obj_vars = rand_sort(select <lvar(Nat)> in body end);
//  body = replace <lvar(Nat)> v in body with lvar(first_index(v, obj_vars)) end;
//
//  vec_var_ids = rand_sort(retrieve v.id from VecVar v in body end);
//  body = replace VecVar v in body with vvar(id: first_index(v.id, vec_var_ids), size: v.size) end;
//  body = replace <evar(id: Nat, idx: Nat)> v in body with evar(id: first_index(v.id, vec_var_ids), idx: v.idx) end;
//
//  bool_vars = rand_sort(select <bvar(Nat)> in body end);
//  body = replace <bvar(Nat)> v in body with bvar(first_index(v, bool_vars)) end;
//  
//  set_it_vars = rand_sort(select SetItVar in body end);
//  body = replace SetItVar v in body with set_it_var(first_index(v, set_it_vars)) end;
//  
//  seq_it_vars = rand_sort(select SeqItVar in body end);
//  body = replace SeqItVar v in body with seq_it_var(first_index(v, seq_it_vars)) end;
//  
//  strm_vars = rand_sort(select StreamVar in body end);
//  body = replace StreamVar v in body with svar(first_index(v, strm_vars)) end;
//  
//  return update_body(pd, body);
//  
//  //## BAD BAD BAD
//  ProcDef update_body(ProcDef pd, [Instr^] body):
//    ObjProcDef    = obj_proc_def(pd.name, pd.in_arity, body),
//    BoolProcDef   = bool_proc_def(pd.name, pd.arity, body);
//}


ObjProcDef gen_proc_code(ProcDef2 proc_def)
{
  fn_res_var = lvar(0);
  tmp_bvar   = bvar(0);

  body = [];

  let ( next_set_it_var_id = 0,
        next_seq_it_var_id = 0,
        next_map_it_var_id = 0,
        next_obj_var_id    = 1,
        next_int_var_id    = 0,
        next_bool_var_id   = 1,
        next_vector_var_id = 0,
        next_stream_var_id = 0)

    //// Checking parameter types
    //for (p @ i : fndef.params)
    //  body = body & gen_type_checking_code(p.type, fn_par(i), tmp_bvar) & [check(tmp_bvar)] if p.type?;
    //;

    // Setting named variables for parameters
    body = body & [set_var(p.var, fn_par(i)) : p @ i <- proc_def.params];

    // Evaluating the expression
    body = body & [execute_block(gen_code(proc_def.body, fn_res_var))];

    //// Checking the type of the result
    //if (fndef.res_type?)
    //  body = body & gen_type_checking_code(fndef.res_type, fn_res_var, tmp_bvar) & [check(tmp_bvar)];
    //;
  ;

  debug_code = [push_call_info(proc_def.name, [just(fn_par(i)) : p @ i <- proc_def.params])];
  ret_val = if proc_def.res_type /= nil then fn_res_var else object(nil) end; //## BAD: HERE I'M CHEATING...
  body = debug_code & body & [pop_call_info, ret_val(ret_val)];

  return obj_proc_def(proc_def.name, arity(proc_def) * [:obj], (), body);
}


ObjProcDef gen_fn_code(FnDef fndef)
{
  fn_res_var = lvar(0);
  tmp_bvar   = bvar(0);

  body = [];

  let ( next_set_it_var_id = 0,
        next_seq_it_var_id = 0,
        next_map_it_var_id = 0,
        next_obj_var_id    = 1,
        next_int_var_id    = 0,
        next_bool_var_id   = 1,
        next_vector_var_id = 0,
        next_stream_var_id = 0)

    //// Checking parameter types
    //for (p @ i : fndef.params)
    //  body = body & gen_type_checking_code(p.type, fn_par(i), tmp_bvar) & [check(tmp_bvar)] if p.type?;
    //;

    // Setting named variables for parameters
    body = body & [set_var(p.var, fn_par(i)) : p @ i <- fndef.params, var_has_to_be_set(p)];

    // Evaluating the expression
    body = body & gen_eval_code(fndef.expr, fn_res_var);

    //// Checking the type of the result
    //if (fndef.res_type?)
    //  body = body & gen_type_checking_code(fndef.res_type, fn_res_var, tmp_bvar) & [check(tmp_bvar)];
    //;
  ;

  body = [push_call_info(fndef.name, [maybe(fn_par(i), is_scalar_par(p)) : p @ i <- fndef.params])] & body & [pop_call_info, ret_val(fn_res_var)];

  ObjProcPar low_level_param(FnFrmPar p):
    scalar_par()      = :obj,
    non_scalar_par()  = if p.var? then cls(p.var, p.arity) else cls(p.arity) end;

  params = [low_level_param(p) : p <- fndef.params];

  return obj_proc_def(fndef.name, params, (v => arity(t) : v => t <- fndef.named_params), body);

  //## UGLY: ISNT THERE ANY BETTER WAY? HAVING TO WRITE A FUNCTIONS FOR SOMETHING SO SIMPLE FEELS OVERKILL
  Bool var_has_to_be_set(FnFrmPar p):
    scalar_par()      = p.var?,
    non_scalar_par()  = false;
}


Program generate_dispatch_functions(Program prg)
{
  mult_map = bag([[fd.name, arity(fd)] : fd <- rand_sort(prg.fndefs)]); //## BAD: USING A SEQUENCE INSTEAD OF A BAG AND AGAIN A SEQUENCE INSTEAD OF A TUPLE

  overloaded_fns = for (na => m <- mult_map)
                     if (m > 1) {{
                       fd : fd <- prg.fndefs, [fd.name, arity(fd)] == na
                     }};
  
  dispatched_fns = union({generate_dispatch_function(fns, prg.anon_tdefs) : fns <- overloaded_fns});
  
  new_fns = dispatched_fns & (prg.fndefs - union(overloaded_fns));
  
  return program(
    tdefs:          prg.tdefs,
    anon_tdefs:     prg.anon_tdefs,
    proc_defs:      prg.proc_defs,
    subtype_decls:  prg.subtype_decls,
    fndefs:         new_fns
  );
}

FnDef+ generate_dispatch_function(FnDef+ fds, (TypeName => AnonType) typedefs)
{
  assert size(fds) > 1;
  assert size({length(fd.params) : fd <- fds}) == 1; // All functions have the same arity

  //## I DON'T PARTICULARLY LIKE THIS...
  rand_fd      = an_elem(fds);
  name         = rand_fd.name;
  scalar_pars  = [i : p @ i <- rand_fd.params, is_scalar_par(p)];
  arity        = arity(rand_fd);
  named_params = rand_fd.named_params;

  //## BAD: THIS IS REALLY UGLY. NEED A NON-DESTRUCTIVE OPERATION TO UPDATE THE FIELDS OF A TUPLE
  FnDef make_unique(FnDef fd, Nat i) =
    fn_def(
      name:         unique_fn_symbol(fd.name, i),
      params:       fd.params,
      named_params: fd.named_params,
      res_type:     fd.res_type if fd.res_type?,
      expr:         fd.expr
      // expr:         Expr
    );

  unique_fds = [make_unique(fd, i) : fd @ i <- rand_sort(fds)];

  candidates = [];
  for (i : scalar_pars)
    params = [fd.params[i] : fd <- rand_sort(fds)];
    ptypes = [if p.type? then pseudotype(p.type, typedefs) else pseudotype_any end : p <- params];
    good = all([all([are_disjoint(p1, p2) : p2 <- right_subseq(ptypes, j+1)]) : p1 @ j <- ptypes]); //## BAD: INEFFICIENT. ALSO A BIT UGLY...
    candidates = candidates & [i] if good;
  ;

  // If no single parameter is enough to discriminate between all the functions,
  // then we just check all of them, except for closures. Otherwise we use the
  // first parameter that can do the job.
  //## EVEN IF NO SINGLE PARAMETER IS ENOUGHT TO DISCRIMINATE BETWEEN ALL THE FUNCTIONS,
  //## CHANCES ARE THAT WE STILL DON'T NEED TO CHECK ALL OF THEM. ALSO, IF THERE IS MORE
  //## THAN ONE CANDIDATE PARAMETER, WE SHOULD CHOOSE THE BEST ONE, THAT IS, THE ONE THAT
  //## CAN DO THE JOB MORE EFFICIENTLY.
  //## ALSO, THE PARAMETERS THAT ARE NOT CHECKED AND THAT DO NOT DEFINE ANY VARIABLES
  //## SHOULD NOT BE INCLUDED IN THE MATCH AT ALL (ALTHOUGH THIS WOULD MAKE A DIFFERENCE
  //## ONLY WHEN AT LEAST ONE PARAMETER IS NOT NAMED IN ANY OF THE FUNCTIONS)
  is_checked = if candidates == [] then bit_map(scalar_pars, arity) else [i == candidates[0] : i < arity] end;

  dispatch_call_params = [if is_scalar_par(p) then fn_par(i) else cls_var(i) end : p @ i <- rand_fd.params];

  Pattern mk_ptrn(<(var: var(Atom)?, type: UserExtType?)> param, (TypeName => AnonType) typedefs, Bool is_checked) =
    if param.type? and is_checked
      then user_type_to_pseudotype_pattern(param.type, typedefs)
      else ptrn_any
    end;

  cases = [];
  for (fd : unique_fds)
    ptrns = [mk_ptrn(p, typedefs, is_checked[i]) : p @ i <- fd.params];
    case  = (ptrns: ptrns, expr: fn_call(fd.name, dispatch_call_params));
    cases = [case] & cases;
  ;

  new_expr = match_expr(
    exprs: [fn_par(i) : i < arity],
    cases: cases
  );

  params = [if is_scalar_par(p) then :scalar_par(()) else non_scalar_par(p.arity) end : p @ i <- rand_fd.params];

  dispatch_fn = fn_def(
    name:          name,
    params:        params,
    named_params:  named_params,
    //res_type: ????
    expr:          new_expr
  );

  return set(unique_fds) & {dispatch_fn};
}
