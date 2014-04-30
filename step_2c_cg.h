
Any gen_prg_code(Program prg)
{
  simpl_prg  := merge_fns_same_name_and_arity(prg);
  
  memb_tests := {mk_named_type_memb_test_fn(tn, prg.tdefs) : tn <- keys(simpl_prg.tdefs)}; // where type_map = simpl_prg.tdefs;;
                
  fndefs     := {gen_fn_code(fd; type_map = simpl_prg.tdefs) : fd <- simpl_prg.fndefs};

  return memb_tests & fndefs;
  //return {normalize_var_numbers(pd) : pd <- memb_tests & fndefs};
}


//ProcDef normalize_var_numbers(ProcDef pd)
//{
//  body := pd.body;
//  
//  // This should go first, just to be on the safeside
//  int_vars := rand_sort(select IntVar in body end);
//  body := replace IntVar v in body with ivar(first_index(v, int_vars)) end;
//
//  obj_vars := rand_sort(select <lvar(Nat)> in body end);
//  body := replace <lvar(Nat)> v in body with lvar(first_index(v, obj_vars)) end;
//
//  vec_var_ids := rand_sort(retrieve v.id from VecVar v in body end);
//  body := replace VecVar v in body with vvar(id: first_index(v.id, vec_var_ids), size: v.size) end;
//  body := replace <evar(id: Nat, idx: Nat)> v in body with evar(id: first_index(v.id, vec_var_ids), idx: v.idx) end;
//
//  bool_vars := rand_sort(select <bvar(Nat)> in body end);
//  body := replace <bvar(Nat)> v in body with bvar(first_index(v, bool_vars)) end;
//  
//  set_it_vars := rand_sort(select SetItVar in body end);
//  body := replace SetItVar v in body with set_it_var(first_index(v, set_it_vars)) end;
//  
//  seq_it_vars := rand_sort(select SeqItVar in body end);
//  body := replace SeqItVar v in body with seq_it_var(first_index(v, seq_it_vars)) end;
//  
//  strm_vars := rand_sort(select StreamVar in body end);
//  body := replace StreamVar v in body with svar(first_index(v, strm_vars)) end;
//  
//  return update_body(pd, body);
//  
//  //## BAD BAD BAD
//  ProcDef update_body(ProcDef pd, [Instr+] body):
//    ObjProcDef    = obj_proc_def(pd.name, pd.in_arity, body),
//    BoolProcDef   = bool_proc_def(pd.name, pd.arity, body);
//}



using (Any => Type) type_map
{
  ObjProcDef gen_fn_code(FnDef fndef)
  {
    fn_res_var := lvar(0);
    tmp_bvar   := bvar(0);

    body := [];

    let ( next_set_it_var_id = 0,
          next_seq_it_var_id = 0,
          next_map_it_var_id = 0,
          next_obj_var_id    = 1,
          next_int_var_id    = 0,
          next_bool_var_id   = 1,
          next_vector_var_id = 0,
          next_stream_var_id = 0)

      //// Checking parameter types
      //for (p, i : fndef.params)
      //  body := body & gen_type_checking_code(p.type, fn_par(i), tmp_bvar) & [check(tmp_bvar)] if p.type?;
      //;
      
      // Setting named variables for parameters
      body := body & [set_var(p.var, fn_par(i)) : p, i <- fndef.params, p.var?];

      // Evaluating the expression
      body := body & gen_eval_code(fndef.expr, fn_res_var);
      
      //// Checking the type of the result
      //if (fndef.res_type?)
      //  body := body & gen_type_checking_code(fndef.res_type, fn_res_var, tmp_bvar) & [check(tmp_bvar)];
      //;
    ;
        
    body := body & [ret_val(fn_res_var)];
    
    return obj_proc_def(fndef.name, length(fndef.params), (v => arity(t) : v => t <- fndef.named_params), body);
  }
}


Program merge_fns_same_name_and_arity(Program prg)
{
  mult_map := apply(prg.fndefs; f(fd) = [fd.name, arity(fd)]);
  
  fns_to_merge := for (na => m <- mult_map)
                    if (m > 1) {{
                      fd : fd <- prg.fndefs ; [fd.name, arity(fd)] == na
                    }};
  
  merged_fns := {merge_fns(fns) : fns <- fns_to_merge};
  
  new_fns := merged_fns & (prg.fndefs - union(fns_to_merge));
  
  return program(tdefs: prg.tdefs, fndefs: new_fns);
}

FnDef merge_fns(FnDef+ fds)
{
  assert size(fds) > 1;
  //if (size({[fd.name, arity(fd), fd.impl_env] : fd <- fds}) /= 1)
  //  print {[fd.name, arity(fd)] : fd <- fds};;
  //assert size({[fd.name, arity(fd), fd.impl_env] : fd <- fds}) = 1;
  
  // try_expr(exprs: [Expr+], cases: [(ptrns: [Pattern+], expr: Expr)+]),
  cases := [];
  for (fd : rand_sort(fds))
    ptrns := [mk_ptrn(p) : p <- fd.params];
    case  := (ptrns: ptrns, expr: fd.expr);
    cases := [case | cases];  
  ;
  
  //## I DON'T LIKE THIS...
  rand_fd      := rand_elem(fds); 
  name         := rand_fd.name;
  arity        := arity(rand_fd);
  named_params := rand_fd.named_params;

  new_expr := match_expr(
                exprs: [fn_par(i) : i <- inc_seq(arity)], //## BAD
                cases: cases
              );

  
  return fn_def(
           name:          name,
           params:        rep_seq(arity, ()), //## BAD
           named_params:  named_params,
           //res_type: ????
           expr:          new_expr
         );

  mk_ptrn(param)
  {
    ptrn := :type_ptrn(if param.type? then param.type else :type_any end);
    ptrn := var_ptrn(name: param.var, ptrn: ptrn) if param.var?;
    return ptrn;
  }
}
