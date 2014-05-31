using
{
  Nat next_set_it_var_id,
  Nat next_seq_it_var_id,
  Nat next_map_it_var_id,
  Nat next_obj_var_id,
  Nat next_int_var_id;


  [Instr+] gen_ptrn_matching_code(Pattern ptrn, AtomicExpr obj, BoolVar res_var):
    
    :ptrn_any           = [set_bvar(res_var, true)],

    obj_ptrn(LeafObj x) = [set_bvar(res_var, is_eq(obj, x))],
    
    type_ptrn(t)        = gen_type_checking_code(t, obj, res_var),
    
    ext_var_ptrn(v)     = [set_bvar(res_var, is_eq(obj, v))],
    
    //## THIS WORKS ONLY IF THE PATTERNS THAT REFERENCE A LOCALLY BOUND VAR
    //## ARE TURNED INTO ext_var_ptrn() OBJECTS
    var_ptrn()          = gen_ptrn_matching_code(ptrn.ptrn, obj, res_var) & [do_if(res_var, set_var(ptrn.name, obj))],
    
    tag_ptrn() = {
      var  := lvar(next_obj_var_id);
      
      let (next_obj_var_id = next_obj_var_id + 1)
        code := [ block_failure_if_not(is_tagged_obj(obj), res_var),
                  set_var(var, get_tag(obj))
                ] &
                gen_ptrn_matching_code(ptrn.tag, var, res_var) &
                [ exit_block_if_not(res_var),
                  set_var(var, get_inner_obj(obj))
                ] &
                gen_ptrn_matching_code(ptrn.obj, var, res_var);
      ;
      
      return [execute_block(code)];
    };
}