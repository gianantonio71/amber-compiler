using
{
  Nat next_set_it_var_id,
  Nat next_seq_it_var_id,
  Nat next_map_it_var_id,
  Nat next_obj_var_id,
  Nat next_int_var_id;


  [Instr^] gen_ptrn_matching_code(Pattern ptrn, AtomicExpr obj, BoolVar res_var, Var* loc_bound_vars):
    ptrn_var()        = gen_ptrn_var_matching_code(ptrn.var, ptrn.ptrn, obj, res_var, loc_bound_vars),
    ptrn_tag_obj()    = gen_ptrn_tag_obj_matching_code(ptrn.tag, ptrn.obj, obj, res_var, loc_bound_vars),
    ptrn_union(ps?)   = gen_ptrn_union_matching_code(ps, obj, res_var, loc_bound_vars),
    _                 = [set_bvar(res_var, gen_ptrn_matching_expr(ptrn, obj))];


  [Instr^] gen_ptrn_var_matching_code(Var var, Pattern ptrn, AtomicExpr obj, BoolVar res_var, Var* loc_bound_vars) =
    if in(var, loc_bound_vars)
      then [set_bvar(res_var, is_eq(obj, var))]
      else gen_ptrn_matching_code(ptrn, obj, res_var, loc_bound_vars) & [do_if(res_var, set_var(var, obj))]
    end;


  [Instr^] gen_ptrn_tag_obj_matching_code(TagPtrn tag, Pattern obj_ptrn, AtomicExpr obj, BoolVar res_var, Var* loc_bound_vars)
  {
    var  = lvar(next_obj_var_id);

    let (next_obj_var_id = next_obj_var_id + 1)
      code = [ block_failure_if_not(is_tagged_obj(obj), res_var),
                set_var(var, get_tag(obj))
              ] &
              gen_ptrn_matching_code(tag, var, res_var, loc_bound_vars) &
              [ exit_block_if_not(res_var),
                set_var(var, get_inner_obj(obj))
              ] &
              gen_ptrn_matching_code(obj_ptrn, var, res_var, loc_bound_vars);
    ;

    return [execute_block(code)];
  }


  [Instr^] gen_ptrn_union_matching_code(Pattern+ ps, AtomicExpr obj, BoolVar res_var, Var* loc_bound_vars)
  {
    code = [];
    for (p : rand_sort(ps))
      code = code & gen_ptrn_matching_code(p, obj, res_var, loc_bound_vars) & [exit_block_if(res_var)];
    ;
    code = code & [set_bvar(res_var, false)];
    return [execute_block(code)];
  }
}


BoolExpr gen_ptrn_matching_expr(Pattern ptrn, AtomicExpr obj):
  ptrn_symbol                   = is_symb(obj),
  ptrn_integer                  = is_int(obj),
  ptrn_float                    = is_float(obj),
  ptrn_empty_set                = is_eq(obj, empty_set),
  ptrn_ne_set                   = is_ne_set(obj),
  ptrn_empty_seq                = is_eq(obj, empty_seq),
  ptrn_ne_seq                   = is_ne_seq(obj),
  ptrn_empty_map                = is_eq(obj, empty_map),
  ptrn_ne_map                   = is_ne_map(obj),
  ptrn_tag_obj                  = is_tagged_obj(obj),
  ptrn_any                      = true,
  ptrn_symbol(s?)               = is_eq(obj, s),
  ptrn_integer(integer)         = is_int(obj),
  ptrn_integer(low_ints() t?)   = and_then(is_int(obj), is_le(get_int_val(obj), t.max)),
  ptrn_integer(high_ints() t?)  = and_then(is_int(obj), is_ge(get_int_val(obj), t.min)),
  ptrn_integer(int_range() t?)  = and_then(is_int(obj), is_ge(get_int_val(obj), t.min), is_le(get_int_val(obj), max(t))),
  _                             = {fail;};
