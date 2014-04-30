using
{
  Nat next_set_it_var_id,
  Nat next_seq_it_var_id,
  Nat next_map_it_var_id,
  Nat next_obj_var_id,
  Nat next_int_var_id;


  [Instr+] gen_ptrn_matching_code(Pattern ptrn, AtomicExpr obj, BoolVar res_var):
    
    obj_ptrn(LeafObj x) = [set_bvar(res_var, is_eq(obj, x))],
    
    type_ptrn(t)        = gen_type_checking_code(t, obj, res_var),
    
    ext_var_ptrn(v)     = [set_bvar(res_var, is_eq(obj, v))],
    
    //## THIS WORKS ONLY IF THE PATTERNS THAT REFERENCE A LOCALLY BOUND VAR
    //## ARE TURNED INTO ext_var_ptrn() OBJECTS
    var_ptrn()          = if ptrn.ptrn? then
                            gen_ptrn_matching_code(ptrn.ptrn, obj, res_var) &
                            [do_if(res_var, set_var(ptrn.name, obj))]
                          else
                            [set_var(ptrn.name, obj), set_bvar(res_var, true)]
                          end,
    
    tuple_ptrn() = {
      obj_var  := lvar(next_obj_var_id);
      it_var   := map_it_var(next_map_it_var_id);

      sorted_fields := sort_set(ptrn.fields; is_strictly_ordered(f1, f2) = f1.label < f2.label);

      code := [ maybe_op(block_success_if(is_empty_map(obj), res_var), sorted_fields == []),
                block_failure_if_not(is_ne_map(obj), res_var),
                maybe_op(block_failure_if_not(is_eq(get_map_size(obj), length(sorted_fields)), res_var), not ptrn.is_open),
                maybe_op(get_iter(it_var, obj), not ptrn.is_open)
              ];
      
      //## BAD BAD BAD SEE IF THE CODE CAN BE MADE A BIT NICER
      let (next_obj_var_id = next_obj_var_id + 1, next_map_it_var_id = next_map_it_var_id + 1)
        if (ptrn.is_open)
          //## MAYBE HERE I SHOULD CHECK THAT THE OBJECT IS ACTUALLY A TUPLE, NOT JUST A MAP
          for (f : sorted_fields)
            code := code &
                    [ lookup(res_var, obj_var, obj, f.label),
                      exit_block_if_not(res_var)
                    ] &
                    gen_ptrn_matching_code(f.ptrn, obj_var, res_var) &
                    [ exit_block_if_not(res_var)];
          ;
        else
          for (f, i : sorted_fields)
            code := code &
                    [ maybe_op(move_forward(it_var), i > 0), //block_failure_if(is_out_of_range(it_var), res_var),
                      set_var(obj_var, get_curr_key(it_var)),
                      block_failure_if_not(is_eq(obj_var, f.label), res_var),
                      set_var(obj_var, get_curr_value(it_var))
                    ] &
                    gen_ptrn_matching_code(f.ptrn, obj_var, res_var) &
                    [ exit_block_if_not(res_var)//,
                      //move_forward(it_var)
                    ];
          ;
        ;
      ;

      return [execute_block(code)];
    },
    
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