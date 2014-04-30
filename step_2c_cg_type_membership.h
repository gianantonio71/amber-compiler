BoolProcDef mk_named_type_memb_test_fn(TypeSymbol type_name, (TypeSymbol => Type) typedefs)
{
  res_var := bvar(0);
  
  code := gen_type_checking_code(
            typedefs[type_name],
            fn_par(0),
            res_var;
            next_set_it_var_id = 0,
            next_seq_it_var_id = 0,
            next_map_it_var_id = 0,
            next_obj_var_id    = 0,
            next_int_var_id    = 0
          );

  return bool_proc_def(:memb_test(type_name), 1, code & [ret_val(res_var)]);    
}

using
{
  Nat next_set_it_var_id,
  Nat next_seq_it_var_id,
  Nat next_map_it_var_id,
  Nat next_obj_var_id,
  Nat next_int_var_id;


  [Instr+] gen_type_checking_code(Type type, AtomicExpr obj, BoolVar res_var):

    //## OPTIMIZE FOR SETS OF ANY
    set_type() =
    {
      it_var   := set_it_var(next_set_it_var_id);
      elem_var := lvar(next_obj_var_id);

      elem_code := gen_type_checking_code(
                     type.elem_type,
                     elem_var,
                     res_var;
                     next_obj_var_id    = next_obj_var_id + 1,
                     next_set_it_var_id = next_set_it_var_id + 1
                   );
 
      code := [ maybe_op(block_success_if(is_empty_set(obj), res_var), not type.nonempty),
                block_failure_if_not(is_ne_set(obj), res_var),
                get_iter(it_var, obj),
                repeat(
                  [ break_if(is_out_of_range(it_var)),
                    get_curr_obj(elem_var, it_var)
                  ] &
                  elem_code &                  
                  [ exit_block_if_not(res_var),
                    move_forward(it_var)
                  ]
                ),
                set_bvar(res_var, true)
              ];

      return [execute_block(code)];
    },


    //## OPTIMIZE FOR SEQUENCES OF ANY
    seq_type() =
    {
      elem_var := lvar(next_obj_var_id);
      it_var   := seq_it_var(next_seq_it_var_id);
      
      elem_code := gen_type_checking_code(
                     type.elem_type,
                     elem_var,
                     res_var;
                     next_obj_var_id    = next_obj_var_id + 1,
                     next_seq_it_var_id = next_seq_it_var_id + 1
                   );
      
      code := [ maybe_op(block_success_if(is_empty_seq(obj), res_var), not type.nonempty),
                block_failure_if_not(is_ne_seq(obj), res_var),
                get_iter(it_var, obj),
                repeat(
                  [ break_if(is_out_of_range(it_var)),
                    get_curr_obj(elem_var, it_var)
                  ] &
                  elem_code &
                  [ exit_block_if_not(res_var),
                    move_forward(it_var)
                  ]
                ),
                set_bvar(res_var, true)
              ];
      
      return [execute_block(code)];
    },


    fixed_seq_type(ts) =
    {
      len_var  := ivar(next_int_var_id);
      elem_var := lvar(next_obj_var_id);
      it_var   := seq_it_var(next_seq_it_var_id);
      
      len  := length(ts);

      code := [ set_bvar(res_var, false),
                exit_block_if_not(is_ne_seq(obj)),
                set_ivar(len_var, get_seq_len(obj)),
                exit_block_if_not(is_eq(len_var, len)),
                get_iter(it_var, obj)
              ];

      let ( next_int_var_id = next_int_var_id + 1,
            next_obj_var_id = next_obj_var_id + 1,
            next_seq_it_var_id = next_seq_it_var_id + 1)
                  
        for (t, i : ts)
          code := code &
                  [get_curr_obj(elem_var, it_var)] &
                  gen_type_checking_code(t, elem_var, res_var) &
                  [ exit_block_if_not(res_var),
                    maybe_op(move_forward(it_var), i /= len - 1)
                  ];
        ;
      ;
      
      code := code & [set_bvar(res_var, true)];
      
      return [execute_block(code)];
    },


    map_type() =
    {
      obj_var := lvar(next_obj_var_id);
      it_var  := map_it_var(next_map_it_var_id);
      
      let (next_obj_var_id = next_obj_var_id + 1, next_map_it_var_id = next_map_it_var_id + 1)
        code := [ block_success_if(is_empty_map(obj), res_var),
                  block_failure_if_not(is_ne_map(obj), res_var),
                  get_iter(it_var, obj),
                  repeat(
                    [ break_if(is_out_of_range(it_var)),
                      get_curr_key(obj_var, it_var)
                    ] &
                    gen_type_checking_code(type.key_type, obj_var, res_var) &
                    [ exit_block_if_not(res_var),
                      get_curr_value(obj_var, it_var)
                    ] &
                    gen_type_checking_code(type.value_type, obj_var, res_var) &
                    [ exit_block_if_not(res_var),
                      move_forward(it_var)
                    ]
                  ),
                  set_bvar(res_var, true)
                ];
      ;
            
      return [execute_block(code)];                          
    },


    tuple_type(fs) =
    {
      size_var := ivar(next_int_var_id);
      obj_var  := lvar(next_obj_var_id);
      it_var   := map_it_var(next_map_it_var_id);

      max_fields := size(fs);
      min_fields := size({f : f <- fs ; not f.optional});
      
      code := [ maybe_op(block_success_if(is_empty_map(obj), res_var), min_fields == 0),
                block_failure_if_not(is_ne_map(obj), res_var),
                set_ivar(size_var, get_map_size(obj)),
                block_failure_if_not(is_between(size_var, min_fields, max_fields), res_var),
                get_iter(it_var, obj)
              ];

      sorted_fields := sort_set(fs; is_strictly_ordered(f1, f2) = f1.label < f2.label);

      for (b : sorted_fields)
        inner_code := [set_var(obj_var, get_curr_value(it_var))] &
                      gen_type_checking_code(
                        b.type,
                        obj_var,
                        res_var;
                        next_int_var_id    = next_int_var_id + 1,
                        next_obj_var_id    = next_obj_var_id + 1,
                        next_map_it_var_id = next_map_it_var_id + 1
                      ) &
                      [exit_block_if_not(res_var), move_forward(it_var)];
                    
        if (b.optional)
          code := code & [ do_if_not(is_out_of_range(it_var),
                             [ set_var(obj_var, get_curr_key(it_var)),
                               do_if(is_eq(obj_var, b.label), inner_code)                              
                             ]
                           )
                         ];
        else
          code := code & [ block_failure_if(is_out_of_range(it_var), res_var),
                           set_var(obj_var, get_curr_key(it_var)),
                           block_failure_if_not(is_eq(obj_var, b.label), res_var)
                         ] & inner_code;
        ;
      ;
      
      code := code & [set_bvar(res_var, is_out_of_range(it_var))];
      
      return [execute_block(code)];  
    },


    tag_type() =
    {
      obj_var := lvar(next_obj_var_id);

      let (next_obj_var_id = next_obj_var_id + 1)
        code := [ block_failure_if_not(is_tagged_obj(obj), res_var),
                  set_var(obj_var, get_tag(obj))
                ] &
                gen_type_checking_code(type.tag_type, obj_var, res_var) &
                [ exit_block_if_not(res_var),
                  set_var(obj_var, get_inner_obj(obj))
                ] &
                gen_type_checking_code(type.obj_type, obj_var, res_var);
      ;
           
      return [execute_block(code)];
    },


    union_type(ts) =
    {
      //## PERFORMANCE COULD BE IMPROVED HERE USING A SWITCH/CASE
      code := [];
      for (t : rand_sort(ts))
        code := code & gen_type_checking_code(t, obj, res_var) & [exit_block_if(res_var)];
      ;
      return [execute_block(code)];
    },


    _             = [set_bvar(res_var, gen_type_checking_expr(type, obj))];
}


BoolExpr gen_type_checking_expr(Type type, AtomicExpr obj):
  :type_any       = true,
  :atom_type      = is_symb(obj),
  symb_type(s)    = is_eq(s, obj),
  :integer        = is_int(obj),
  low_ints()      = and_then(is_int(obj), is_le(get_int_val(obj), type.max)),
  high_ints()     = and_then(is_int(obj), is_ge(get_int_val(obj), type.min)),
  int_range()     = and_then(is_int(obj), is_ge(get_int_val(obj), type.min), is_le(get_int_val(obj), max(type))),
  type_ref(ts)    = eval_bool_fn(:memb_test(ts), [obj]),
  type_var()      = true, //## BUG BUG BUG THIS IS TEMPORARY...
  :empty_seq_type = is_eq(obj, empty_seq),
  :empty_set_type = is_eq(obj, empty_seq),
  :empty_map_type = is_eq(obj, empty_map);

