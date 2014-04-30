
//## FIND BETTER NAME
type FinalMatchAction = set_found_var_and_leave(var: ObjVar),
                        eval_expr_and_add_to_set(expr: Expr, stream_var: StreamVar),
                        eval_exprs_and_add_to_map(
                          key_expr:         Expr,
                          value_expr:       Expr,
                          key_stream_var:   StreamVar,
                          value_stream_var: StreamVar
                        );

//## FIND BETTER NAME
type CondMatchAction  = cond_match_action(cond: Expr, action: FinalMatchAction);

type MatchAction      = FinalMatchAction,
                        CondMatchAction,
                        match_action(clause: Clause, action: MatchAction);
                   


FinalMatchAction set_found_var_and_leave(ObjVar v) = set_found_var_and_leave(var: v);

FinalMatchAction eval_expr_and_add_to_set(Expr e, StreamVar sv) =
  eval_expr_and_add_to_set(expr: e, stream_var: sv);

FinalMatchAction eval_exprs_and_add_to_map(Expr ke, Expr ve, StreamVar ksv, StreamVar vsv) =
  eval_exprs_and_add_to_map(
    key_expr:         ke,
    value_expr:       ve,
    key_stream_var:   ksv,
    value_stream_var: vsv
  );

CondMatchAction action(Expr c, FinalMatchAction a) = cond_match_action(cond: c, action: a);

MatchAction action(Clause c, MatchAction a) = match_action(clause: c, action: a);


using
{
  Nat next_obj_var_id,
  Nat next_int_var_id,
  Nat next_bool_var_id,
  Nat next_set_it_var_id,
  Nat next_seq_it_var_id,
  Nat next_map_it_var_id,
  Nat next_vector_var_id,
  Nat next_stream_var_id;


  [Instr*] gen_code(MatchAction action):
  
    match_action() = gen_iter_code(action.clause, action.action),

    cond_match_action() = {
      cond_var    := lvar(next_obj_var_id);
      cond_info   := gen_eval_info(action.cond, cond_var; next_obj_var_id = next_obj_var_id + 1);
      action_code := gen_code(action.action);
      
      return cond_info.eval_code &
             [ check(is_bool(cond_info.expr)),
               do_if(is_true(cond_info.expr), action_code)
             ];
    },

    set_found_var_and_leave() = [set_var(action.var, obj_true), exit_block],

    eval_expr_and_add_to_set() = {
      tmp_var := lvar(next_obj_var_id);
      info    := gen_eval_info(action.expr, tmp_var; next_obj_var_id = next_obj_var_id + 1);
      return info.add_ref_eval_code & [append(action.stream_var, info.expr)];     
    },
    
    eval_exprs_and_add_to_map() = {
      tmp_var    := lvar(next_obj_var_id);
      
      key_info   := gen_eval_info(action.key_expr, tmp_var; next_obj_var_id = next_obj_var_id + 1);
      value_info := gen_eval_info(action.value_expr, tmp_var; next_obj_var_id = next_obj_var_id + 1);
    
      return key_info.add_ref_eval_code   & [append(action.key_stream_var, key_info.expr)] &
             value_info.add_ref_eval_code & [append(action.value_stream_var, value_info.expr)];
    };


  [Instr+] gen_iter_code(Clause clause, MatchAction action):

    in_clause() = {
      src_var  := lvar(next_obj_var_id);
      tmp_var  := lvar(next_obj_var_id + 1);
      res_var  := bvar(next_bool_var_id);
      it_var   := set_it_var(next_set_it_var_id);

      let (next_obj_var_id = next_obj_var_id + 1)
        // Variables to avoid: src_var
        src_info := gen_eval_info(clause.src, src_var);

        let (next_set_it_var_id = next_set_it_var_id + 1)
          // Variables to avoid: src_var, it_var
          next_step_code := gen_code(action);

          // Variables to avoid: src_var, it_var, res_var, tmp_var
          match_code := gen_ptrn_matching_code(
                          clause.ptrn,
                          tmp_var,
                          res_var;
                          next_obj_var_id  = next_obj_var_id  + 1,
                          next_bool_var_id = next_bool_var_id + 1
                        );
        ;
      ;

      loop_code := [ get_iter(it_var, src_info.expr),
                     repeat(
                       [ break_if(is_out_of_range(it_var)),
                         set_var(tmp_var, get_curr_obj(it_var))
                       ] &
                       match_code &
                       [ do_if(res_var, next_step_code),
                         move_forward(it_var)
                       ]
                     )
                   ];

      return src_info.eval_code & loop_code & src_info.cleanup_code;
    },

    not_in_clause() = {
      src_var := lvar(next_obj_var_id);
      tmp_var := lvar(next_obj_var_id + 1);
      res_var := bvar(next_bool_var_id);
      it_var  := set_it_var(next_set_it_var_id);

      let (next_obj_var_id = next_obj_var_id + 1)
        // Variables to avoid: src_var
        src_info := gen_eval_info(clause.src, src_var);
        
        // Variables to avoid: src_var, it_var, tmp_var, res_var
        match_code := gen_ptrn_matching_code(
                        clause.ptrn,
                        tmp_var,
                        res_var;
                        next_obj_var_id    = next_obj_var_id    + 1,
                        next_bool_var_id   = next_bool_var_id   + 1,
                        next_set_it_var_id = next_set_it_var_id + 1
                      );

        // Variables to avoid: src_var
        next_step_code := gen_code(action);
      ;

      loop_code := [ get_iter(it_var, src_info.expr),
                     repeat(
                       [ break_if(is_out_of_range(it_var)),
                         set_var(tmp_var, get_curr_obj(it_var))
                       ] & match_code &
                       [ do_if(res_var, exit_block),
                         move_forward(it_var)
                       ]
                     )
                     //## BUG BUG BUG HERE I MUST EVALUATE sel_expr FIRST, OR MAYBE
                     //## I CAN EVALUATE IT JUST ONCE. THINK ABOUT IT.
                   ];
      
      return src_info.eval_code & [execute_block(loop_code & next_step_code)] & src_info.cleanup_code;
    },

    map_in_clause() = {
      src_var  := lvar(next_obj_var_id);
      tmp_var  := lvar(next_obj_var_id + 1);
      res_var  := bvar(next_bool_var_id);
      it_var   := map_it_var(next_map_it_var_id);
      
      let (next_obj_var_id = next_obj_var_id + 1)
        // Variables to avoid: src_var      
        src_info := gen_eval_info(clause.src, src_var);

        let (next_set_it_var_id = next_set_it_var_id + 1)
          // Variables to avoid: src_var, it_var
          next_step_code := gen_code(action);

          let (next_obj_var_id = next_obj_var_id + 1, next_bool_var_id = next_bool_var_id + 1)
            // Variables to avoid: src_var, it_var, tmp_var, res_var      
            key_ptrn_code := gen_ptrn_matching_code(clause.key_ptrn, tmp_var, res_var);
            
            // Variables to avoid: src_var, it_var, tmp_var, res_var      
            value_ptrn_code := gen_ptrn_matching_code(clause.value_ptrn, tmp_var, res_var);
          ;
        ;
      ;
            
      loop_code := [ get_iter(it_var, src_info.expr),
                     repeat(
                       [ break_if(is_out_of_range(it_var)),
                         set_var(tmp_var, get_curr_key(it_var))
                       ] & key_ptrn_code &
                       [ do_if(
                           res_var,
                           [set_var(tmp_var, get_curr_value(it_var))] &
                           value_ptrn_code &
                           [do_if(res_var,next_step_code)]
                         ),
                         move_forward(it_var)
                       ]
                     )
                   ];
             
      return src_info.eval_code & loop_code & src_info.cleanup_code;
    },

    map_not_in_clause() = {
      src_var := lvar(next_obj_var_id);
      tmp_var := lvar(next_obj_var_id + 1);
      res_var := bvar(next_bool_var_id);
      it_var  := map_it_var(next_map_it_var_id);

      let (next_obj_var_id = next_obj_var_id + 1)      
        //## HERE I PROBABLY NEED TO HAVE A VARIABLE
        // Variables to avoid: src_var
        src_info := gen_eval_info(clause.src, src_var);
        
        let ( next_obj_var_id    = next_obj_var_id + 1,
              next_bool_var_id   = next_bool_var_id + 1,
              next_map_it_var_id = next_map_it_var_id + 1)
              
          // Variables to avoid: src_var, it_var, tmp_var, res_var      
          key_ptrn_code := gen_ptrn_matching_code(clause.key_ptrn, tmp_var, res_var);
          
          // Variables to avoid: src_var, it_var, tmp_var, res_var      
          value_ptrn_code := gen_ptrn_matching_code(clause.value_ptrn, tmp_var, res_var);
        ;

        // Variables to avoid: src_var
        next_step_code := gen_code(action);
      ;
      
      loop_code := [ get_iter(it_var, src_info.expr),
                     repeat(
                       [ break_if(is_out_of_range(it_var)),
                         set_var(tmp_var, get_curr_key(it_var))
                       ] &
                       key_ptrn_code &
                       [ do_if(
                           res_var,
                           [set_var(tmp_var, get_curr_value(it_var))] &
                           value_ptrn_code &
                           [do_if(res_var, exit_block)]
                         ),
                         move_forward(it_var)
                       ]
                     )
                   ];
      
      return src_info.eval_code & [execute_block(loop_code & next_step_code)] & src_info.cleanup_code;
    },
    
    or_clause()   = gen_iter_code(clause.left, action) & gen_iter_code(clause.right, action),
    
    and_clause() = gen_iter_code(clause.left, action(clause.right, action));
}
