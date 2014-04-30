
//  gen_eval_code(expr, var)
//    Generates code that evaluates <expr> and stores the result in <var>, reference counted

//  gen_eval_info(expr, var)
//    Generates code needed to evaluate expr, and to cleanup after it's not used anymore
//    If need be, the code stores the result in variable var, but it doesn't have to
//    It also generates an expression that is used to access the result
//    The expression may not be valid anymore if a variable used in the expression
//    is updated or goes out of scope

//  gen_eval_info(expr)
//    Like above, but automatically choses the name of the variable, if one is needed.
//    Also returns the id of the first free object variable.


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


  [Instr+] gen_fn_body(Expr expr)
  {
    fn_res_var := lvar(next_obj_var_id);
    code := gen_eval_code(expr, fn_res_var; next_obj_var_id = next_obj_var_id + 1);
    return code & [ret_val(fn_res_var)];
  }


  ( eval_code:         [Instr*],
    cleanup_code:      [Instr*],
    add_ref_eval_code: [Instr*],
    expr:              AtomicExpr,
    var_used:          Bool
  )
  gen_eval_info(Expr expr, ObjVar var):
    LeafObj   = ( eval_code:         [],
                  cleanup_code:      [],
                  add_ref_eval_code: [],
                  expr:              expr,
                  var_used:          false
                ),

    Var       = ( eval_code:         [],
                  cleanup_code:      [],
                  add_ref_eval_code: [add_ref(expr)],
                  expr:              expr,
                  var_used:          false
                ),

    _         = { eval_code    := gen_eval_code(expr, var);
                  
                  return ( 
                    eval_code:         eval_code,
                    cleanup_code:      [release(var)],
                    add_ref_eval_code: eval_code,
                    expr:              var,
                    var_used:          true
                  );
                };


  ( eval_code:         [Instr*],
    cleanup_code:      [Instr*],
    add_ref_eval_code: [Instr*],
    expr:              AtomicExpr,
    var_used:          Bool,
    next_var_id:       Nat
  )
  gen_eval_info(Expr expr)
  {
    var    := lvar(next_obj_var_id);
    info   := gen_eval_info(expr, var; next_obj_var_id = next_obj_var_id + 1); //## BUG? BUG? BUG?
    return info & (next_var_id: next_obj_var_id + if info.var_used then 1 else 0 end);
  }


  ( eval_code:         [Instr*],
    cleanup_code:      [Instr*],
    add_ref_eval_code: [Instr*],
    exprs:             [AtomicExpr*],
    next_var_id:       Nat
  )
  gen_eval_info([Expr*] exprs)
  {
    eval_code         := [];
    cleanup_code      := [];
    add_ref_eval_code := [];
    res_exprs         := [];
    next_var_id       := next_obj_var_id;
    
    for (e : exprs)
      info := gen_eval_info(e; next_obj_var_id = next_var_id);
      eval_code         := eval_code & info.eval_code;
      cleanup_code      := info.cleanup_code & cleanup_code;
      add_ref_eval_code := add_ref_eval_code & info.add_ref_eval_code;
      res_exprs         := res_exprs & [info.expr];
      next_var_id       := info.next_var_id;
    ;

    return (
      eval_code:            eval_code,
      cleanup_code:         cleanup_code,
      add_ref_eval_code:    add_ref_eval_code,
      exprs:                res_exprs,
      next_var_id:          next_var_id
    );
  }

  
  //## THIS IS ALL WRONG (WHY?)
  (code: [Instr*], vect_var: VecVar, count_var: IntVar)
  gen_vector_eval_info([SubExpr*] exprs)
  {
    elems_var := vvar(next_vector_var_id, length(exprs));
    count_var := ivar(next_int_var_id);
    
    code := gen_vector_eval_code(
              exprs,
              elems_var,
              count_var;
              next_vector_var_id = next_vector_var_id + 1,
              next_int_var_id    = next_int_var_id + 1
            );
    
    return (code: code, vect_var: elems_var, count_var: count_var);


    [Instr*] gen_vector_eval_code([SubExpr*] exprs, VecVar elems_var, IntVar count_var)
    {
      curr_slot_var := evar(elems_var.id, count_var);
      cond_var      := lvar(next_obj_var_id);
      
      code := [set_ivar(count_var, 0)];
      
      for (e : exprs)
        if (e :: Expr)
          new_code := gen_eval_code(e, curr_slot_var) & [increment(count_var)];
          
        else
          assert e :: CondExpr;
          
          cond_eval_info := gen_eval_info(e.cond, cond_var; next_obj_var_id = next_obj_var_id + 1);
          
          // No need to change next_obj_var_id, as cond_var is not used anymore when running this code
          expr_eval_code := gen_eval_code(e.expr, curr_slot_var);
          
          new_code := cond_eval_info.eval_code &
                      [ check(is_bool(cond_eval_info.expr)),
                        do_if(
                          is_true(cond_eval_info.expr),
                          expr_eval_code & [increment(count_var)]
                        )
                      ];
        ;
        
        code := code & new_code;
      ;

      return code;
    }
  }


  [SubExpr*] sort_exprs_first(SubExpr* exprs)
  {
    pure_exprs := {e : Expr e <- exprs};
    cond_exprs := exprs - pure_exprs;
    return rand_sort(pure_exprs) & rand_sort(cond_exprs);
  }
   

  [Instr*] gen_eval_code(BuiltIn name, [AtomicExpr*] params, ObjVar res_var)
  {
    return [gen_eval_instr(name, params, res_var)];

    Instr gen_eval_instr(BuiltIn name, [AtomicExpr*] ps, ObjVar res_var):
      :slice        = get_seq_slice(res_var, ps[0], get_int_val(ps[1]), get_int_val(ps[2])),
      :cat          = join_seqs(res_var, ps[0], ps[1]),
      :rev          = rev_seq(res_var, ps[0]),
      :set          = seq_to_set(res_var, ps[0]),
      :at           = get_at(res_var, ps[0], get_int_val(ps[1])),
      :mset         = seq_to_mset(res_var, ps[0]),
      :isort        = internal_sort(res_var, ps[0]),
      :list_to_seq  = list_to_seq(res_var, ps[0]),
      _             = set_var(res_var, gen_eval_expr(name, ps));
    
    ObjExpr gen_eval_expr(BuiltIn name, [AtomicExpr*] ps):
      :str      = to_str(ps[0]),
      :symb     = to_symb(ps[0]),
      :neg      = to_obj(minus(get_int_val(ps[0]))),
      :add      = to_obj(add(get_int_val(ps[0]), get_int_val(ps[1]))),
      :mult     = to_obj(mult(get_int_val(ps[0]), get_int_val(ps[1]))),
      :counter  = to_obj(unique_int),
      :len      = to_obj(get_seq_len(ps[0]));
  }
  
  
  [Instr+] gen_eval_code(Expr expr, ObjVar res_var):

    object()        = [set_var(res_var, expr)],

    Var             = [set_var(res_var, expr), add_ref(res_var)],

    do_expr(ss)     = [execute_block(gen_code(ss, res_var))],

    select_expr()   = gen_eval_code(simplify(expr), res_var), //## BAD
    replace_expr()  = gen_eval_code(simplify(expr), res_var), //## BAD


    //## HERE WE CAN SLIGHTLY IMPROVE PERFORMANCE BY USING GEN_EVAL_INFO FOR THE FIRST EXPRESSION
    and_expr()      = gen_eval_code(expr.left, res_var) &
                      [ check(is_bool(res_var)),
                        do_if(
                          is_true(res_var),
                          gen_eval_code(expr.right, res_var) & [check_is_bool(res_var)]
                        )
                      ],

    //## HERE WE CAN SLIGHTLY IMPROVE PERFORMANCE BY USING GEN_EVAL_INFO FOR THE FIRST EXPRESSION
    or_expr()       = gen_eval_code(expr.left, res_var) &
                      [ check(is_bool(res_var)),
                        do_if(
                          is_false(res_var),
                          gen_eval_code(expr.right, res_var) & [check(is_bool(res_var))]
                        )
                      ],
    
                      //## BAD BAD BAD
    not_expr(e)     = gen_eval_code(e, res_var) &
                      [ check(is_bool(res_var)),
                        branch(is_true(res_var),
                          [set_var(res_var, obj_false)],
                          [set_var(res_var, obj_true)]
                        )
                      ],

    
    set_expr(es) =
    {
      return [set_var(res_var, empty_set)] if es == {};
      info := gen_vector_eval_info(sort_exprs_first(es));
      return info.code & [mk_set(res_var, info.vect_var, info.count_var)];
    },


    seq_expr() =
    {
      if (expr.tail?)
        head_res_var := lvar(next_obj_var_id);
        new_obj_var_id := next_obj_var_id + 1;
      else
        head_res_var := res_var;
        new_obj_var_id := next_obj_var_id;                        
      ;

      if (expr.head /= [])
        info := gen_vector_eval_info(expr.head; next_obj_var_id = new_obj_var_id);
        code := info.code & [mk_seq(head_res_var, info.vect_var, info.count_var)];
      else
        code := [set_var(head_res_var, empty_seq)];
      ;
      
      if (expr.tail?)
        // info.vect_var and info.count_var are not in use anymore here and can be reused.
        info := gen_eval_info(expr.tail; next_obj_var_id = new_obj_var_id);
        code := code & info.eval_code &
                [ join_seqs(res_var, head_res_var, info.expr),
                  release(head_res_var)
                ];
      ;
      return code;
    },


    map_expr(es) =
    {
      return [set_var(res_var, empty_map)] if es == {};

      cond_var   := lvar(next_obj_var_id);
      keys_var   := vvar(next_vector_var_id, size(es));
      values_var := vvar(next_vector_var_id + 1, size(es));
      count_var  := ivar(next_int_var_id);

      curr_key_slot_var   := evar(keys_var.id, count_var);
      curr_value_slot_var := evar(values_var.id, count_var);
      
      code := [set_ivar(count_var, 0)];

      let (next_int_var_id = next_int_var_id + 1, next_vector_var_id = next_vector_var_id + 2)
        for (e : rand_sort(es))
          key_code   := gen_eval_code(e.key, curr_key_slot_var);
          value_code := gen_eval_code(e.value, curr_value_slot_var);
          entry_code := key_code & value_code & [increment(count_var)];
                        
          if (e.cond?)
            cond_info := gen_eval_info(e.cond, cond_var; next_obj_var_id = next_obj_var_id + 1);
            
            entry_code := cond_info.eval_code &
                          [ check(is_bool(cond_info.expr)),
                            do_if(is_true(cond_info.expr), entry_code)
                          ];
          ;
          
          code := code & entry_code;
        ;
      ;
      
      return code & [mk_map(res_var, keys_var, values_var, count_var)];
    },


    tag_obj_expr() =
    {
      info := gen_eval_info([expr.tag, expr.obj]);
      return info.add_ref_eval_code & [mk_tagged_obj(res_var, info.exprs[0], info.exprs[1])];
    },


    // fn_call(name: FnSymbol, params: [ExtExpr*], named_params: (<named_par(Atom)> => ExtExpr)), //## NEW BAD BAD
    fn_call() = make_scopes(rand_sort_pairs(expr.named_params), (expr: expr, res_var: res_var)), //## BAD BAD BAD
    //{
    //  pars_info := gen_eval_info(expr.params);
    //  call_code := [call_proc(res_var, expr.name, pars_info.exprs)];
    //  code := pars_info.eval_code & call_code & pars_info.cleanup_code;
    //  if (expr.named_params /= ())
    //    //## BUG BUG BUG. THE ASSIGNMENTS ARE DONE IN RANDOM ORDER. FIX THIS
    //    nps := rand_sort_pairs(expr.named_params);
    //    code := make_scopes(nps, code);
    //  ;
    //  return code;
    //},

    //## BAD BAD BAD TOO SIMILAR TO THE ABOVE CODE
    cls_call() =
    {
      pars_info := gen_eval_info(expr.params);
      call_code := [call_cls(res_var, expr.name, pars_info.exprs)];
      return pars_info.eval_code & call_code & pars_info.cleanup_code;
    },


    //## BAD BAD BAD TOO SIMILAR TO THE ABOVE CODE
    builtin_call() =
    {
      pars_info := gen_eval_info(expr.params);
      call_code := gen_eval_code(expr.name, pars_info.exprs, res_var);
      return pars_info.eval_code & call_code & pars_info.cleanup_code;
    },


    eq() =
    {
      info := gen_eval_info([expr.left, expr.right]);
      return info.eval_code &
             [set_var(res_var, to_obj(is_eq(info.exprs[0], info.exprs[1])))] &
             info.cleanup_code;
    },


    membership() =
    {
      //bool_var_id := next_bool_var_id;
      bool_var := bvar(next_bool_var_id);

      info := gen_eval_info(expr.obj);
      
      code := gen_type_checking_code(
                expr.type,
                info.expr,
                bool_var;
                next_obj_var_id  = info.next_var_id,
                next_bool_var_id = next_bool_var_id + 1
              );

      return info.eval_code & code & [set_var(res_var, to_obj(bool_var))] & info.cleanup_code;
    },


    accessor() =
    {
      info := gen_eval_info(expr.expr);
      code := [ ext_lookup(res_var, info.expr, expr.field),
                add_ref(res_var)
              ];
      return info.eval_code & code & info.cleanup_code;  
    },


    accessor_test() =
    {
      info := gen_eval_info(expr.expr);
      bvar := bvar(next_bool_var_id);
      // Here I use res_var to store a temporary value
      // that has nothing to do with the actual result
      code := [ ext_lookup(bvar, res_var, info.expr, expr.field),
                set_var(res_var, to_obj(bvar))
              ];
      return info.eval_code & code & info.cleanup_code;
    },


    if_expr() =
    {
      info := gen_eval_info(expr.cond);
      code := [ check(is_bool(info.expr)),
                branch(
                  is_true(info.expr),
                  gen_eval_code(expr.then, res_var),
                  gen_eval_code(expr.else, res_var)
                )
              ];
      return info.eval_code & code; // No need to cleanup the condition object
    },


    match_expr() =
    {
      tmp_bvar := bvar(next_bool_var_id);

      info := gen_eval_info(expr.exprs);

      code := [terminate];
      for (c : reverse(expr.cases))
        let (next_obj_var_id = info.next_var_id)
          case_code := gen_eval_code(c.expr, res_var);
          case_code := case_code & [exit_block];
          for (p, i : reverse(c.ptrns))
            // No need for now to set next_bool_var_id as it's not used
            // by gen_ptrn_matching_code
            case_code := gen_ptrn_matching_code(p, rev_at(info.exprs, i), tmp_bvar) &
                         [do_if(tmp_bvar, case_code)];
          ;
        ;
        code := case_code & code;
      ;
      code := [execute_block(code)];
      
      return info.eval_code & code & info.cleanup_code;
    },


    ex_qual() =
    {
      action := set_found_var_and_leave(res_var);
      action := action(expr.sel_expr, action) if expr.sel_expr?;
      
      code := gen_iter_code(expr.source, action);
      
      return [set_var(res_var, obj_false), execute_block(code)];
    },


    set_comp() =
    {
      strm_var := svar(next_stream_var_id);

      action := eval_expr_and_add_to_set(expr.expr, strm_var);
      action := action(expr.sel_expr, action) if expr.sel_expr?;
      
      code := gen_iter_code(expr.source, action; next_stream_var_id = next_stream_var_id + 1);
      
      return [init_stream(strm_var)] & code & [mk_set_from_stream(res_var, strm_var)];
    },


    map_comp() =
    {
      key_strm_var   := svar(next_stream_var_id);
      value_strm_var := svar(next_stream_var_id + 1);

      action := eval_exprs_and_add_to_map(expr.key_expr, expr.value_expr, key_strm_var, value_strm_var);
      action := action(expr.sel_expr, action) if expr.sel_expr?;
      
      code := gen_iter_code(expr.source, action; next_stream_var_id = next_stream_var_id + 2);

      return [init_stream(key_strm_var), init_stream(value_strm_var)] & code &
             [mk_map_from_streams(res_var, key_strm_var, value_strm_var)];
    },


    seq_comp() =
    {
      src_var  := lvar(next_obj_var_id);
      item_var := lvar(next_obj_var_id + 1);
      sel_var  := lvar(next_obj_var_id + 2);
      it_var   := seq_it_var(next_seq_it_var_id);
      strm_var := svar(next_stream_var_id);
      idx_var  := ivar(next_int_var_id); //## BAD BAD BAD USED EVEN WHEN NOT REQUIRED

      let ( next_obj_var_id    = next_obj_var_id    + 3,
            next_seq_it_var_id = next_seq_it_var_id + 1,
            next_stream_var_id = next_stream_var_id + 1,
            next_int_var_id    = next_int_var_id    + 1)

        src_info  := gen_eval_info(expr.src_expr, src_var);
        item_info := gen_eval_info(expr.expr, item_var);
        sel_info  := if expr.sel_expr? then gen_eval_info(expr.sel_expr, sel_var) else nil end; //## BUG BUG BUG
      ;
            
      needs_idx_var := not expr.sel_expr? or expr.idx_var?;
      knows_size := not expr.sel_expr?;
      
      eval_and_assign_code := item_info.add_ref_eval_code &
                              if knows_size
                                then [set_at(res_var, idx_var, item_info.expr)]
                                else [append(strm_var, item_info.expr)]
                              end;
      
      core_loop_code := eval_and_assign_code;
      if (expr.sel_expr?)
        core_loop_code := sel_info.eval_code &
                          [ check(is_bool(sel_info.expr)),
                            do_if(is_true(sel_info.expr), core_loop_code)
                          ];
      ;
      
      loop_code := [ if knows_size
                       then mk_array(res_var, get_seq_len(src_info.expr), obj_nil)
                       else init_stream(strm_var)
                     end,
                     get_iter(it_var, src_info.expr),
                     maybe_op(set_ivar(idx_var, 0), needs_idx_var),
                     repeat(
                       [ break_if(is_out_of_range(it_var)),
                         set_var(expr.var, get_curr_obj(it_var)),
                         if expr.idx_var? then set_var(expr.idx_var, to_obj(idx_var)) else no_op end
                       ] &
                       core_loop_code &
                       [ move_forward(it_var),
                         maybe_op(increment(idx_var), needs_idx_var)
                       ]
                     ),
                     maybe_op(mk_seq_from_stream(res_var, strm_var), not knows_size)
                   ];

      return src_info.eval_code & loop_code & src_info.cleanup_code;
    };

    ////## THERE MIGHT BE A BUG HERE. WHAT HAPPENS IF THE WHERE CLAUSE CONTAINS MORE THAN
    ////## ONE ASSIGNMENT AND THE SECOND ONE REFERENCES THE PARAMETER SET BY THE FIRST?
    ////## THE PROBLEM IS PROBABLY INTRINSIC IN THE cls_scope(cls: ClsDef, body: [Instr+]) OBJECT
    //where_expr() =
    //{
    //  code := gen_eval_code(expr.expr, res_var);
    //  for (cls : rand_sort(expr.fndefs))
    //    //## HERE I'M EXCLUDING ALL fn_par() VARIABLES DEFINED LOCALLY. BUT IF AND WHEN I INTRODUCE
    //    //## A NOTATION TO ACCESS THE fn_par() DIRECTLY, I WOULD STILL BE ABLE TO ACCESS SOME
    //    //## OF THE fn_par() VARIABLES OF THE PARENT FUNCTION IF THIS HAS MORE ARGUMENTS THAN
    //    //## THE CLOSURE. I SHOULD CHECK AND STOP THIS DURING THE WELL-FORMEDNESS CHECK.
    //    loc_vs   := set([v : v <- cls.vars, v /= nil] & [:fn_par(i) : i <- inc_seq(length(cls.vars))]);
    //    ext_vs   := rand_sort(extern_vars(cls.body) - loc_vs);
    //    cls_body := [set_var(v, fn_par(i)) : v, i <- cls.vars, v /= nil]    &
    //                [set_var(v, cls_ext_par(i)) : v, i <- ext_vs] &
    //                gen_fn_body(cls.body);
    //    code     := [cls_scope(cls.name, length(cls.vars), ext_vs, cls_body, code)];
    //  ;
    //  return code;
    //};


    // fn_call(name: FnSymbol, params: [ExtExpr*], named_params: (<named_par(Atom)> => ExtExpr)), //## NEW BAD BAD
    //fn_call() = make_scopes(rand_sort_pairs(expr.named_params), expr), //## BAD BAD BAD
    //{
    //  pars_info := gen_eval_info(expr.params);
    //  call_code := [call_proc(res_var, expr.name, pars_info.exprs)];
    //  code := pars_info.eval_code & call_code & pars_info.cleanup_code;
    //  if (expr.named_params /= ())
    //    //## BUG BUG BUG. THE ASSIGNMENTS ARE DONE IN RANDOM ORDER. FIX THIS
    //    nps := rand_sort_pairs(expr.named_params);
    //    code := make_scopes(nps, code);
    //  ;
    //  return code;
    //},

  //## THIS FUNCTION IS IN A REALLY BAD POSITION, SHOULD BE CLOSE TO THE gen_code CASE FOR fn_call(). ALSO, IT COULD HAVE A BETTER NAME
  [Instr+] make_scopes([[<named_par(Atom)>, ExtExpr]*] asgnms, body_gen_info) //[Instr+] body_code)
  {
    // THIS IS SUPER SUPER BAD BAD BAD
    if (asgnms == [])
      if (body_gen_info.expr?)
        expr := body_gen_info.expr;
        res_var := body_gen_info.res_var;
        pars_info := gen_eval_info(expr.params);
        call_code := [call_proc(res_var, expr.name, pars_info.exprs)];
        return pars_info.eval_code & call_code & pars_info.cleanup_code;
      else
        return gen_code(body_gen_info.body, body_gen_info.res_var, body_gen_info.all_rel_vars, body_gen_info.break_vars, body_gen_info.surv_vars); //## NOT SURE ABOUT THIS ONE
      ;
    ;


    var  := left(asgnms[0]);
    expr := right(asgnms[0]);
    
    rem_asgnms := subseq(asgnms, 1, length(asgnms)-1);
    
    if (expr :: Expr)
      info := gen_eval_info(expr);
      body := make_scopes(rem_asgnms, body_gen_info; next_obj_var_id = info.next_var_id);
      return info.eval_code & [var_scope(var, info.expr, body)] & info.cleanup_code;

    else
      //name     := :fn_symbol(untag(var));
      arity    := length(expr.params);
      loc_vs   := set([v : v <- expr.params, v /= nil] & [:fn_par(i) : i <- indexes(expr.params)]); //## BAD
      ext_vs   := rand_sort(extern_vars(expr.expr) - loc_vs);
      cls_body := [set_var(v, fn_par(i)) : v, i <- expr.params, v /= nil] &
                  [set_var(v, cls_ext_par(i)) : v, i <- ext_vs]           &
                  gen_fn_body(expr.expr);
      body     := make_scopes(rem_asgnms, body_gen_info);
      return [cls_scope(var, arity, ext_vs, cls_body, body)];
      //return [add_ref(v) : v <- ext_vs] & [cls_scope(var, arity, ext_vs, cls_body, body)] & [release(v) : v <- ext_vs];
    ;
  }


  [Instr*] gen_code([Statement*] stmts, ObjVar res_var) = gen_code(stmts, res_var, {}, {}, {});


  // all_rel_vars:  Vars that have been defined in an upper scope and that have to
  //                be released before assigning them or issuing a return statement
  //
  // break_vars:    Vars that have been defined in an upper scope and that have to be
  //                released before issuing a break statement. It is a subset of all_rel_vars
  //
  // surv_vars:     Vars that are defined in the current scope, but that survive to it.
  //                Disjoint from both all_rel_vars and break_vars
  
  [Instr*] gen_code([Statement*] stmts, ObjVar res_var, ObjVar* all_rel_vars, ObjVar* break_vars, ObjVar* surv_vars)
  {
    assert subset(break_vars, all_rel_vars);
    assert not in(res_var, all_rel_vars); //## THINK ABOUT THIS ONE
    assert disjoint(all_rel_vars, surv_vars);
    
    vs   := {};
    code := [];
    for (s : stmts)
      code := code & gen_code(s, res_var, all_rel_vars & vs, break_vars & vs);
      vs   := vs & (new_vars(s) - all_rel_vars); //## BUG? BUG? BUG?
    ;
    
    if (can_fall_through(stmts))
      code := code & [release(v) : v <- rand_sort(vs - surv_vars)];
    //## Try to reenable it if there are memory leaks
    //## else
    //##   code := code & [terminate];
    ;
    
    return code;
  }

  // all_rel_vars:  Vars that are in scope and that were defined in the current procedural expression.
  //                They have to be released before a return statement, or before being reassigned.
  //
  // break_vars:    Vars that have to be released before a break statement. It's a subset of all_rel_vars
  
  [Instr+] gen_code(Statement stmt, ObjVar res_var, ObjVar* all_rel_vars, ObjVar* break_vars):

    :break_stmt     = [release(v) : v <- rand_sort(break_vars)] & [break_loop],

    :fail_stmt      = [terminate],

    loop_stmt(ss)   = [repeat(gen_code(ss, res_var, all_rel_vars, {}, {}))],

    assert_stmt(e)  = { info := gen_eval_info(e);
                        return info.eval_code & [check(is_true(info.expr))];
                      },

    print_stmt(e)   = { info := gen_eval_info(e);
                        return info.eval_code & [print_obj(info.expr)] & info.cleanup_code;
                      },

    return_stmt(e)  = { assert not in(res_var, all_rel_vars);
                        
                        return gen_eval_code(e, res_var)               &
                               [release(v) : v <- rand_sort(all_rel_vars)] &
                               [exit_block];
                      },

    // let_stmt(asgnms: (<var(Atom)> => ExtExpr), body: [Statement+]), //## NEW BAD BAD
    //## BUG BUG BUG. THE ASSIGNMENTS ARE DONE IN RANDOM ORDER. FIX THIS
    let_stmt() =
    {
      //## THIS SHOULD BE CHECKED IN THE PROPER PLACE, BOTH IN LAYER 1 AND 2
      //## IT'S A TEMPORARY LIMITATION THAT SHOULD BE REMOVED
      assert not flow_control_can_jump_out(stmt.body);
      
      surv_vars := new_vars(stmt.body) - all_rel_vars;
      return make_scopes(rand_sort_pairs(stmt.asgnms), (body: stmt.body, res_var: res_var, all_rel_vars: all_rel_vars, break_vars: break_vars, surv_vars: surv_vars));

      //body := gen_code(stmt.body, res_var, all_rel_vars, break_vars, surv_vars); //## NOT SURE ABOUT THIS ONE
      //return make_scopes(rand_sort_pairs(stmt.asgnms), body);
    },

    assignment_stmt() =
    {
      if (in(stmt.var, all_rel_vars))
        if (in(stmt.var, extern_vars(stmt.value)))
          tmp_var := lvar(next_obj_var_id);
          code    := gen_eval_code(stmt.value, tmp_var; next_obj_var_id = next_obj_var_id + 1) &
                     [release(stmt.var), set_var(stmt.var, tmp_var)];
        else
          code := [release(stmt.var)] & gen_eval_code(stmt.value, stmt.var);
        ;
      else
        code := gen_eval_code(stmt.value, stmt.var);
      ;
      return code;
    },

    if_stmt() =
    {
      cond_info := gen_eval_info(stmt.cond);
      
      surv_vars := new_vars(stmt) - all_rel_vars;
      
      // The variable used to store the value of the condition is not
      // needed anymore here, so there's no need to update next_obj_var_id
      if_code   := gen_code(stmt.body, res_var, all_rel_vars, break_vars, surv_vars);
      else_code := gen_code(stmt.else, res_var, all_rel_vars, break_vars, surv_vars);
      
      branch_code := [ check(is_bool(cond_info.expr)),
                       branch(is_true(cond_info.expr), if_code, else_code)
                     ];
      
      return cond_info.eval_code & branch_code;
    },


    for_stmt() =
    {
      tmp_var   := lvar(next_obj_var_id);
      start_var := ivar(next_int_var_id);
      end_var   := ivar(next_int_var_id + 1);
      idx_var   := ivar(next_int_var_id + 2);
      
      let (next_obj_var_id = next_obj_var_id + 1)
        start_eval_code := gen_eval_code(stmt.start_val, tmp_var);
        end_eval_code   := gen_eval_code(stmt.end_val, tmp_var);
        
        body_code := gen_code(stmt.body, res_var, all_rel_vars, {}, {}; next_int_var_id = next_int_var_id + 3);
      ;
      
      return start_eval_code & [set_ivar(idx_var, get_int_val(tmp_var))] &
             end_eval_code   & [set_ivar(end_var, get_int_val(tmp_var))] &
             [ repeat(
                 [ break_if(is_gt(idx_var, end_var)),
                   set_var(stmt.var, to_obj(idx_var))
                 ] & body_code &
                 [increment(idx_var)]
               )
             ];
    },

    
    foreach_stmt() =
    {
      src_var := lvar(next_obj_var_id);
      idx_var := ivar(next_int_var_id);
      it_var  := seq_it_var(next_seq_it_var_id);
      
      has_idx_var := stmt.idx_var?;
      
      src_info := gen_eval_info(stmt.values, src_var; next_obj_var_id = next_obj_var_id + 1);
      
      body_code := gen_code(
                     stmt.body,
                     res_var,
                     all_rel_vars & {src_var if src_info.var_used},
                     {},
                     {};
                     next_obj_var_id    = next_obj_var_id + if src_info.var_used then 1 else 0 end,
                     next_int_var_id    = next_int_var_id + if has_idx_var then 1 else 0 end,
                     next_seq_it_var_id = next_seq_it_var_id + 1
                   );

      loop_code := [ get_iter(it_var, src_info.expr),
                     if stmt.idx_var? then set_ivar(idx_var, 0) else no_op end,
                     repeat(
                       [ break_if(is_out_of_range(it_var)),
                         set_var(stmt.var, get_curr_obj(it_var)),
                         if stmt.idx_var? then set_var(stmt.idx_var, to_obj(idx_var)) else no_op end
                       ] & body_code &
                       [ move_forward(it_var),
                         if stmt.idx_var? then increment(idx_var) else no_op end
                       ]
                     )
                   ];
      
      return src_info.eval_code & loop_code & src_info.cleanup_code;
    };
}

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

// select_expr(expr: Expr, ptrn: Pattern, src_expr: Expr, cond: Expr?),
// replace_expr(expr: Expr, src_expr: Expr, ptrn: Pattern);

// fn_call(name: FnSymbol, params: [ExtExpr*], named_params: (<var(Atom)> => ExtExpr)), //## NEW BAD BAD

// type ClsExpr  = cls_expr(params: [<var(Atom)>+], expr: Expr);

Expr simplify(Expr expr)
{
  return make(expr);
  
  Expr make(Expr expr):
    select_expr()   = make(
                       :select_expr_fn,
                       expr.src_expr,
                       expr.ptrn,
                       if expr.cond? then expr.cond else obj_true end,
                       expr.expr
                     ),

    replace_expr()  = make(
                       :replace_expr_fn,
                       expr.src_expr,
                       expr.ptrn,
                       obj_true,
                       expr.expr
                     );

  Expr make(Atom fn_name, Expr src_expr, Pattern ptrn, Expr sel_expr, Expr expr)
  {
    cond_expr := match_expr(
                   exprs: [fn_par(0)],
                   cases: [
                     (ptrns: [ptrn],                  expr: sel_expr),
                     (ptrns: [:type_ptrn(:type_any)], expr: obj_false)
                   ]
                 );

    cond_cls  := cls_expr(params: [nil], expr: cond_expr);  //## FIX THIS
    
    eval_expr := match_expr(
                   exprs: [fn_par(0)],
                   cases: [(ptrns: [ptrn], expr: expr)]
                 );

    eval_cls  := cls_expr(params: [nil], expr: eval_expr);  //## FIX THIS
    
    nps := (:named_par(:condition) => cond_cls, :named_par(:eval) => eval_cls);
    
    return fn_call(name: :fn_symbol(fn_name), params: [src_expr], named_params: nps);
  }
}

