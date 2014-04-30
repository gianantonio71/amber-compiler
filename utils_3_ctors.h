ObjVar lvar(Nat n)                  = :lvar(n);
ObjVar evar(Nat n, <Nat, IntVar> i) = evar(id: n, idx: i);

VecVar vvar(Nat n, NzNat s) = vvar(id: n, size: s);

BoolVar bvar(Nat n) = :bvar(n);
IntVar  ivar(Nat n) = :ivar(n);

StreamVar svar(Nat n) = :svar(n);

SetItVar set_it_var(Nat n) = :set_it_var(n);
SeqItVar seq_it_var(Nat n) = :seq_it_var(n);
MapItVar map_it_var(Nat n) = :map_it_var(n);

BoolFnName memb_test(TypeSymbol ts) = :memb_test(ts);

AtomicExpr empty_set = :empty_set;
AtomicExpr empty_seq = :empty_seq;
AtomicExpr empty_map = :empty_map;

NatBoolOp is_symb(ObjExpr e)                   = :is_symb(e);
NatBoolOp is_int(ObjExpr e)                    = :is_int(e);
NatBoolOp is_ne_set(ObjExpr e)                 = :is_ne_set(e);
NatBoolOp is_ne_seq(ObjExpr e)                 = :is_ne_seq(e);
NatBoolOp is_ne_map(ObjExpr e)                 = :is_ne_map(e);
NatBoolOp is_tagged_obj(ObjExpr e)             = :is_tagged_obj(e);
NatBoolOp is_eq(BoolExpr e1, BoolExpr e2)      = is_eq_bool(expr1: e1, expr2: e2);
NatBoolOp is_eq(IntExpr e1, IntExpr e2)        = is_eq_int(expr1: e1, expr2: e2);
NatBoolOp is_eq(ObjExpr e1, ObjExpr e2)        = is_eq(expr1: e1, expr2: e2);
NatBoolOp is_gt(IntExpr e1, IntExpr e2)        = is_gt(expr1: e1, expr2: e2);
NatBoolOp is_ge(IntExpr e1, IntExpr e2)        = is_ge(expr1: e1, expr2: e2);
NatBoolOp is_lt(IntExpr e1, IntExpr e2)        = is_lt(expr1: e1, expr2: e2);
NatBoolOp is_le(IntExpr e1, IntExpr e2)        = is_le(expr1: e1, expr2: e2);
NatBoolOp is_out_of_range(ItVar v)             = :is_out_of_range(v);

NatIntOp get_int_val(ObjExpr e)       = :get_int_val(e);
NatIntOp get_set_size(ObjExpr e)      = :get_set_size(e);
NatIntOp get_seq_len(ObjExpr e)       = :get_seq_len(e);
NatIntOp get_map_size(ObjExpr e)      = :get_map_size(e);
NatIntOp minus(IntExpr e)             = :minus(e);
NatIntOp add(IntExpr e1, IntExpr e2)  = add(val1: e1, val2: e2);
NatIntOp mult(IntExpr e1, IntExpr e2) = mult(val1: e1, val2: e2);
NatIntOp idiv(IntExpr e1, IntExpr e2) = idiv(val1: e1, val2: e2);
NatIntOp unique_int                   = :unique_int;

//NatObjOp at(ObjExpr s, ObjExpr i)              = at(seq: s, idx: i);
NatObjOp get_tag(ObjExpr e)                    = :get_tag(e);
NatObjOp get_inner_obj(ObjExpr e)              = :get_inner_obj(e);
NatObjOp to_obj(<BoolExpr, IntExpr> e)         = :to_obj(e);
NatObjOp to_str(ObjExpr e)                     = :to_str(e);
NatObjOp to_symb(ObjExpr e)                    = :to_symb(e);
NatObjOp get_curr_obj(<SetItVar, SeqItVar> it) = :get_curr_obj(it);
NatObjOp get_curr_key(MapItVar it)             = :get_curr_key(it);
NatObjOp get_curr_value(MapItVar it)           = :get_curr_value(it);

BoolExpr neg(BoolExpr e)                           = :neg(e);
BoolExpr and([BoolExpr+] es)                       = :and(es);
BoolExpr or([BoolExpr+] es)                        = :or(es);
BoolExpr and_then([BoolExpr+] es)                  = :and_then(es);
BoolExpr or_else([BoolExpr+] es)                   = :or_else(es);
BoolExpr eval_bool_fn(BoolFnName n, [AnyExpr+] ps) = eval_bool_fn(name: n, params: ps);

// Basic instructions

Instr init_stream(StreamVar v)       = :init_stream(v);
Instr append(StreamVar v, ObjExpr e) = append(stream: v, obj: e);

Instr mk_set_from_stream(ObjVar v, StreamVar s) = mk_set_from_stream(var: v, stream: s);
Instr mk_set(ObjVar v, VecVar es, IntExpr s)    = mk_set(var: v, elems: es, size: s);

Instr mk_seq_from_stream(ObjVar v, StreamVar s) = mk_seq_from_stream(var: v, stream: s);
Instr mk_seq(ObjVar v, VecVar es, IntExpr s)    = mk_seq(var: v, elems: es, size: s);

Instr mk_map_from_streams(ObjVar v, StreamVar ks, StreamVar vs) = mk_map_from_streams(var: v, key_stream: ks, value_stream: vs);
Instr mk_map(ObjVar v, VecVar ks, VecVar vs, IntExpr s)         = mk_map(var: v, keys: ks, values: vs, size: s);

Instr mk_tagged_obj(ObjVar v, ObjExpr t, ObjExpr o) = mk_tagged_obj(var: v, tag: t, obj: o);

Instr mk_array(ObjVar v, IntExpr s, ObjExpr d)                 = mk_array(var: v, size: s, value: d);
Instr get_seq_slice(ObjVar v, ObjExpr s, IntExpr f, IntExpr l) = get_seq_slice(var: v, seq: s, idx_first: f, len: l);
Instr join_seqs(ObjVar v, ObjExpr l, ObjExpr r)                = join_seqs(var: v, left: l, right: r);
Instr rev_seq(ObjVar v, ObjExpr s)                             = rev_seq(var: v, seq: s);
Instr get_at(ObjVar v, ObjExpr s, IntExpr i)                   = get_at(var: v, seq: s, idx: i);
Instr set_at(ObjVar v, IntExpr i, ObjExpr x)                   = set_at(var: v, idx: i, value: x);

Instr lookup(BoolVar sv, ObjVar v, ObjExpr m, ObjExpr k)     = lookup(success_var: sv, var: v, map: m, key: k);
Instr lookup(ObjVar v, ObjExpr m, ObjExpr k)                 = lookup(var: v, map: m, key: k);
Instr ext_lookup(BoolVar sv, ObjVar v, ObjExpr m, ObjExpr k) = ext_lookup(success_var: sv, var: v, map: m, key: k);
Instr ext_lookup(ObjVar v, ObjExpr m, ObjExpr k)             = ext_lookup(var: v, map: m, key: k);
Instr merge_maps(ObjVar v, ObjExpr m1, ObjExpr m2)           = merge_maps(var: v, map1: m1, map2: m2);

Instr seq_to_set(ObjVar v, ObjExpr s)    = seq_to_set(var: v, seq: s);
Instr seq_to_mset(ObjVar v, ObjExpr s)   = seq_to_mset(var: v, seq: s);
Instr list_to_seq(ObjVar v, ObjExpr l)   = list_to_seq(var: v, list: l);
Instr internal_sort(ObjVar v, ObjExpr s) = internal_sort(var: v, set: s);

Instr get_iter(SetItVar v, ObjExpr s) = get_set_iter(var: v, src: s);
Instr get_iter(SeqItVar v, ObjExpr s) = get_seq_iter(var: v, src: s);
Instr get_iter(MapItVar v, ObjExpr m) = get_map_iter(var: v, src: m);

Instr move_forward(ItVar v) = :move_forward(v);

Instr set_var(ObjVar v, ObjExpr e)    = set_var(var: v, value: e);
Instr set_bvar(BoolVar v, BoolExpr e) = set_bvar(var: v, value: e);
Instr set_ivar(IntVar v, IntExpr e)   = set_ivar(var: v, value: e);

Instr terminate = :terminate;

Instr add_ref(ObjVar v) = :add_ref(v);
Instr release(ObjVar v) = :release(v);

Instr print_obj(ObjExpr x) = print_obj(obj: x);

Instr ret_val(<ObjExpr, BoolExpr> e) = :ret_val(e);

Instr no_op = :no_op;

Instr branch(BoolExpr c, [Instr*] t, [Instr*] f) =
  if t /= [] or f == []
    then branch(cond: c, when_true: t, when_false: f)
    else branch(cond: neg(c), when_true: f, when_false: t)
  end;

//Instr symbol_switch() = symbol_switch(val: ObjExpr, cases: (vals: SymbObj+, instrs: [Instr*])*, else: [Instr+]?);

Instr repeat([Instr+] b) = :repeat(b);
Instr break_loop         = :break_loop;

Instr execute_block([Instr+] b) = :execute_block(b);
Instr exit_block                = :exit_block;

Instr call_proc(ObjVar v, ObjFnName n, [ObjExpr*] ps) = call_proc(var: v, name: n, params: ps);
Instr call_cls(ObjVar v, Var cv, [ObjExpr*] ps)  = call_cls(var: v, cls_var: cv, params: ps);

Instr var_scope(<named_par(Atom)> var, AtomicExpr value, [Instr+] body) = var_scope(var: var, new_value: value, body: body);
Instr cls_scope(<named_par(Atom)> v, [Var*] e, ClsDef c, [Instr+] b) = cls_scope(var: v, env: e, cls: c, body: b);

//////////////////// //////////////////// ////////////////////

ObjProcDef obj_proc_def(ObjFnName name, Nat arity, (<named_par(Atom)> => Nat) nps, [Instr+] body) =
  obj_proc_def(
    name:         name,
    in_arity:     arity,
    named_params: nps,
    body:         body
  );

BoolProcDef bool_proc_def(BoolFnName name, NzNat arity, [Instr+] body) =
  bool_proc_def(
    name:  name,
    arity: arity,
    body:  body
  );

//////////////////// Derived expressions  ////////////////////

BoolExpr and(BoolExpr e1, BoolExpr e2)      = and([e1, e2]);
BoolExpr or(BoolExpr e1, BoolExpr e2)       = or([e1, e2]);
BoolExpr and_then(BoolExpr e1, BoolExpr e2) = and_then([e1, e2]);
BoolExpr or_else(BoolExpr e1, BoolExpr e2)  = or_else([e1, e2]);

BoolExpr and(BoolExpr e1, BoolExpr e2, BoolExpr e3)      = and([e1, e2, e3]);
BoolExpr or(BoolExpr e1, BoolExpr e2, BoolExpr e3)       = or([e1, e2, e3]);
BoolExpr and_then(BoolExpr e1, BoolExpr e2, BoolExpr e3) = and_then([e1, e2, e3]);
BoolExpr or_else(BoolExpr e1, BoolExpr e2, BoolExpr e3)  = or_else([e1, e2, e3]);

BoolExpr is_empty_set(ObjExpr e) = is_eq(e, empty_set);
BoolExpr is_empty_seq(ObjExpr e) = is_eq(e, empty_seq);
BoolExpr is_empty_map(ObjExpr e) = is_eq(e, empty_map);

BoolExpr is_between(IntExpr e, IntExpr l, IntExpr u) = and(is_ge(e, l), is_le(e, u));

Var    fn_par(Nat n)      = :fn_par(n);
ObjVar cls_ext_par(Nat n) = :cls_ext_par(n);

BoolExpr is_true(ObjExpr e)  = is_eq(e, obj_true);
BoolExpr is_false(ObjExpr e) = is_eq(e, obj_false);

BoolExpr is_bool(ObjExpr e)  = or(is_true(e), is_false(e));

SymbObj obj_true  = :object(true);
SymbObj obj_false = :object(false);

ObjExpr obj_nil   = :object(nil);

Instr cls_scope(<named_par(Atom)> var, Int arity, [Var*] env, [Instr+] cls_body, [Instr+] body)
{
  cls := cls_def(arity: arity, body: cls_body);
  return cls_scope(var, env, cls, body);
}

//////////////////// Derived instructions ////////////////////

Instr repeat_while(BoolExpr cond, [Instr+] body) = repeat([do_if_not(cond, break_loop)] & body);

Instr increment(IntVar v) = set_ivar(v, add(v, 1));

Instr do_if(BoolExpr cond, [Instr*] instrs)      = branch(cond, instrs, []);
Instr do_if_not(BoolExpr cond, [Instr*] instrs)  = branch(cond, [], instrs);

Instr do_if(BoolExpr cond, Instr instr)      = do_if(cond, [instr]);
Instr do_if_not(BoolExpr cond, Instr instr)  = do_if_not(cond, [instr]);

Instr do_if_in(ObjExpr val, SymbObj+ values, [Instr*] instrs) =
  symbol_switch(
    val:   val,
    cases: {(vals: values, instrs: instrs)}
  );

Instr do_if_not_in(ObjExpr val, SymbObj+ values, [Instr*] instrs) =
  symbol_switch(
    val:   val,
    cases: {(vals: values, instrs: [])},
    else:  instrs
  );

Instr break_if(BoolExpr cond)     = do_if(cond, break_loop);
Instr break_if_not(BoolExpr cond) = do_if_not(cond, break_loop);

Instr exit_block_if(BoolExpr cond)     = do_if(cond, exit_block);
Instr exit_block_if_not(BoolExpr cond) = do_if_not(cond, exit_block);

Instr ret_true  = ret_val(true);
Instr ret_false = ret_val(false);

Instr ret_true_if(BoolExpr cond)  = do_if(cond, ret_true);
Instr ret_false_if(BoolExpr cond) = do_if(cond, ret_false);

Instr ret_true_if_not(BoolExpr cond)  = do_if_not(cond, ret_true);
Instr ret_false_if_not(BoolExpr cond) = do_if_not(cond, ret_false);

Instr ret_false_if_not_in(ObjExpr val, SymbObj+ values) = do_if_not_in(val, values, [ret_false]);

Instr check(BoolExpr e) = do_if_not(e, terminate);

Instr check_is_bool(ObjExpr e) = check(is_bool(e));

Instr get_curr_obj(ObjVar v, <SetItVar, SeqItVar> it) = set_var(v, get_curr_obj(it));
Instr get_curr_key(ObjVar v, MapItVar it)             = set_var(v, get_curr_key(it));
Instr get_curr_value(ObjVar v, MapItVar it)           = set_var(v, get_curr_value(it));

Instr maybe_op(Instr instr, Bool cond) = if cond then instr else no_op end;

Instr block_success_if(BoolExpr c, BoolVar res_var)     = do_if(c, [set_bvar(res_var, true), exit_block]);
Instr block_failure_if(BoolExpr c, BoolVar res_var)     = do_if(c, [set_bvar(res_var, false), exit_block]);
Instr block_failure_if_not(BoolExpr c, BoolVar res_var) = block_failure_if(neg(c), res_var);



////## BAD BAD BAD. ALL THIS IS VERY, VERY, VERY BAD
//
//////////////////////////////////////////////////////////////////////////////////
//
//AtomicExpr literal(Obj obj):
//  Symbol      = obj,
//  int(Int)    = obj, //## BAD
//  empty_set   = obj, //## BAD
//  _           = :literal(obj);
//
//
////ObjFnName accessor_fn      = internal_fn(:accessor);
////ObjFnName accessor_test_fn = internal_fn(:accessor_test);
//
//////////////////////////////////////////////////////////////////////////////////
//                    
//NatBoolOp is_symb(ObjExpr e)   = :is_symb(e);
//NatBoolOp is_int(ObjExpr e)    = :is_int(e);
//NatBoolOp is_ne_set(ObjExpr e) = :is_ne_set(e);
//NatBoolOp is_term(ObjExpr e)   = :is_term(e);
//
//NatBoolOp is_eq(ObjExpr e1,  ObjExpr e2)  = is_eq(expr1: e1, expr2: e2);
//NatBoolOp is_eq(BoolExpr e1, BoolExpr e2) = is_eq_bool(expr1: e1, expr2: e2);
//NatBoolOp is_eq(IntExpr e1,  IntExpr e2)  = is_eq_int(expr1: e1, expr2: e2);
//
//NatBoolOp is_gt(IntExpr e1, IntExpr e2) = is_gt(expr1: e1, expr2: e2);
//NatBoolOp is_ge(IntExpr e1, IntExpr e2) = is_ge(expr1: e1, expr2: e2);
//NatBoolOp is_lt(IntExpr e1, IntExpr e2) = is_lt(expr1: e1, expr2: e2);
//NatBoolOp is_le(IntExpr e1, IntExpr e2) = is_le(expr1: e1, expr2: e2);
//
//NatBoolOp is_out_range(ItVar v) = :is_out_range(v); 
//
//////////////////////////////////////////////////////////////////////////////////
//
//NatBoolOp is_gt(ObjExpr e1, ObjExpr e2) = is_gt(expr1: get_int_val(e1), expr2: get_int_val(e2));
//NatBoolOp is_ge(ObjExpr e1, ObjExpr e2) = is_ge(expr1: get_int_val(e1), expr2: get_int_val(e2));
//NatBoolOp is_lt(ObjExpr e1, ObjExpr e2) = is_lt(expr1: get_int_val(e1), expr2: get_int_val(e2));
//NatBoolOp is_le(ObjExpr e1, ObjExpr e2) = is_le(expr1: get_int_val(e1), expr2: get_int_val(e2));
//
//////////////////////////////////////////////////////////////////////////////////
//
//NatBoolOp is_empty_set(ObjExpr v) = is_eq(v, :empty_set);
//BoolExpr  is_set(ObjExpr v)       = or(is_eq(v, :empty_set), is_ne_set(v));
//
//////////////////////////////////////////////////////////////////////////////////
//
//NatIntOp get_int_val(ObjExpr e)       = :get_int_val(e);
//NatIntOp get_set_size(ObjExpr e)      = :get_set_size(e);
//NatIntOp get_seq_len(ObjExpr e)       = :get_seq_len(e);
//NatIntOp minus(IntExpr e)             = :minus(e);
//NatIntOp add(IntExpr e1, IntExpr e2)  = add(val1: e1, val2: e2);
//NatIntOp mult(IntExpr e1, IntExpr e2) = add(val1: e1, val2: e2);
//NatIntOp unique_int                   = :unique_int;
//
//////////////////////////////////////////////////////////////////////////////////
//
//NatObjOp get_obj(ItVar v)                   = :get_obj(v);
//NatObjOp get_root(ObjExpr e)                = :get_root(e);
//NatObjOp accessor_test(ObjExpr e, Symbol l) = accessor_test(expr: e, label: l);
//NatObjOp to_str(ObjExpr e)                  = :to_str(e);
//NatObjOp to_symb(ObjExpr e)                 = :to_symb(e);
//NatObjOp to_obj(<BoolExpr, IntExpr> e)      = :to_obj(e);
//NatObjOp at(ObjExpr seq, ObjExpr idx)       = at(seq: seq, idx: idx);
//
//////////////////////////////////////////////////////////////////////////////////
//
//BoolExpr neg(BoolExpr e)                                  = :neg(e);
//BoolExpr eval_bool_fn(BoolFnName fn, [AnyExpr+] ps)       = eval_bool_fn(name: fn, params: ps);
//
//BoolExpr and(BoolExpr e1, BoolExpr e2)                    = :and([e1, e2]);
//BoolExpr and(BoolExpr e1, BoolExpr e2, BoolExpr e3)       = :and([e1, e2, e3]);
//
//BoolExpr or(BoolExpr e1, BoolExpr e2)                     = :or([e1, e2]);
//BoolExpr or(BoolExpr e1, BoolExpr e2, BoolExpr e3)        = :or([e1, e2, e3]);
//
//BoolExpr and_then(BoolExpr e1, BoolExpr e2)               = :and_then([e1, e2]);
//BoolExpr and_then(BoolExpr e1, BoolExpr e2, BoolExpr e3)  = :and_then([e1, e2, e3]);
//
//BoolExpr or_else(BoolExpr e1, BoolExpr e2)                = :or_else([e1, e2]);
//BoolExpr or_else(BoolExpr e1, BoolExpr e2, BoolExpr e3)   = :or_else([e1, e2, e3]);
//
//////////////////////////////////////////////////////////////////////////////////
//
//Instr init_stream(StreamVar v)            = :init_stream(v);
//Instr append(StreamVar v, ObjExpr obj)    = append(stream: v, obj: obj);
//Instr mk_checkpoint(StreamVar v)          = :mk_checkpoint(v);
//Instr commit(StreamVar v)                 = :commit(v);
//Instr rollback(StreamVar v)               = :rollback(v);
//Instr mk_set(ObjVar v, StreamVar psv)     = mk_set(var: v, stream: psv);
//
//Instr mk_set(ObjVar v, VecVar elems)      = mk_fixed_set(var: v, elems: elems);
//
//Instr mk_term(ObjVar var, ObjExpr root, ObjExpr subobjs) = mk_term(var: var, root: root, subobjs: subobjs);
//
//Instr mk_seq(ObjVar var, StreamVar stream)           = mk_seq_from_stream(var: var, stream: stream);
//Instr mk_seq(ObjVar var, VecVar elems)               = mk_seq(var: var, elems: elems);
//Instr mk_seq(ObjVar var, VecVar elems, ObjExpr tail) = mk_seq(var: var, elems: elems, tail: tail);
//
//Instr mk_array(ObjVar var, IntExpr size, ObjExpr value) = mk_array(var: var, size: size, value: value);
//Instr set_at(ObjVar var, IntExpr idx, ObjExpr value)  = set_at(var: var, idx: idx, value: value);
//
//Instr get_inner_set(ObjVar v, ObjExpr e) = get_inner_set(var: v, expr: e);
//
//Instr get_seq_slice(ObjVar var, ObjExpr seq, ObjExpr idx_first, ObjExpr len) =
//  get_seq_slice(
//    var: var,
//    seq: seq,
//    idx_first: idx_first,
//    len: len
//  );
//  
//Instr join_seqs(ObjVar var, ObjExpr left, ObjExpr right) = join_seqs(var: var, left: left, right: right);
//Instr rev_seq(ObjVar var, ObjExpr seq)                   = rev_seq(var: var, seq: seq);
//Instr seq_to_set(ObjVar var, ObjExpr seq)                = seq_to_set(var: var, seq: seq);
//
//Instr accessor(ObjVar v, ObjExpr e, Symbol l) = accessor(var: v, expr: e, label: l);
//
//Instr set_var(ObjVar v, ObjExpr e)      = set_var(var: v, value: e);
//Instr set_bvar(BoolVar v, BoolExpr e)   = set_bvar(var: v, value: e);
//Instr set_ivar(IntVar var, IntExpr val) = set_ivar(var: var, value: val);
//
//Instr ret_val(<ObjExpr, BoolExpr> e)    = :ret_val(e);
//
//Instr add_ref(ObjVar v) = :add_ref(v);
//Instr release(ObjVar v) = :release(v);
//
//Instr no_op                     = :no_op;
//
//Instr branch(BoolExpr cond, [Instr*] on_true, [Instr*] on_false) = if is_null(on_true) and is_null(on_false) then
//                                                                     no_op
//                                                                   else
//                                                                     branch(
//                                                                       cond:       cond,
//                                                                       when_true:  rem_no_ops(on_true) if not is_null(on_true),
//                                                                       when_false: rem_no_ops(on_false) if not is_null(on_false)
//                                                                     );
//                                                                   ;
//
////## SHOULD BE A LOCAL FUNCTION
//Bool is_null([Instr*] instrs) = rem_no_ops(instrs) = [];
//
//[Instr*] rem_no_ops([Instr*] instrs) = [instr : instr <- instrs, instr /= no_op];
//
//
//
//Instr symbol_switch(ObjExpr val, (vals: Symbol+, instrs: [Instr*])* cases, [Instr*] def_instrs) =
//  symbol_switch(
//    val:   val, 
//    cases: cases, 
//    else:  def_instrs if def_instrs /= []
//  );
//
//Instr repeat([Instr+] body)         = :repeat(body);
//Instr break_loop                    = :break_loop;
//
//Instr execute_block([Instr+] block) = :execute_block(block);
//Instr exit_block                    = :exit_block;
//
//Instr get_iter(ItVar v, ObjExpr e)  = get_iter(var: v, set: e);
//Instr move_forward(ItVar v)         = :move_forward(v);
//                    
//Instr call_proc([ObjVar+] vs, ObjFnName fn, [ObjExpr*] ps) = call_proc(vars: vs, name: fn, params: ps);
//Instr call_cls(ObjVar v, ObjFnName fn, [ObjExpr*] ps)      = call_cls(var: v, name: fn, params: ps);
//
//
//Instr cls_scope(FnSymbol name, [Var*] params, [Var*] env, [Instr+] cls_body, [Instr+] body)
//{
//  cls := cls_def(
//           name:   name,
//           arity:  length(params),
//           env:    env,
//           body:   cls_body
//         );
//
//  return cls_scope(cls: cls, body: body);
//}
//
//  //cls_scope(
//  //  name:     name,
//  //  params:   params,
//  //  env:      env,
//  //  cls_body: cls_body,
//  //  body:     body
//  //);
//
//Instr print_obj(ObjExpr e) = print_obj(obj: e);
//
//Instr terminate = :terminate;
//
//////////////////////////////////////////////////////////////////////////////////
//
//ObjProcDef obj_proc_def(ObjFnName name, Nat arity, [Instr+] body) = obj_proc_def(
//                                                                      name:       name,
//                                                                      in_arity:   arity,
//                                                                      out_arity:  1,
//                                                                      body:       body
//                                                                    );
//
//BoolProcDef bool_proc_def(BoolFnName name, NzNat arity, [Instr+] body) = bool_proc_def(
//                                                                           name:  name,
//                                                                           arity: arity,
//                                                                           body:  body
//                                                                         );
//
//////////////////////////////////////////////////////////////////////////////////
//
//Instr repeat_while(BoolExpr cond, [Instr+] body) = repeat([do_if_not(cond, break_loop)] & body);
//
//Instr increment(IntVar v) = set_ivar(v, add(v, 1));
//
//Instr do_if(BoolExpr cond, [Instr*] instrs)      = branch(cond, instrs, []);
//Instr do_if_not(BoolExpr cond, [Instr*] instrs)  = branch(cond, [], instrs);
//
//Instr do_if(BoolExpr cond, Instr instr)      = do_if(cond, [instr]);
//Instr do_if_not(BoolExpr cond, Instr instr)  = do_if_not(cond, [instr]);
//
//Instr do_if_in(ObjExpr val, Symbol+ values, [Instr*] instrs) =
//  symbol_switch(
//    val:   val,
//    cases: {(vals: values, instrs: instrs)}
//  );
//
//Instr do_if_not_in(ObjExpr val, Symbol+ values, [Instr*] instrs) =
//  symbol_switch(
//    val:   val,
//    cases: {(vals: values, instrs: [])},
//    else:  instrs
//  );
//
//Instr break_if(BoolExpr cond)     = do_if(cond, break_loop);
//Instr break_if_not(BoolExpr cond) = do_if_not(cond, break_loop);
//
//Instr exit_block_if(BoolExpr cond)     = do_if(cond, exit_block);
//Instr exit_block_if_not(BoolExpr cond) = do_if_not(cond, exit_block);
//
//Instr ret_true  = ret_val(true);
//Instr ret_false = ret_val(false);
//
//Instr ret_true_if(BoolExpr cond)  = do_if(cond, ret_true);
//Instr ret_false_if(BoolExpr cond) = do_if(cond, ret_false);
//
//Instr ret_true_if_not(BoolExpr cond)  = do_if_not(cond, ret_true);
//Instr ret_false_if_not(BoolExpr cond) = do_if_not(cond, ret_false);
//
//Instr ret_false_if_not_in(ObjExpr val, Symbol+ values) = do_if_not_in(val, values, [ret_false]);
//
//Instr check(BoolExpr e) = do_if_not(e, terminate);
//
//////////////////////////////////////////////////////////////////////////////////
//
//BoolExpr is_symb(ItVar v)      = and_then(neg(is_out_range(v)), is_symb(get_obj(v)));
//BoolExpr is_int(ItVar v)       = and_then(neg(is_out_range(v)), is_int(get_obj(v)));
//BoolExpr is_empty_set(ItVar v) = and_then(neg(is_out_range(v)), is_empty_set(get_obj(v)));
//BoolExpr is_ne_set(ItVar v)    = and_then(neg(is_out_range(v)), is_ne_set(get_obj(v)));
//BoolExpr is_term(ItVar v)      = and_then(neg(is_out_range(v)), is_term(get_obj(v)));
//
//ObjExpr bool2obj(Bool b) = if b then :symbol(true) else :symbol(false) end;
//
//ObjExpr obj_true  = :symbol(true);
//ObjExpr obj_false = :symbol(false);
//
//////////////////////////////////////////////////////////////////////////////////
//
//BoolExpr is_true(ObjExpr e)  = is_eq(e, :symbol(true));
//BoolExpr is_false(ObjExpr e) = is_eq(e, :symbol(false));
//
//BoolExpr is_bool(ObjExpr e)  = or(is_true(e), is_false(e));
//
//////////////////////////////////////////////////////////////////////////////////
//
//ObjVar  new_lvar = :lvar(_counter_(nil));
//BoolVar new_bvar = :bvar(_counter_(nil));
//IntVar  new_ivar = :ivar(_counter_(nil));
//
//VecVar new_vvar(NzNat size)          = vvar(id: _counter_(nil), size: size);
//ObjVar get_evar(VecVar var, Nat idx) = evar(id: var.id, idx: idx);
//
//SetItVar new_set_itvar = :set_it_var(_counter_(nil));
//SeqItVar new_seq_itvar = :seq_it_var(_counter_(nil));
//
//StreamVar new_strm_var = :svar(_counter_(nil));
