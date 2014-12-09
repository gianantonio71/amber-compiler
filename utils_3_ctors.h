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

NatBoolOp is_symb(ObjExpr e)                    = :is_symb(e);
NatBoolOp is_int(ObjExpr e)                     = :is_int(e);
NatBoolOp is_ne_set(ObjExpr e)                  = :is_ne_set(e);
NatBoolOp is_ne_seq(ObjExpr e)                  = :is_ne_seq(e);
NatBoolOp is_ne_map(ObjExpr e)                  = :is_ne_map(e);
NatBoolOp is_tagged_obj(ObjExpr e)              = :is_tagged_obj(e);
NatBoolOp has_elem(ObjExpr s, ObjExpr e)        = has_elem(set: s, elem: e);
NatBoolOp is_eq(BoolExpr e1, BoolExpr e2)       = is_eq_bool(expr1: e1, expr2: e2);
NatBoolOp is_eq(IntExpr e1, IntExpr e2)         = is_eq_int(expr1: e1, expr2: e2);
// NatBoolOp is_eq(ObjExpr e1, ObjExpr e2)         = is_eq(expr1: e1, expr2: e2);
NatBoolOp is_gt(IntExpr e1, IntExpr e2)         = is_gt(expr1: e1, expr2: e2);
NatBoolOp is_ge(IntExpr e1, IntExpr e2)         = is_ge(expr1: e1, expr2: e2);
NatBoolOp is_lt(IntExpr e1, IntExpr e2)         = is_lt(expr1: e1, expr2: e2);
NatBoolOp is_le(IntExpr e1, IntExpr e2)         = is_le(expr1: e1, expr2: e2);
NatBoolOp inline_is_eq(ObjExpr e, InlineObj v)  = inline_is_eq(expr: e, value: v);
NatBoolOp is_out_of_range(ItVar v)              = :is_out_of_range(v);

BoolExpr is_eq(ObjExpr e1, ObjExpr e2):
  InlineObj,  InlineObj   = e1 == e2,
  _,          InlineObj   = inline_is_eq(e1, e2),
  InlineObj,  _           = inline_is_eq(e2, e1),
  _,          _           = is_eq(expr1: e1, expr2: e2);

NatIntOp get_int_val(ObjExpr e)         = :get_int_val(e);
NatIntOp get_set_size(ObjExpr e)        = :get_set_size(e);
NatIntOp get_seq_len(ObjExpr e)         = :get_seq_len(e);
NatIntOp get_map_size(ObjExpr e)        = :get_map_size(e);
NatIntOp minus(IntExpr e)               = :minus(e);
NatIntOp add(IntExpr e1, IntExpr e2)    = add(val1: e1, val2: e2);
NatIntOp sub(IntExpr e1, IntExpr e2)    = sub(val1: e1, val2: e2);
NatIntOp mult(IntExpr e1, IntExpr e2)   = mult(val1: e1, val2: e2);
NatIntOp div(IntExpr e1, IntExpr e2)    = div(val1: e1, val2: e2);
NatIntOp mod_op(IntExpr e1, IntExpr e2) = mod(val1: e1, val2: e2); //## THIS SHOULD JUST BE NAMED mod, BUT THAT WOULD CONFLICT WITH THE INTEGER MOD OPERATION
NatIntOp unique_nat                     = :unique_nat;
NatIntOp rand_nat(ObjExpr e)            = :rand_nat(get_int_val(e));
NatIntOp ticks                          = :ticks;

NatObjOp at(ObjExpr s, IntExpr i)              = at(seq: s, idx: i);
NatObjOp get_tag(ObjExpr e)                    = :get_tag(e);
NatObjOp get_inner_obj(ObjExpr e)              = :get_inner_obj(e);
NatObjOp to_obj(<BoolExpr, IntExpr> e)         = :to_obj(e);
NatObjOp obj_neg(ObjExpr e)                    = :obj_neg(e);
NatObjOp to_str(ObjExpr e)                     = :to_str(e);
NatObjOp to_symb(ObjExpr e)                    = :to_symb(e);
NatObjOp get_curr_obj(<SetItVar, SeqItVar> it) = :get_curr_obj(it);
NatObjOp get_curr_key(MapItVar it)             = :get_curr_key(it);
NatObjOp get_curr_value(MapItVar it)           = :get_curr_value(it);
NatObjOp rand_elem(ObjExpr s)                  = :rand_elem(s);

BoolExpr neg(BoolExpr e)                           = :neg(e);
BoolExpr and([BoolExpr^] es)                       = :and(es);
BoolExpr or([BoolExpr^] es)                        = :or(es);
BoolExpr and_then([BoolExpr^] es)                  = :and_then(es);
BoolExpr or_else([BoolExpr^] es)                   = :or_else(es);
BoolExpr eval_bool_fn(BoolFnName n, [AnyExpr^] ps) = eval_bool_fn(name: n, params: ps);

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
Instr join_mult_seqs(ObjVar v, ObjExpr ss)                     = join_mult_seqs(var: v, seqs: ss);
Instr rev_seq(ObjVar v, ObjExpr s)                             = rev_seq(var: v, seq: s);
// Instr get_at(ObjVar v, ObjExpr s, IntExpr i)                   = get_at(var: v, seq: s, idx: i);
Instr set_at(ObjVar v, IntExpr i, ObjExpr x)                   = set_at(var: v, idx: i, value: x);

Instr lookup(BoolVar sv, ObjVar v, ObjExpr m, ObjExpr k)     = lookup(success_var: sv, var: v, map: m, key: k);
Instr lookup(ObjVar v, ObjExpr m, ObjExpr k)                 = lookup(var: v, map: m, key: k);
Instr ext_lookup(BoolVar sv, ObjVar v, ObjExpr m, ObjExpr k) = ext_lookup(success_var: sv, var: v, map: m, key: k);
Instr ext_lookup(ObjVar v, ObjExpr m, ObjExpr k)             = ext_lookup(var: v, map: m, key: k);

Instr merge_sets(ObjVar v, ObjExpr ss)  = merge_sets(var: v, sets: ss);
Instr merge_maps(ObjVar v, ObjExpr ms)  = merge_maps(var: v, maps: ms);

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

Instr branch(BoolExpr c, [Instr] t, [Instr] f) =
  if t /= [] or f == []
    then branch(cond: c, when_true: t, when_false: f)
    else branch(cond: neg(c), when_true: f, when_false: t)
  end;

//Instr symbol_switch() = symbol_switch(val: ObjExpr, cases: (vals: SymbObj+, instrs: [Instr])*, else: [Instr^]?);

Instr repeat([Instr^] b) = :repeat(b);
Instr break_loop         = :break_loop;

Instr execute_block([Instr^] b) = :execute_block(b);
Instr exit_block                = :exit_block;

Instr call_proc(ObjVar v, ObjFnName n, [<ObjExpr, BoundCls>] ps) = call_proc(var: v, name: n, params: ps);
Instr call_cls(ObjVar v, Var cv, [ObjExpr] ps)  = call_cls(var: v, cls_var: cv, params: ps);

Instr push_call_info(FnSymbol fn_name, [ObjVar] params) = push_call_info(fn_name: fn_name, params: params);
Instr pop_call_info = :pop_call_info;

Instr runtime_check(ObjExpr c) = runtime_check(cond: c);

Instr var_scope(<named_par(Atom)> var, AtomicExpr value, [Instr^] body) = var_scope(var: var, new_value: value, body: body);
Instr cls_scope(<named_par(Atom)> v, BoundCls c, [Instr^] b) = cls_scope(var: v, bound_cls: c, body: b);

//////////////////// //////////////////// ////////////////////

ClsDef   cls_def(NzNat a, [Instr^] b)   = cls_def(arity: a, body: b);

BoundCls bound_cls(ClsDef c, [Var] vs)  = bound_cls(cls: c, env: vs);

// ObjProcPar obj = :obj; //## DEFINING THIS WILL BREAK THE GENERATED CODE
ObjProcPar cls(ClsVar n, NzNat a) = cls(name: n, arity: a);
ObjProcPar cls(NzNat a) = cls(arity: a);

ObjProcDef obj_proc_def(ObjFnName name, [ObjProcPar] params, (<named_par(Atom)> => Nat) nps, [Instr^] body) =
  obj_proc_def(
    name:         name,
    params:       params,
    named_params: nps,
    body:         body
  );

BoolProcDef bool_proc_def(BoolFnName name, NzNat arity, [Instr^] body) =
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

ObjVar cls_ext_par(Nat n) = :cls_ext_par(n);

BoolExpr is_true(ObjExpr e)  = is_eq(e, obj_true);
BoolExpr is_false(ObjExpr e) = is_eq(e, obj_false);

BoolExpr is_bool(ObjExpr e)  = or(is_true(e), is_false(e));

SymbObj obj_true  = :object(true);
SymbObj obj_false = :object(false);

ObjExpr obj_nil   = :object(nil);

//////////////////// Derived instructions ////////////////////

Instr repeat_while(BoolExpr cond, [Instr^] body) = repeat([do_if_not(cond, break_loop)] & body);

Instr increment(IntVar v) = set_ivar(v, add(v, 1));

Instr do_if(BoolExpr cond, [Instr] instrs)      = branch(cond, instrs, []);
Instr do_if_not(BoolExpr cond, [Instr] instrs)  = branch(cond, [], instrs);

Instr do_if(BoolExpr cond, Instr instr)      = do_if(cond, [instr]);
Instr do_if_not(BoolExpr cond, Instr instr)  = do_if_not(cond, [instr]);

Instr do_if_in(ObjExpr val, SymbObj+ values, [Instr] instrs) =
  symbol_switch(
    val:   val,
    cases: {(vals: values, instrs: instrs)}
  );

Instr do_if_not_in(ObjExpr val, SymbObj+ values, [Instr] instrs) =
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
// Instr check(BoolExpr e) = no_op;

Instr check_is_bool(ObjExpr e) = check(is_bool(e));

Instr get_curr_obj(ObjVar v, <SetItVar, SeqItVar> it) = set_var(v, get_curr_obj(it));
Instr get_curr_key(ObjVar v, MapItVar it)             = set_var(v, get_curr_key(it));
Instr get_curr_value(ObjVar v, MapItVar it)           = set_var(v, get_curr_value(it));

Instr maybe_op(Instr instr, Bool cond) = if cond then instr else no_op end;

Instr block_success_if(BoolExpr c, BoolVar res_var)     = do_if(c, [set_bvar(res_var, true), exit_block]);
Instr block_failure_if(BoolExpr c, BoolVar res_var)     = do_if(c, [set_bvar(res_var, false), exit_block]);
Instr block_failure_if_not(BoolExpr c, BoolVar res_var) = block_failure_if(neg(c), res_var);
