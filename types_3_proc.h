type ObjVar       = Var,
                    cls_ext_par(Nat), //## RENAME THIS
                    lvar(Nat), //## THIS IS REDUNDANT, WE ALREADY HAVE unique_var(Nat)
                    evar(id: Nat, idx: <Nat, IntVar>);

type VecVar       = vvar(id: Nat, size: NzNat);

type BoolVar      = bvar(Nat);
type IntVar       = ivar(Nat);

type StreamVar    = svar(Nat); //## DOES THIS NEED CLEANUP?

type SetItVar     = set_it_var(Nat); //## MUST WORK WITHOUT THE NEED FOR EXPLICIT CLEANUP
type SeqItVar     = seq_it_var(Nat); //## MUST WORK WITHOUT THE NEED FOR EXPLICIT CLEANUP
type MapItVar     = map_it_var(Nat); //## MUST WORK WITHOUT THE NEED FOR EXPLICIT CLEANUP

type ItVar        = SetItVar, SeqItVar, MapItVar;

type AnyVar       = ObjVar, VecVar, BoolVar, IntVar, ItVar, StreamVar;

//## WHY NOT REMOVE ObjFnName ALTOGETHER AND USE FnSymbol DIRECTLY?
type ObjFnName    = FnSymbol;

type BoolFnName   = memb_test(TypeSymbol);

type InlineObj    = LeafObj, empty_set, empty_seq, empty_map;

type AtomicExpr   = InlineObj, ObjVar;

type NatBoolOp    = is_symb(ObjExpr),
                    is_int(ObjExpr),
                    is_float(ObjExpr),
                    is_ne_set(ObjExpr),
                    is_ne_seq(ObjExpr),
                    is_ne_map(ObjExpr),
                    is_tagged_obj(ObjExpr),
                    has_elem(set: ObjExpr, elem: ObjExpr),
                    //has_key(map: ObjExpr, key: ObjExpr),
                    //comes_before(expr1: ObjExpr, expr2: ObjExpr),
                    is_eq_bool(expr1: BoolExpr, expr2: BoolExpr),
                    is_eq_int(expr1: IntExpr, expr2: IntExpr),
                    is_eq(expr1: ObjExpr, expr2: ObjExpr),
                    is_gt(expr1: IntExpr, expr2: IntExpr),
                    is_ge(expr1: IntExpr, expr2: IntExpr),
                    is_lt(expr1: IntExpr, expr2: IntExpr),
                    is_le(expr1: IntExpr, expr2: IntExpr),
                    inline_is_eq(expr: ObjExpr, value: InlineObj),
                    is_out_of_range(ItVar);

type NatIntOp     = get_int_val(ObjExpr),
                    get_set_size(ObjExpr),
                    get_seq_len(ObjExpr),
                    get_map_size(ObjExpr),
                    minus(IntExpr),
                    add(val1: IntExpr, val2: IntExpr),
                    sub(val1: IntExpr, val2: IntExpr),
                    mult(val1: IntExpr, val2: IntExpr),
                    div(val1: IntExpr, val2: IntExpr),
                    mod(val1: IntExpr, val2: IntExpr),
                    mantissa(ObjExpr),
                    dec_exp(ObjExpr),
                    rand_nat(IntExpr),  // Non-deterministic
                    unique_nat,         // Non-deterministic
                    ticks;              // Impure

type NatObjOp     = at(seq: ObjExpr, idx: IntExpr),
                    //lookup(map: ObjExpr, key: ObjExpr),
                    get_tag(ObjExpr),
                    get_inner_obj(ObjExpr), //## RENAME?
                    
                    to_obj(<BoolExpr, IntExpr>),
                    obj_neg(ObjExpr),

                    to_str(ObjExpr), // For this to be a no-delete operation, the string must be cached
                    to_symb(ObjExpr),

                    get_curr_obj(<SetItVar, SeqItVar>),
                    get_curr_key(MapItVar),
                    get_curr_value(MapItVar),

                    rand_elem(ObjExpr); // Non-deterministic

type BoolExpr     = true,
                    false,
                    BoolVar,
                    NatBoolOp,
                    neg(BoolExpr),
                    and([BoolExpr^]), //## SEQUENCES OR SETS?
                    or([BoolExpr^]),  //## DITTO
                    and_then([BoolExpr^]),
                    or_else([BoolExpr^]),
                    eval_bool_fn(name: BoolFnName, params: [AnyExpr^]);

type IntExpr      = Int, IntVar, NatIntOp;                    

type ObjExpr      = AtomicExpr, NatObjOp;

type AnyExpr      = BoolExpr, IntExpr, ObjExpr;

type Instr        = init_stream(StreamVar),
                    append(stream: StreamVar, obj: ObjExpr),

                    mk_set_from_stream(var: ObjVar, stream: StreamVar),
                    mk_set(var: ObjVar, elems: VecVar, size: IntExpr),

                    mk_seq_from_stream(var: ObjVar, stream: StreamVar),
                    mk_seq(var: ObjVar, elems: VecVar, size: IntExpr),

                    mk_map_from_streams(var: ObjVar, key_stream: StreamVar, value_stream: StreamVar),
                    mk_map(var: ObjVar, keys: VecVar, values: VecVar, size: IntExpr),
                    
                    mk_tagged_obj(var: ObjVar, tag: ObjExpr, obj: ObjExpr),

                    mk_float(var: ObjVar, mantissa: Int, dec_exp: Int),

                    neg_float(var: ObjVar, value: ObjExpr),
                    add_floats(var: ObjVar, values: (ObjExpr, ObjExpr)),
                    sub_floats(var: ObjVar, values: (ObjExpr, ObjExpr)),
                    mult_floats(var: ObjVar, values: (ObjExpr, ObjExpr)),
                    div_floats(var: ObjVar, values: (ObjExpr, ObjExpr)),
                    square_root(var: ObjVar, value: ObjExpr),
                    floor_op(var: ObjVar, value: ObjExpr),
                    ceiling_op(var: ObjVar, value: ObjExpr),
                    int_to_float(var: ObjVar, value: ObjExpr),

                    mk_array(var: ObjVar, size: IntExpr, value: ObjExpr),
                    get_seq_slice(var: ObjVar, seq: ObjExpr, idx_first: IntExpr, len: IntExpr),
                    // <seq> and <new_elem> must already be reference-counted
                    append_to_seq(var: ObjVar, seq: ObjExpr, new_elem: ObjExpr),
                    join_seqs(var: ObjVar, left: ObjExpr, right: ObjExpr),
                    join_mult_seqs(var: ObjVar, seqs: ObjExpr),
                    rev_seq(var: ObjVar, seq: ObjExpr),
                    // get_at(var: ObjVar, seq: ObjExpr, idx: IntExpr),
                    //## BUG BUG BUG: IF ObjExpr CONTAINS A NON-COUNTED REFERENCE TO THE ARRAY,
                    //## I COULD END UP WITH A CYCLE IN THE OBJECT GRAPH AND MAYBE OTHER PROBLEMS
                    set_at(var: ObjVar, idx: IntExpr, value: ObjExpr),

                    lookup(success_var: BoolVar?, var: ObjVar, map: ObjExpr, key: ObjExpr),
                    ext_lookup(success_var: BoolVar?, var: ObjVar, map: ObjExpr, key: ObjExpr),

                    merge_sets(var: ObjVar, sets: ObjExpr),
                    merge_maps(var: ObjVar, maps: ObjExpr),
                    
                    seq_to_set(var: ObjVar, seq: ObjExpr),
                    seq_to_mset(var: ObjVar, seq: ObjExpr),
                    list_to_seq(var: ObjVar, list: ObjExpr),
                    internal_sort(var: ObjVar, set: ObjExpr),
                    
                    get_set_iter(var: SetItVar, src: ObjExpr),
                    get_seq_iter(var: SeqItVar, src: ObjExpr),
                    get_map_iter(var: MapItVar, src: ObjExpr),
                    
                    move_forward(ItVar),
                    
                    set_var(var: ObjVar, value: ObjExpr),
                    set_bvar(var: BoolVar, value: BoolExpr),
                    set_ivar(var: IntVar, value: IntExpr),
                    
                    terminate,
                    
                    add_ref(ObjVar),
                    release(ObjVar),
                    
                    print_obj(obj: ObjExpr),

                    ret_val(<ObjExpr, BoolExpr>),
                    
                    no_op,
                    
                    branch(cond: BoolExpr, when_true: [Instr], when_false: [Instr]),
                    
                    symbol_switch(val: ObjExpr, cases: (vals: SymbObj+, instrs: [Instr])*, else: [Instr^]?),

                    repeat([Instr^]),
                    break_loop,
                    
                    execute_block([Instr^]),
                    exit_block,

                    call_proc(var: ObjVar, name: ObjFnName, params: [<ObjExpr, BoundCls>]),
                    call_cls(var: ObjVar, cls_var: Var, params: [ObjExpr]),
                    
                    push_call_info(fn_name: FnSymbol, params: [Maybe[ObjVar]]),
                    pop_call_info,

                    runtime_check(cond: ObjExpr),

                    var_scope(var: <named_par(Atom)>, new_value: AtomicExpr, body: [Instr^]),
                    cls_scope(var: <named_par(Atom)>, bound_cls: BoundCls, body: [Instr^]);


type ClsDef       = cls_def(arity: NzNat, body: [Instr^]);

type BoundCls     = ClsVar, bound_cls(cls: ClsDef, env: [Var]);

type ObjProcPar   = obj, cls(name: ClsVar?, arity: NzNat);

type ObjProcDef   = obj_proc_def(
                      name:         ObjFnName,
                      params:       [ObjProcPar],
                      named_params: (<named_par(Atom)> => Nat), //## SHOULD IT BE <named_var(name: Atom, arity: Nat)>* INSTEAD?
                      body:         [Instr^]
                    );

type BoolProcDef  = bool_proc_def(
                      name:  BoolFnName,
                      arity: NzNat,
                      body:  [Instr^]
                    );

type ProcDef      = ObjProcDef, BoolProcDef;
