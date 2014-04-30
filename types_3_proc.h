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

type AtomicExpr   = LeafObj,
                    empty_set,
                    empty_seq,
                    empty_map,
                    ObjVar;

type NatBoolOp    = is_symb(ObjExpr),
                    is_int(ObjExpr),
                    is_ne_set(ObjExpr),
                    is_ne_seq(ObjExpr),
                    is_ne_map(ObjExpr),
                    is_tagged_obj(ObjExpr),
                    //has_key(map: ObjExpr, key: ObjExpr),
                    //comes_before(expr1: ObjExpr, expr2: ObjExpr),
                    is_eq_bool(expr1: BoolExpr, expr2: BoolExpr),
                    is_eq_int(expr1: IntExpr, expr2: IntExpr),
                    is_eq(expr1: ObjExpr, expr2: ObjExpr),
                    is_gt(expr1: IntExpr, expr2: IntExpr),
                    is_ge(expr1: IntExpr, expr2: IntExpr),
                    is_lt(expr1: IntExpr, expr2: IntExpr),
                    is_le(expr1: IntExpr, expr2: IntExpr),
                    is_out_of_range(ItVar);

type NatIntOp     = get_int_val(ObjExpr),
                    get_set_size(ObjExpr),
                    get_seq_len(ObjExpr),
                    get_map_size(ObjExpr),
                    minus(IntExpr),
                    add(val1: IntExpr, val2: IntExpr),
                    mult(val1: IntExpr, val2: IntExpr),
                    idiv(val1: IntExpr, val2: IntExpr),
                    unique_int;

type NatObjOp     = //at(seq: ObjExpr, idx: ObjExpr),
                    //lookup(map: ObjExpr, key: ObjExpr),
                    get_tag(ObjExpr),
                    get_inner_obj(ObjExpr), //## RENAME?
                    
                    to_obj(<BoolExpr, IntExpr>),

                    to_str(ObjExpr), //## FOR THIS TO BE A NO-DELETE OPERATION, THE STRING MUST BE CACHED
                    to_symb(ObjExpr),

                    get_curr_obj(<SetItVar, SeqItVar>),
                    get_curr_key(MapItVar),
                    get_curr_value(MapItVar);

type BoolExpr     = true,
                    false,
                    BoolVar,
                    NatBoolOp,
                    neg(BoolExpr),
                    and([BoolExpr+]), //## SEQUENCES OR SETS?
                    or([BoolExpr+]),  //## DITTO
                    and_then([BoolExpr+]),
                    or_else([BoolExpr+]),
                    eval_bool_fn(name: BoolFnName, params: [AnyExpr+]);

type IntExpr      = Int, IntVar, NatIntOp;                    

type ObjExpr      = AtomicExpr, NatObjOp;

type AnyExpr      = BoolExpr, IntExpr, ObjExpr;

type Instr        = init_stream(StreamVar),
                    append(stream: StreamVar, obj: ObjExpr),

                    mk_set_from_stream(var: ObjVar, stream: StreamVar),
                    mk_set(var: ObjVar, elems: VecVar, size: IntExpr),

                    mk_seq_from_stream(var: ObjVar, stream: StreamVar),
                    mk_seq(var: ObjVar, elems: VecVar, size: IntExpr), //## I DON'T LIKE "elems"

                    mk_map_from_streams(var: ObjVar, key_stream: StreamVar, value_stream: StreamVar),
                    mk_map(var: ObjVar, keys: VecVar, values: VecVar, size: IntExpr),
                    
                    mk_tagged_obj(var: ObjVar, tag: ObjExpr, obj: ObjExpr),

                    mk_array(var: ObjVar, size: IntExpr, value: ObjExpr),
                    get_seq_slice(var: ObjVar, seq: ObjExpr, idx_first: IntExpr, len: IntExpr),
                    join_seqs(var: ObjVar, left: ObjExpr, right: ObjExpr),
                    rev_seq(var: ObjVar, seq: ObjExpr),
                    get_at(var: ObjVar, seq: ObjExpr, idx: IntExpr),
                    //## BUG BUG BUG: IF ObjExpr CONTAINS A NON-COUNTED REFERENCE TO THE ARRAY,
                    //## I COULD END UP WITH A CYCLE IN THE OBJECT GRAPH AND MAYBE OTHER PROBLEMS
                    set_at(var: ObjVar, idx: IntExpr, value: ObjExpr),

                    lookup(success_var: BoolVar?, var: ObjVar, map: ObjExpr, key: ObjExpr),
                    ext_lookup(success_var: BoolVar?, var: ObjVar, map: ObjExpr, key: ObjExpr),
                    merge_maps(var: ObjVar, map1: ObjExpr, map2: ObjExpr),
                    
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
                    
                    branch(cond: BoolExpr, when_true: [Instr*], when_false: [Instr*]),
                    
                    symbol_switch(val: ObjExpr, cases: (vals: SymbObj+, instrs: [Instr*])*, else: [Instr+]?),

                    repeat([Instr+]),
                    break_loop,
                    
                    execute_block([Instr+]),
                    exit_block,

                    call_proc(var: ObjVar, name: ObjFnName, params: [ObjExpr*]),
                    call_cls(var: ObjVar, cls_var: Var, params: [ObjExpr*]), //## NEW
                    
                    var_scope(var: <named_par(Atom)>, new_value: AtomicExpr, body: [Instr+]),     //## STILL NEW
                    cls_scope(var: <named_par(Atom)>, env: [Var*], cls: ClsDef, body: [Instr+]);  //## NEW
                    

type ClsDef       = cls_def(
                      //name:   FnSymbol, //## NEW
                      arity:  NzNat,
                      //env:    [Var*],  //## NEW - NOT ENTIRELY SURE ABOUT THIS ONE
                      body:   [Instr+]
                    );

type ObjProcDef   = obj_proc_def(
                      name:         ObjFnName,
                      in_arity:     Nat, //## THIS HAS TO BE UPDATED ONCE I ALLOW CLOSURES AS POSITIONAL PARAMETERS
                      named_params: (<named_par(Atom)> => Nat), //## NEW - SHOULD IT BE <named_var(name: Atom, arity: Nat)>* INSTEAD?
                      body:         [Instr+]
                    );

type BoolProcDef  = bool_proc_def(
                      name:  BoolFnName,
                      arity: NzNat,
                      body:  [Instr+]
                    );

type ProcDef      = ObjProcDef, BoolProcDef;
