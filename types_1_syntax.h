// SynTypeSymbol must be a subset of TypeSymbol

type SynParTypeSymbol = par_type_symbol(symbol: BasicTypeSymbol, params: [SynType^]);
type SynTypeSymbol    = BasicTypeSymbol, SynParTypeSymbol;

/////////////////////////////////////////////////////////////////////////////////////

// SynType must be a superset of UserType

type SynType        = SynLeafType, SynTypeRef, TypeVar, SynNeSeqType, SynNeSetType,
                      SynNeMapType, SynRecordType, SynTupleType, SynTagObjType, SynUnionType;

type SynLeafType    = LeafType, syn_int_range(min: Int, max: Int);
type SynTypeRef     = type_ref(SynTypeSymbol);

type SynNeSeqType   = ne_seq_type(elem_type: SynType);
type SynNeSetType   = ne_set_type(elem_type: SynType);
type SynNeMapType   = ne_map_type(key_type: SynType, value_type: SynType);

type SynRecordType  = record_type(<[SynRecordField^], SynRecordMap>);
type SynRecordField = (label: SymbObj, type: SynType, optional: Bool);
type SynRecordMap   = (SymbObj => (type: UserType, optional: Bool));

type SynTupleType   = tuple_type([SynType^]);

type SynTagObjType  = tag_obj_type(tag_type: SynType, obj_type: SynType);

type SynUnionType   = union_type(SynType+), syn_union_type([SynType^]);

/////////////////////////////////////////////////////////////////////////////////////

type SynClsType  = cls_type(in_types: [SynType^], out_type: SynType);
type SynExtType  = SynType, SynClsType;

/////////////////////////////////////////////////////////////////////////////////////

type SynTypedef    = typedef(name: BasicTypeSymbol, type: SynType);

type SynParTypedef = par_typedef(name: BasicTypeSymbol, params: [TypeVar^], type: SynType);

/////////////////////////////////////////////////////////////////////////////////////

type SynExpr  = LeafObj, FloatLit, Var, ConstOrVar, ClsPar,
                SynSeqExpr, SynSetExpr, SynMapExpr, SynTagObjExpr,
                SynFnCall, SynBuiltInCall,
                SynBoolExpr, SynCmpExpr,
                SynMembExpr, SynCastExpr,
                SynAccExpr, SynAccTestExpr,
                SynExQualExpr, SynSCExpr, SynMCExpr, SynLCExpr,
                SynIfExpr, SynTryExpr,
                SynDoExpr,
                SynSelExpr, SynReplExpr,
                SynLetExpr;

type ConstOrVar       = const_or_var(Atom); //## NOT SURE ATOM IS THE RIGHT THING HERE

type ClsPar           = cls_par(Nat);

type SynSeqExpr       = seq_expr([SynSubExpr]), seq_tail_expr(seq: SynExpr, tail: [SynExpr^]);
type SynSetExpr       = set_expr(SynSubExpr*);
type SynMapExpr       = map_expr(SynMapExprEntry*);
type SynTagObjExpr    = tag_obj_expr(tag: SynExpr, obj: SynExpr);


type SynFnCall        = fn_call(name: FnSymbol, params: [ExtSynExpr], named_params: [SynFnDef]); //## BAD: NAMED PARAMS AS SynFnDef? REALLY?
type SynBuiltInCall   = builtin_call(name: BuiltIn, params: [SynExpr^]);

type SynBoolExpr      = and(left: SynExpr, right: SynExpr),
                        or(left: SynExpr, right: SynExpr),
                        not(SynExpr);

type SynCmpExpr       = eq(left: SynExpr, right: SynExpr),
                        neq(left: SynExpr, right: SynExpr);

type SynMembExpr      = membership(obj: SynExpr, type: SynType);
type SynCastExpr      = cast_expr(expr: SynExpr, type: SynType);

type SynAccExpr       = accessor(expr: SynExpr, field: SymbObj);
type SynAccTestExpr   = accessor_test(expr: SynExpr, field: SymbObj);

type SynExQualExpr    = ex_qual(source: [SynClause^], sel_exprs: [SynExpr]);
type SynSCExpr        = set_comp(expr: SynExpr, source: [SynClause^], sel_exprs: [SynExpr]);
type SynMCExpr        = map_comp(key_expr: SynExpr, value_expr: SynExpr, source: [SynClause^], sel_exprs: [SynExpr]);
type SynLCExpr        = seq_comp(expr: SynExpr, vars: [Var^], idx_var: Var?, src_expr: SynExpr, sel_expr: SynExpr?);

type SynIfExpr        = if_expr(branches: [(cond: SynExpr, expr: SynExpr)^], else: SynExpr);
type SynTryExpr       = match_expr(exprs: [SynExpr^], cases: [SynCase^]);

type SynDoExpr        = do_expr([SynStmt^]);

type SynSelExpr       = select_expr(type: SynType, src_expr: SynExpr);
type SynReplExpr      = replace_expr(expr: SynExpr, src_expr: SynExpr, type: SynType, var: Var);

type SynLetExpr       = let_expr(expr: SynExpr, stmts: [SynAsgnStmt^]);

/////////////////////////////////////////////////////////////////////////////////////

type SynClsExpr       = cls_expr(params: [<var(Atom)>^], expr: SynExpr);
type ExtSynExpr       = SynExpr, SynClsExpr;

type SynCondExpr      = cond_expr(expr: SynExpr, cond: SynExpr);
type SynSubExpr       = SynExpr, SynCondExpr;

type SynMapExprEntry  = (key: SynExpr, value: SynExpr, cond: SynExpr?);

/////////////////////////////////////////////////////////////////////////////////////

type SynPtrn    = ptrn_symbol,
                  ptrn_integer,
                  ptrn_float,
                  ptrn_seq,
                  ptrn_set,
                  ptrn_map,
                  ptrn_tag_obj,
                  ptrn_any,
                  ptrn_symbol(SymbObj),
                  ptrn_integer(IntObj),
                  ptrn_tag_obj(tag: TagPtrn, obj: SynPtrn),
                  ptrn_var(var: Var, ptrn: SynPtrn),
                  ptrn_type(SynType);

type SynClause  = in_clause(ptrn: SynPtrn, src: SynExpr),
                  map_in_clause(key_ptrn: SynPtrn, value_ptrn: SynPtrn, src: SynExpr),
                  eq_clause(var: Var, expr: SynExpr),
                  and_clause([SynClause^]),
                  or_clause(left: SynClause, right: SynClause);

type SynCase    = case(patterns: [SynPtrn^], expr: SynExpr);

/////////////////////////////////////////////////////////////////////////////////////

type SynStmt  = SynAsgnStmt, SynReturnStmt, SynIfStmt, SynLoopStmt, SynInfLoopStmt, SynForStmt,
                SynLetStmt, SynBreakStmt, SynFailStmt, SynAssertStmt, SynPrintStmt, SynFnDefStmt;

type SynAsgnStmt    = assignment_stmt(vars: [Var^], value: SynExpr);
type SynReturnStmt  = return_stmt(SynExpr);
type SynIfStmt      = if_stmt(branches: [(cond: SynExpr, body: [SynStmt^])^], else: [SynStmt]);
type SynLoopStmt    = loop_stmt(cond: SynExpr, skip_first: Bool, body: [SynStmt^]);
type SynInfLoopStmt = inf_loop_stmt([SynStmt^]);
type SynForStmt     = for_stmt(loops: [SynIter^], body: [SynStmt^]);
type SynLetStmt     = let_stmt(asgnms: [SynFnDef^], body: [SynStmt^]); //## BAD: REPLACE THOSE SynFnDef WITH SOMETHING MORE APPROPRIATE
type SynBreakStmt   = break_stmt; //## REPLACE WITH BreakStmt
type SynFailStmt    = fail_stmt;  //## REPLACE WITH FailStmt
type SynAssertStmt  = assert_stmt(SynExpr);
type SynPrintStmt   = print_stmt(SynExpr);

type SynFnDefStmt   = fn_def_stmt(SynFnDef);

type SynIter  = seq_iter(vars: [Var^], idx_var: Var?, values: SynExpr),
                range_iter(var: Var, start_val: SynExpr, end_val: SynExpr);

/////////////////////////////////////////////////////////////////////////////////////

type SynFnDef       = syn_fn_def(
                        name:       FnSymbol,
                        params:     [SynFnArg],
                        res_type:   SynType?,
                        expr:       SynExpr,
                        local_fns:  [SynFnDef]
                      );

type SynFnArg       = (type: SynExtType?, var: var(Atom)?);

type SynSgn         = syn_sgn(
                        name:     FnSymbol,
                        params:   [SynType],
                        res_type: SynType
                      );

type SynUsingBlock  = using_block(
                        signatures: [SynSgn^],
                        fn_defs:    [SynFnDef^]
                      );

type SynSubtypeDecl = SubtypeDecl;

type PrgDecl        = SynTypedef, SynParTypedef, SynFnDef, SynUsingBlock, SynSubtypeDecl;

type SynPrg         = prg([PrgDecl]);
