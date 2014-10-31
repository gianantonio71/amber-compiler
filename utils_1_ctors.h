
SynParTypeSymbol syn_par_type_symbol(BasicTypeSymbol s, [SynType^] ps) = par_type_symbol(symbol: s, params: ps);

////////////////////////////////////////////////////////////////////////////////

SynType       syn_int_range(Int min, Int max)                       = syn_int_range(min: min, max: max);
SynTypeRef    syn_type_ref(BasicTypeSymbol s, [SynType^] ps)        = :type_ref(syn_par_type_symbol(s, ps));
SynRecordType syn_record_type([SynRecordField^] fields)             = :tuple_type(fields);
SynTagObjType syn_tag_obj_type(TagType tag_type, SynType obj_type)  = tag_obj_type(tag_type: tag_type, obj_type: obj_type);
SynTagObjType syn_any_tag_obj_type(SynType obj_type)                = syn_tag_obj_type(atom_type, obj_type);
SynType       syn_union([SynType^] types)                           = if length(types) == 1 then types[0] else :syn_union_type(types) end;

SynType syn_set_type(SynType elem_type, Bool non_empty)
{
  res_type := ne_set_type(elem_type: elem_type);
  res_type := syn_union([empty_set_type, res_type]) if not non_empty;
  return res_type;
}

SynType syn_seq_type(SynType elem_type, Bool non_empty)
{
  res_type := ne_seq_type(elem_type: elem_type);
  res_type := syn_union([empty_seq_type, res_type]) if not non_empty;
  return res_type;
}

SynType syn_map_type(SynType key_type, SynType value_type) =
  syn_union([
    empty_map_type,
    ne_map_type(key_type: key_type, value_type: value_type)
  ]);

////////////////////////////////////////////////////////////////////////////////

SynTypedef syn_typedef(BasicTypeSymbol n, SynType t) = typedef(name: n, type: t);

SynParTypedef syn_par_typedef(BasicTypeSymbol n, [TypeVar^] ps, SynType t) = par_typedef(name: n, params: ps, type: t);

////////////////////////////////////////////////////////////////////////////////


ConstOrVar const_or_var(Atom a)                           = :const_or_var(a);

SynSeqExpr syn_seq_expr([SynSubExpr] h)                   = seq_expr(head: h);
SynSeqExpr syn_seq_expr([SynSubExpr] h, SynExpr t)        = seq_expr(head: h, tail: t);
SynSetExpr syn_set_expr([SynSubExpr] ses)                 = :set_expr(set(ses));
SynMapExpr syn_map_expr([SynMapExprEntry] es)             = :map_expr(set(es));
SynTagObjExpr syn_tag_obj_expr(SynExpr t, SynExpr o)      = tag_obj_expr(tag: t, obj: o);

SynFnCall syn_fn_call(FnSymbol n, [ExtSynExpr] ps) = syn_fn_call(n, ps, []);
SynFnCall syn_fn_call(FnSymbol n, [ExtSynExpr] ps, [SynFnDef] nps) = fn_call(name: n, params: ps, named_params: nps);

SynBuiltInCall syn_builtin_call(BuiltIn bi, [SynExpr^] ps) = builtin_call(name: bi, params: ps);

SynBoolExpr syn_and(SynExpr l, SynExpr r) = and(left: l, right: r);
SynBoolExpr syn_or(SynExpr l, SynExpr r)  = or(left: l, right: r);
SynBoolExpr syn_not(SynExpr e)            = :not(e);

SynCmpExpr syn_eq(SynExpr l, SynExpr r)   = eq(left: l, right: r);
SynCmpExpr syn_neq(SynExpr l, SynExpr r)  = neq(left: l, right: r);

SynMembExpr syn_membership(SynExpr e, SynType t) = membership(obj: e, type: t);
// type SynCastExpr    = cast_expr(expr: SynExpr, type: SynType);

SynAccExpr syn_accessor(SynExpr e, Atom f)    = syn_accessor(e, object(f));
SynAccExpr syn_accessor(SynExpr e, SymbObj f) = accessor(expr: e, field: f);

SynAccTestExpr syn_accessor_test(SynExpr e, Atom f)    = syn_accessor_test(e, object(f));
SynAccTestExpr syn_accessor_test(SynExpr e, SymbObj f) = accessor_test(expr: e, field: f);

SynExQualExpr syn_ex_qual([SynClause^] cs, [SynExpr] es) = ex_qual(source: cs, sel_exprs: es);
SynSCExpr syn_set_comp(SynExpr e, [SynClause^] cs, [SynExpr] es) = set_comp(expr: e, source: cs, sel_exprs: es);
SynMCExpr syn_map_comp(SynExpr k, SynExpr v, [SynClause^] cs, [SynExpr] es) = map_comp(key_expr: k, value_expr: v, source: cs, sel_exprs: es);

// type SynLCExpr      = seq_comp(expr: SynExpr, var: Var, idx_var: Var?, src_expr: SynExpr, sel_expr: SynExpr?);

SynIfExpr syn_if_expr([(cond: SynExpr, expr: SynExpr)^] bs, SynExpr ee) = if_expr(branches: bs, else: ee);

SynTryExpr syn_try_expr([SynExpr^] es, [SynCase^] cs) = match_expr(exprs: es, cases: cs);

SynDoExpr syn_do_expr([SynStmt^] ss) = :do_expr(ss);

SynSelExpr syn_select_expr(SynType t, SynExpr e)                      = select_expr(type: t, src_expr: e);
SynReplExpr syn_replace_expr(SynExpr e, SynExpr se, SynType t, Var v) = replace_expr(expr: e, src_expr: se, type: t, var: v);

// type SynLetExpr     = let_expr(expr: SynExpr, stmts: [SynAsgnStmt^]);

////////////////////////////////////////////////////////////////////////////////

SynCondExpr cond_expr(SynExpr e, SynExpr c) = cond_expr(expr: e, cond: c);

////////////////////////////////////////////////////////////////////////////////

SynAsgnStmt syn_asgnm_stmt(Var v, SynExpr e)                                = assignment_stmt(var: v, value: e);
SynReturnStmt syn_ret_stmt(SynExpr e)                                       = :return_stmt(e);
SynIfStmt syn_if_stmt(SynExpr c, [SynStmt^] ss)                             = syn_if_stmt([(cond: c, body: ss)], []);
SynIfStmt syn_if_stmt([(cond: SynExpr, body: [SynStmt^])^] bs, [SynStmt] e) = if_stmt(branches: bs, else: e);
SynLoopStmt syn_loop_stmt(SynExpr c, [SynStmt^] b)                          = syn_loop_stmt(c, b, false);
SynLoopStmt syn_loop_stmt(SynExpr c, [SynStmt^] b, Bool s)                  = loop_stmt(cond: c, skip_first: s, body: b);
SynInfLoopStmt syn_inf_loop_stmt([SynStmt^] ss)                             = :inf_loop_stmt(ss);
SynForStmt syn_for_stmt([SynIter^] ls, [SynStmt^] b)                        = for_stmt(loops: ls, body: b);
SynLetStmt syn_let_stmt([SynFnDef^] a, [SynStmt^] b)                        = let_stmt(asgnms: a, body: b);
SynAssertStmt syn_assert_stmt(SynExpr e)                                    = :assert_stmt(e);
SynPrintStmt syn_print_stmt(SynExpr e)                                      = :print_stmt(e);

SynFnDefStmt syn_fn_def_stmt(SynFnDef fd)                                   = :fn_def_stmt(fd);

// type SynAsgnStmt    = assignment_stmt(var: Var, value: SynExpr);
// type SynReturnStmt  = return_stmt(SynExpr);
// type SynIfStmt      = if_stmt(branches: [(cond: SynExpr, body: [SynStmt^])^], else: [SynStmt]);
// type SynLoopStmt    = loop_stmt(cond: SynExpr, skip_first: Bool, body: [SynStmt^]);
// type SynInfLoopStmt = inf_loop_stmt([SynStmt^]);
// type SynForStmt     = for_stmt(loops: [SynIter^], body: [SynStmt^]);
// type SynLetStmt     = let_stmt(asgnms: [SynFnDef^], body: [SynStmt^]);

SynIter syn_seq_iter(Var v, SynExpr e)                                      = seq_iter(var: v, values: e);
SynIter syn_seq_iter(Var v, Var iv, SynExpr e)                              = seq_iter(var: v, idx_var: iv, values: e);
SynIter syn_range_iter(Var v, SynExpr se, SynExpr ee)                       = range_iter(var: v, start_val: se, end_val: ee);

////////////////////////////////////////////////////////////////////////////////

SynClause syn_in_clause(SynPtrn p, SynExpr e)                   = in_clause(ptrn: p, src: e);
SynClause syn_map_in_clause(SynPtrn kp, SynPtrn vp, SynExpr e)  = map_in_clause(key_ptrn: kp, value_ptrn: vp, src: e);
SynClause syn_eq_clause(Var v, SynExpr e)                       = eq_clause(var: v, expr: e);
SynClause syn_and_clause([SynClause^] cs)                       = if length(cs) == 1 then cs[0] else :and_clause(cs) end;
SynClause syn_or_clause(SynClause l, SynClause r)               = or_clause(left: l, right: r);

////////////////////////////////////////////////////////////////////////////////

SynPtrn syn_ptrn_integer(Int n)                   = :ptrn_integer(object(n));

SynPtrn syn_ptrn_seq                              = :ptrn_seq;
SynPtrn syn_ptrn_set                              = :ptrn_set;
SynPtrn syn_ptrn_map                              = :ptrn_map;

SynPtrn syn_ptrn_tag_obj(Atom a)                  = syn_ptrn_tag_obj(ptrn_symbol(a), ptrn_any);
SynPtrn syn_ptrn_tag_obj(TagPtrn tp, SynPtrn op)  = ptrn_tag_obj(tag: tp, obj: op);

SynPtrn syn_ptrn_var(Atom a)                      = syn_ptrn_var(var(a));
SynPtrn syn_ptrn_var(Var v)                       = syn_ptrn_var(v, ptrn_any);
SynPtrn syn_ptrn_var(Var v, SynPtrn p)            = ptrn_var(var: v, ptrn: p);

SynPtrn syn_ptrn_type(SynType t)                  = :ptrn_type(t);


SynCase syn_case([SynPtrn^] ps, SynExpr e) = case(patterns: ps, expr: e);

////////////////////////////////////////////////////////////////////////////////

SynSgn syn_sgn(FnSymbol n, [SynType] ps, SynType rt) = syn_sgn(name: n, params: ps, res_type: rt);

SynUsingBlock syn_using_block([SynSgn^] ss, [SynFnDef^] fds) = using_block(signatures: ss, fn_defs: fds);
