//## IT WOULD BE USEFUL TO HAVE SYNTACTIC PATTERNS, WITH TUPLE PATTERNS AS SEQUENCES RATHER THAN SETS

type SynType       = Type;

type SynTypedef    = typedef(name: BasicTypeSymbol, type: SynType);

type SynParTypedef = par_typedef(name: BasicTypeSymbol, params: [TypeVar+], type: SynType);

/////////////////////////////////////////////////////////////////////////////////////

type SynExpr = object(<Atom, Int>),

               seq_expr(head: [SynSubExpr*], tail: SynExpr?),
               set_expr(SynSubExpr*),
               map_expr((key: SynExpr, value: SynExpr, cond: SynExpr?)*),
               tag_obj_expr(tag: SynExpr, obj: SynExpr),

               Var,
                    
               const_or_var(Atom), //## NOT SURE ATOM IS THE RIGHT THING HERE
               
               fn_call(name: FnSymbol, params: [ExtSynExpr*], named_params: [SynFnDef*]), //## NEW
               builtin_call(name: BuiltIn, params: [SynExpr+]),
               
               and(left: SynExpr, right: SynExpr),
               or(left: SynExpr, right: SynExpr),
               not(SynExpr),
               
               eq(left: SynExpr, right: SynExpr),
               neq(left: SynExpr, right: SynExpr),
               
               membership(obj: SynExpr, type: SynType),

               accessor(expr: SynExpr, field: SymbObj),
               accessor_test(expr: SynExpr, field: SymbObj),

               ex_qual(source: [SynClause+], sel_exprs: [SynExpr*]),
               set_comp(expr: SynExpr, source: [SynClause+], sel_exprs: [SynExpr*]),
               map_comp(key_expr: SynExpr, value_expr: SynExpr, source: [SynClause+], sel_exprs: [SynExpr*]),
               seq_comp(expr: SynExpr, var: Var, idx_var: Var?, src_expr: SynExpr, sel_expr: SynExpr?),

               if_expr(branches: [(cond: SynExpr, expr: SynExpr)+], else: SynExpr),
               match_expr(exprs: [SynExpr+], cases: [SynCase+]),
               do_expr([SynStmt+]),

               select_expr(type: SynType, src_expr: SynExpr),
               retrieve_expr(expr: SynExpr, ptrn: Pattern, src_expr: SynExpr, cond: SynExpr?),
               replace_expr(expr: SynExpr, src_expr: SynExpr, ptrn: Pattern),

               //is_expr(expr: SynExpr, type: SynType),
               //where_expr(expr: SynExpr, fndefs: [SynFnDef+]),
               let_expr(expr: SynExpr, stmts: [SynStmt+]);


type SynClsExpr  = cls_expr(params: [<var(Atom)>+], expr: SynExpr); //## NEW

type ExtSynExpr  = SynExpr, SynClsExpr; //## NEW


type SynCondExpr  = cond_expr(expr: SynExpr, cond: SynExpr);

type SynSubExpr   = SynExpr, SynCondExpr;

type SynClause    = in_clause(ptrn: Pattern, src: SynExpr),
                    not_in_clause(ptrn: Pattern, src: SynExpr),
                    map_in_clause(key_ptrn: Pattern, value_ptrn: Pattern, src: SynExpr),
                    map_not_in_clause(key_ptrn: Pattern, value_ptrn: Pattern, src: SynExpr),
                    eq_clause(var: Var, expr: SynExpr),
                    and_clause([SynClause+]),
                    or_clause(left: SynClause, right: SynClause);

type SynCase      = case(patterns: [Pattern+], expr: SynExpr);  //## CHANGE

type SynStmt      = assignment_stmt(var: Var, value: SynExpr),
                    return_stmt(SynExpr),
                    if_stmt(branches: [(cond: SynExpr, body: [SynStmt+])+], else: [SynStmt*]),
                    loop_stmt(cond: SynExpr, skip_first: Bool, body: [SynStmt+]),
                    inf_loop_stmt([SynStmt+]),
                    for_stmt(loops: [SynIter+], body: [SynStmt+]),
                    let_stmt(asgnms: [SynFnDef+], body: [SynStmt+]), //## NEW
                    break_stmt,
                    fail_stmt,
                    assert_stmt(SynExpr),
                    print_stmt(SynExpr);

type SynIter      = seq_iter(var: Var, idx_var: Var?, values: SynExpr),
                    range_iter(var: Var, start_val: SynExpr, end_val: SynExpr);

/////////////////////////////////////////////////////////////////////////////////////

type SynFnDef       = syn_fn_def(
                        name:       FnSymbol,
                        params:     [(type: SynType?, var: var(Atom)?)*],
                        res_type:   SynType?,
                        expr:       SynExpr,
                        local_fns:  [SynFnDef*]
                      );

type SynSgn         = syn_sgn(
                        name:     FnSymbol,
                        params:   [Type*],
                        res_type: Type
                      );

type SynUsingBlock  = using_block(
                        signatures: [SynSgn+],
                        fn_defs:    [SynFnDef+]
                      );

type PrgDecl        = SynTypedef, SynParTypedef, SynFnDef, SynUsingBlock;

type SynPrg         = prg([PrgDecl*]);
