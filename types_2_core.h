
type Obj        = object(Any);

type SymbObj    = object(Atom);
type LeafObj    = object(<Atom, Int>);

///////////////////////////////////////////////////////////////////////////////

type BasicTypeSymbol  = type_symbol(Atom);
type ParTypeSymbol    = par_type_symbol(symbol: BasicTypeSymbol, params: [Type+]);
type TypeSymbol       = BasicTypeSymbol, ParTypeSymbol;

type TypeName         = type_name(symbol: BasicTypeSymbol, arity: Nat);

///////////////////////////////////////////////////////////////////////////////

// type Type           = LeafType, TypeVar, SelfPretype, CompType[Type], UnionType[Type], SelfRecType[Type], MutRecType[Type];
type AnonType       = LeafType, TypeVar, SelfPretype, CompType[AnonType], UnionType[AnonType], SelfRecType[AnonType], MutRecType[AnonType];

// type Type           = LeafType, TypeVar, CompType[Type], UnionType[Type], SelfRecType[SelfRefPretype], MutRecType[MutRefPretype];
// type SelfRefPretype = LeafType, TypeVar, self, CompType[Type], UnionType[Type], SelfRecType[SelfRefPretype], MutRecType[MutRefPretype];
// type MutRefPretype  = LeafType, TypeVar, self(Nat), CompType[Type], UnionType[Type], SelfRecType[SelfRefPretype], MutRecType[MutRefPretype];

type VoidType       = void_type;
type ClosedType     = void_type, Type; //## FIND BETTER NAME

// type NonRecType     = LeafType, TypeVar, CompType[NonRecType], UnionType[NonRecType];
// type NonParType     = LeafType, SelfPretype, CompType[NonParType], UnionType[NonParType], SelfRecType[NonParType], MutRecType[NonParType];

type SymbType       = symb_type(SymbObj);

type IntType        = integer, low_ints(max: Int), high_ints(min: Int), int_range(min: Int, size: NzNat);

type LeafType       = atom_type, SymbType, IntType, empty_seq_type, empty_set_type, empty_map_type;

type SelfPretype    = self, self(Nat);

type TypeVar        = type_var(<Atom, Nat>);

type NeSeqType[T]   = ne_seq_type(elem_type: T);
type SeqType[T]     = empty_seq_type, NeSeqType[T];

type NeSetType[T]   = ne_set_type(elem_type: T);
type SetType[T]     = empty_set_type, NeSetType[T];

type NeMapType[T]   = ne_map_type(key_type: T, value_type: T);
type MapType[T]     = empty_map_type, NeMapType[T];

type TupleType[T]   = tuple_type((SymbObj => (type: T, optional: Bool))); //## THE EMPTY MAP SHOULD NOT BE INCLUDED

type TagType        = SymbType, atom_type, TypeVar;
type TagObjType[T]  = tag_obj_type(tag_type: TagType, obj_type: T);

type CompType[T]    = NeSeqType[T], NeSetType[T], NeMapType[T], TupleType[T], TagObjType[T]; //## FIND BETTER NAME

type UnionType[T]   = union_type(T+);

type SelfRecType[T] = self_rec_type(T);

type MutRecType[T]  = mut_rec_type(index: Nat, types: [T+]);

///////////////////////////////////////////////////////////////////////////////

type RawType  = LeafType, TypeRef, TypeVar, CompType[RawType], UnionType[RawType];

type TypeRef  = type_ref(TypeSymbol);

type Type     = RawType;

///////////////////////////////////////////////////////////////////////////////

type ClsType  = cls_type(in_types: [Type+], out_type: Type);

type ExtType  = Type, ClsType;

type FnType     = fn_type(
                    params:       [ExtType*],
                    named_params: (<named_par(Atom)> => ExtType),
                    ret_type:     Type
                  );

///////////////////////////////////////////////////////////////////////////////

type SubtypeDecl  = subtype_decl(subtype: Type, supertype: Type);

///////////////////////////////////////////////////////////////////////////////

type Operator = plus, minus, star, slash, exp, amp, lower, greater, lower_eq, greater_eq, brackets;

type BuiltIn  = neg, add, counter, str, symb, at, len, slice, cat, rev, set, mset, isort, list_to_seq;

type FnSymbol = fn_symbol(Atom),
                op_symbol(Operator),
                nested_fn_symbol(outer: FnSymbol, inner: FnSymbol); //## BAD

type Var      = var(Atom), fn_par(Nat), named_par(Atom), unique_var(Nat); //## BAD

type CondExpr = cond_expr(expr: Expr, cond: Expr);

type SubExpr  = Expr, CondExpr;

type Expr     = LeafObj, //## UPDATE ALL REFERENCES

                set_expr(SubExpr*), //## MAYBE I SHOULDN'T ALLOW EMPTY EXPRESSIONS
                seq_expr(head: [SubExpr*], tail: Expr?), //## I DON'T LIKE THIS MUCH
                map_expr((key: Expr, value: Expr, cond: Expr?)*),
                tag_obj_expr(tag: Expr, obj: Expr),

                Var,

                //## CAN LOCAL FUNCTIONS HAVE NAMED PARAMETERS? IT WOULDN'T MAKE MUCH SENSE,
                //## BUT THE DATA STRUCTURE AND THE SYNTAX ALLOW IT. MAKE SURE IT'S CHECHED
                //## IN THE WELL-FORMEDNESS CHECKING LAYER.
                fn_call(name: FnSymbol, params: [ExtExpr*], named_params: (<named_par(Atom)> => ExtExpr)), //## BAD
                cls_call(name: Var, params: [Expr*]),  //## NEW --- RENAME name: TO var:
                builtin_call(name: BuiltIn, params: [Expr*]), //## CAN A BUILTIN HAVE NO ARGUMENTS?

                and_expr(left: Expr, right: Expr), //## NOT SURE HERE
                or_expr(left: Expr, right: Expr),  //## NOT SURE HERE
                not_expr(Expr),                    //## NOT SURE HERE
                
                eq(left: Expr, right: Expr),
                membership(obj: Expr, type: Type),
                
                accessor(expr: Expr, field: SymbObj),      //## SHOULD <field> BE AN OBJECT OR JUST A PLAIN SYMBOL?
                accessor_test(expr: Expr, field: SymbObj), //## DITTO

                if_expr(cond: Expr, then: Expr, else: Expr),
                match_expr(exprs: [Expr+], cases: [(ptrns: [Pattern+], expr: Expr)+]),
                do_expr([Statement+]),

                ex_qual(source: Clause, sel_expr: Expr?),
                set_comp(expr: Expr, source: Clause, sel_expr: Expr?),
                map_comp(key_expr: Expr, value_expr: Expr, source: Clause, sel_expr: Expr?),
                seq_comp(expr: Expr, var: Var, idx_var: Var?, src_expr: Expr, sel_expr: Expr?),

                select_expr(expr: Expr, ptrn: Pattern, src_expr: Expr, cond: Expr?),
                replace_expr(expr: Expr, src_expr: Expr, ptrn: Pattern);

///////////////////////////////////////////////////////////////////////////////

//type Closure  = closure(params: [var(Atom)+], expr: Expr, captured_vars: Var*);

type ClsExpr  = cls_expr(params: [<var(Atom), nil>+], expr: Expr);

type ExtExpr  = Expr, ClsExpr;

///////////////////////////////////////////////////////////////////////////////

type Pattern  = ptrn_any, //## IN THEORY THIS IS REDUNDANT...
                obj_ptrn(LeafObj),
                type_ptrn(Type),
                ext_var_ptrn(Var),
                var_ptrn(name: Var, ptrn: Pattern),
                tag_ptrn(tag: <obj_ptrn(SymbObj), var_ptrn(name: Var, ptrn: ptrn_any)>, obj: Pattern);

////////////////////////////////////////////////////////////////////////////////

type Clause   = in_clause(ptrn: Pattern, src: Expr),
                not_in_clause(ptrn: Pattern, src: Expr),
                map_in_clause(key_ptrn: Pattern, value_ptrn: Pattern, src: Expr),
                map_not_in_clause(key_ptrn: Pattern, value_ptrn: Pattern, src: Expr),
                and_clause(left: Clause, right: Clause),
                or_clause(left: Clause, right: Clause);

////////////////////////////////////////////////////////////////////////////////

type Statement  = assignment_stmt(var: Var, value: Expr),
                  return_stmt(Expr),
                  if_stmt(cond: Expr, body: [Statement+], else: [Statement*]),
                  loop_stmt([Statement+]),
                  foreach_stmt(var: Var, idx_var: Var?, values: Expr, body: [Statement+]),
                  for_stmt(var: Var, start_val: Expr, end_val: Expr, body: [Statement+]),
                  let_stmt(asgnms: (<named_par(Atom)> => ExtExpr), body: [Statement+]), //## BAD
                  break_stmt,
                  fail_stmt,
                  assert_stmt(Expr),
                  print_stmt(Expr);

///////////////////////////////////////////////////////////////////////////////

//type Signature  = signature(
//                    name:     FnSymbol,
//                    params:   [Type*],
//                    res_type: Type
//                  );

type FnDef      = fn_def(
                    name:         FnSymbol,
                    params:       [(var: var(Atom)?, type: ExtType?)*], //## BAD BAD
                    named_params: (<named_par(Atom)> => ExtType), //## BAD: THIS DOESN'T ALLOW FOR IMPLICIT PARAMETER WITH THE SAME NAME BUT DIFFERENT ARITIES. ALSO THE TYPE IS TOO LOOSE. INCLUDE A CHECK IN THE WELL-FORMEDNESS CHECKING LAYER
                    res_type:     Type?,
                    expr:         Expr
                    //impl_env: Signature*,
                  );

type Program    = program(
                    tdefs:          (TypeSymbol => Type),
                    anon_tdefs:     (TypeName => AnonType),
                    subtype_decls:  SubtypeDecl*,
                    fndefs:         FnDef*
                  );
