
type Obj        = object(Any);

type SymbObj    = object(Atom);
type IntObj     = object(Int);
type LeafObj    = object(<Atom, Int>);

///////////////////////////////////////////////////////////////////////////////

type BasicTypeSymbol  = type_symbol(Atom);
type ParTypeSymbol    = par_type_symbol(symbol: BasicTypeSymbol, params: [UserType+]);
type TypeSymbol       = BasicTypeSymbol, ParTypeSymbol;

type TypeName         = type_name(symbol: BasicTypeSymbol, arity: Nat);

///////////////////////////////////////////////////////////////////////////////

// type Type           = LeafType, TypeVar, SelfPretype, CompType[Type], UnionType[Type], SelfRecType[Type], MutRecType[Type];
type AnonType       = LeafType, TypeVar, SelfPretype, CompType[AnonType], UnionType[AnonType], RecType[AnonType];

// type Type              = LeafType, TypeVar, CompType[Type], UnionType[Type], SelfRecType[SelfRefPretype], MutRecType[MutRefPretype];
// type SelfRefPretype    = LeafType, TypeVar, CompType[Type], UnionType[Type], SelfRecType[SelfRefPretype], MutRecType[MutRefPretype];
// type MutRefPretype     = LeafType, TypeVar, CompType[Type], UnionType[Type], SelfRecType[SelfRefPretype], MutRecType[MutRefPretype];
// type SelfRefPrePretype = LeafType, TypeVar, self, CompType[Type], UnionType[Type], SelfRecType[SelfRefPretype], MutRecType[MutRefPretype];
// type MutRefPrePretype  = LeafType, TypeVar, self(Nat), CompType[Type], UnionType[Type], SelfRecType[SelfRefPretype], MutRecType[MutRefPretype];
type VoidType       = void_type;
type ClosedType     = void_type, AnonType; //## FIND BETTER NAME

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

type TupleType[T]   = tuple_type((SymbObj => (type: T, optional: Bool))); //## THE EMPTY MAP SHOULD NOT BE INCLUDED. OR SHOULD IT?

type TagType        = SymbType, atom_type; //, TypeVar; //## THE CODE HASN'T BEEN UPDATED YET
type TagObjType[T]  = tag_obj_type(tag_type: TagType, obj_type: T);

type CompType[T]    = NeSeqType[T], NeSetType[T], NeMapType[T], TupleType[T], TagObjType[T]; //## FIND BETTER NAME

type UnionType[T]   = union_type(T+);

type SelfRecType[T] = self_rec_type(T);

type MutRecType[T]  = mut_rec_type(index: Nat, types: [T+]);

type RecType[T]     = SelfRecType[T], MutRecType[T];

///////////////////////////////////////////////////////////////////////////////

type ClsType  = cls_type(in_types: [AnonType+], out_type: AnonType);
type ExtType  = AnonType, ClsType;

type FnType   = fn_type(
                  params:       [ExtType*],
                  named_params: (<named_par(Atom)> => ExtType),
                  ret_type:     AnonType
                );

///////////////////////////////////////////////////////////////////////////////

type UserType = LeafType, TypeRef, TypeVar, CompType[UserType], UnionType[UserType];

type TypeRef  = type_ref(TypeSymbol);

///////////////////////////////////////////////////////////////////////////////

type UserClsType  = user_cls_type(in_types: [UserType+], out_type: UserType);
type UserExtType  = UserType, UserClsType;

///////////////////////////////////////////////////////////////////////////////

type SubtypeDecl  = subtype_decl(subtype: UserType, supertype: UserType);

///////////////////////////////////////////////////////////////////////////////

type Operator = plus, minus, star, slash, exp, amp, lower, greater, lower_eq, greater_eq, brackets;

type BuiltIn  = neg, add, str, symb, at, len, slice, cat, rev, set, mset, isort, list_to_seq, tag, obj,
                in, has_key, lookup, union, merge, rand_nat, rand_elem, counter;

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
                
                membership(obj: Expr, type: UserType),
                cast_expr(expr: Expr, type: UserType),

                accessor(expr: Expr, field: SymbObj),      //## SHOULD <field> BE AN OBJECT OR JUST A PLAIN SYMBOL?
                accessor_test(expr: Expr, field: SymbObj), //## DITTO

                if_expr(cond: Expr, then: Expr, else: Expr),
                match_expr(exprs: [Expr+], cases: [(ptrns: [Pattern+], expr: Expr)+]),
                do_expr([Statement+]),

                ex_qual(source: Clause, sel_expr: Expr?),
                set_comp(expr: Expr, source: Clause, sel_expr: Expr?),
                map_comp(key_expr: Expr, value_expr: Expr, source: Clause, sel_expr: Expr?),
                seq_comp(expr: Expr, var: Var, idx_var: Var?, src_expr: Expr, sel_expr: Expr?),

                select_expr(type: UserType, src_expr: Expr),
                replace_expr(expr: Expr, src_expr: Expr, type: UserType, var: Var);

///////////////////////////////////////////////////////////////////////////////

//type Closure  = closure(params: [var(Atom)+], expr: Expr, captured_vars: Var*);

type ClsExpr  = cls_expr(params: [<var(Atom), nil>+], expr: Expr);

type ExtExpr  = Expr, ClsExpr;

///////////////////////////////////////////////////////////////////////////////

type Pattern  = ptrn_symbol, //## THE CORRESPONDING TYPE IS CALLED atom_type. RENAME ONE OF THE TWO?
                ptrn_integer, //## THIS IS ACTUALLY REDUNDANT, AS IT IS THE SAME AS ptrn_integer(integer)
                ptrn_empty_set,
                ptrn_ne_set,
                ptrn_empty_seq,
                ptrn_ne_seq,
                ptrn_empty_map,
                ptrn_ne_map,
                // ptrn_seq,
                // ptrn_set,
                // ptrn_map,
                ptrn_tag_obj,
                ptrn_any,
                ptrn_symbol(SymbObj),
                ptrn_integer(IntType),
                ptrn_tag_obj(tag: TagPtrn, obj: Pattern),
                // ptrn_record((SymbObj => Pattern)),
                ptrn_var(var: Var, ptrn: Pattern),
                ptrn_union(Pattern+);


type TagPtrn  = ptrn_symbol, ptrn_symbol(SymbObj), ptrn_var(var: Var, ptrn: ptrn_symbol);

////////////////////////////////////////////////////////////////////////////////

type Clause   = in_clause(ptrn: Pattern, src: Expr),
                map_in_clause(key_ptrn: Pattern, value_ptrn: Pattern, src: Expr),
                and_clause(left: Clause, right: Clause),
                or_clause(left: Clause, right: Clause);

////////////////////////////////////////////////////////////////////////////////

type Statement  = assignment_stmt(var: Var, value: Expr),
                  return_stmt(Expr),
                  if_stmt(cond: Expr, body: [Statement+], else: [Statement*]),
                  loop_stmt([Statement+]),
                  foreach_stmt(var: Var, idx_var: Var?, values: Expr, body: [Statement+]),
                  for_stmt(var: Var, start_val: Expr, end_val: Expr, body: [Statement+]),
                  let_stmt(asgnms: (<named_par(Atom)> => Expr), body: [Statement+]), //## BAD
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
                    params:       [(var: var(Atom)?, type: UserExtType?)*], //## BAD BAD
                    named_params: (<named_par(Atom)> => UserExtType), //## BAD: THIS DOESN'T ALLOW FOR IMPLICIT PARAMETER WITH THE SAME NAME BUT DIFFERENT ARITIES. ALSO THE TYPE IS TOO LOOSE. INCLUDE A CHECK IN THE WELL-FORMEDNESS CHECKING LAYER
                    res_type:     UserType?,
                    expr:         Expr
                    //impl_env: Signature*,
                  );

type Program    = program(
                    tdefs:          (TypeSymbol => UserType),
                    anon_tdefs:     (TypeName => AnonType),
                    subtype_decls:  SubtypeDecl*,
                    fndefs:         FnDef*
                  );
