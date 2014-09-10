type BasicUntypedSgn  = untyped_sgn(name: FnSymbol, arity: Nat);

type UntypedSgn       = untyped_sgn(
                          name:         FnSymbol,
                          arity:        Nat,
                          named_params: BasicUntypedSgn+?
                        );


//BasicUntypedSgn untyped_sgn(Signature d) = untyped_sgn(
//                                             name:  d.name,
//                                             arity: arity(d)
//                                           );

//BasicUntypedSgn untyped_sgn(Var v, UserExtType t):
//  var(a), Type      = untyped_sgn(name: :fn_symbol(a), arity: 0),
//  var(a), UserClsType   = untyped_sgn(name: :fn_symbol(a), arity: length(t.in_types));


BasicUntypedSgn untyped_sgn(<named_par(Atom)> var, UserExtType type):
  named_par(a), UserType  = untyped_sgn(name: :fn_symbol(a), arity: 0),
  named_par(a), UserClsType   = untyped_sgn(name: :fn_symbol(a), arity: length(type.in_types));

//BasicUntypedSgn* untyped_sgns((<named_par(Atom)> => UserExtType) nps) = {untyped_sgn(v, t) : v => t <- nps};

UntypedSgn untyped_sgn(FnDef fd) =
  untyped_sgn(
    name:         fd.name,
    arity:        arity(fd),
    named_params: untyped_sgns(fd.named_params) if fd.named_params /= ()
  );


BasicUntypedSgn untyped_sgn(Var v, ExtExpr e):
  var(a), Expr    = untyped_sgn(name: :fn_symbol(a), arity: 0),
  var(a), ClsExpr = untyped_sgn(name: :fn_symbol(a), arity: length(e.params));

//BasicUntypedSgn* untyped_sgns((<named_par(Atom)> => ExtExpr) nps) = {untyped_sgn(v, e) : v => e <- nps};
BasicUntypedSgn* untyped_sgns((<named_par(Atom)> => <UserExtType, ExtExpr>) nps) = {untyped_sgn(v, type_or_expr) : v => type_or_expr <- nps};

////////////////////////////////////////////////////////////////////////////////

BasicUntypedSgn untyped_sgn(<SynFnDef, SynSgn> d) = untyped_sgn(
                                                      name:  d.name,
                                                      arity: arity(d)
                                                    );

UntypedSgn untyped_sgn(SynFnDef fd, SynSgn+ named_params) =
  untyped_sgn(
    name:         fd.name,
    arity:        arity(fd),
    named_params: {untyped_sgn(p) : p <- named_params} 
  );

Nat arity(SynSgn s) = length(s.params);

UntypedSgn* merge_and_override(UntypedSgn* low_priority_sgns, UntypedSgn* high_priority_sgns)
{
  sgns := {s : s <- low_priority_sgns ; not (? os <- high_priority_sgns : s.name == os.name, s.arity == os.arity)};
  return sgns & high_priority_sgns;
}

Nat arity(SynFnDef d) = length(d.params);

Bool is_def(FnSymbol name, Nat arity, UntypedSgn* env, BasicUntypedSgn* actual_named_params)
{
  return (? sgn <- env : could_match(name, arity, sgn, actual_named_params));
  
  Bool could_match(FnSymbol name, Nat arity, UntypedSgn sgn, BasicUntypedSgn* actual_named_params)
  {
    return false if sgn.name /= name or sgn.arity /= arity;
    //## IGNORING THE DIFFERENCE BETWEEN SCALAR AND CLOSURES FOR POSITIONAL PARAMETERS
    //## NOT SURE ABOUT NAMED PARAMETERS, I SEEM TO REMEMBERS THE ORIGINAL VERSION OF THIS FUNCTION (THE ONE THAT GOT DELETED) WAS DIFFERENT
    formal_named_params := if sgn.named_params? then sgn.named_params else {} end;
    return subset(formal_named_params, actual_named_params);
  }
}

//## FIND BETTER NAME
Bool is_almost_def(FnSymbol name, Nat arity, UntypedSgn* env) = (? s <- env : s.name == name, s.arity == arity);

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

Var* syn_new_vars(SynPtrn ptrn):
  :ptrn_any       = {},
  obj_ptrn()      = {},
  type_ptrn()     = {},
  ext_var_ptrn()  = {},
  var_ptrn()      = {ptrn.name} & syn_new_vars(ptrn.ptrn),
  tag_ptrn()      = syn_new_vars(ptrn.tag) & syn_new_vars(ptrn.obj);


Var* syn_new_vars(SynStmt stmt):
  assignment_stmt() = {stmt.var},
  if_stmt()         = {
    bodies := {b.body : b <- set(stmt.branches)} & {stmt.else};
    return intersection({syn_new_vars(ss) : ss <- bodies ; not never_falls_through(ss)});
  },
  let_stmt()        = syn_new_vars(stmt.body),                      
  _                 = {};


Var* syn_new_vars([<SynStmt, SynClause>*] objs) = seq_union([syn_new_vars(obj) : obj <- objs]);


Var* syn_new_vars(SynClause clause):
  in_clause()           = syn_new_vars(clause.ptrn),
  not_in_clause()       = {},
  map_in_clause()       = syn_new_vars(clause.key_ptrn) & syn_new_vars(clause.value_ptrn),
  map_not_in_clause()   = {},
  eq_clause()           = {clause.var},
  and_clause(cs)        = seq_union([syn_new_vars(c) : c <- cs]),
  or_clause()           = intersection(syn_new_vars(clause.left), syn_new_vars(clause.right));


Var* syn_new_vars(SynIter iter):
  seq_iter()    = {iter.var, iter.idx_var if iter.idx_var?},
  range_iter()  = {iter.var};


//## BAD: THIS IS ALMOST IDENTICAL TO partitions(Type)
using (TypeSymbol => SynType) typedefs
{
  ObjPartSet syn_partitions(SynType type):
    :atom_type      = {:symbols},
    symb_type(s)    = {partition(s)},
    IntType         = {:integers},
    //## BUG BUG BUG ASSUMING THERE ARE NO DIRECT CYCLES IN TYPEDEFS
    //## BUG BUG BUG ALSO ASSUMING NO TYPE REFERENCE IS "DANGLING"
    type_ref(ts)    = syn_partitions(typedefs[ts]),
    TypeVar         = all_objects,
    :empty_set_type = {:empty_set},
    ne_set_type()   = {:ne_sets},
    :empty_seq_type = {:empty_seq},
    ne_seq_type()   = {:ne_seqs},
    :empty_map_type = {:empty_map},
    ne_map_type()   = {:ne_maps},
    tuple_type(fs)  = match (fs)
                        <(label: SymbObj, type: SynType, optional: Bool)+>  = {:ne_maps, :empty_map if (? f <- fs : not f.optional)},
                        <(SymbObj => (type: SynType, optional: Bool))>      = {:ne_maps, :empty_map if (? l => f <- fs : not f.optional)};
                      ,
    union_type(ts)  = merge_partitions({syn_partitions(t) : t <- ts}),
    tag_obj_type()  = match (type.tag_type)
                        symb_type(object(a))  = {:tagged_obj(a)},
                        :atom_type            = {:tagged_objs},
                        TypeVar               = {:tagged_objs};
                      ;
}
