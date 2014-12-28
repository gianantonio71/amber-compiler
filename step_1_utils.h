type BasicUntypedSgn  = untyped_sgn(name: FnSymbol, arity: Nat);

type UntypedSgn       = untyped_sgn(
                          name:         FnSymbol,
                          arity:        Nat,
                          named_params: BasicUntypedSgn+?
                        );

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

//BasicUntypedSgn untyped_sgn(Signature d) = untyped_sgn(
//                                             name:  d.name,
//                                             arity: arity(d)
//                                           );

//BasicUntypedSgn untyped_sgn(Var v, UserExtType t):
//  var(a), Type      = untyped_sgn(name: :fn_symbol(a), arity: 0),
//  var(a), UserClsType   = untyped_sgn(name: :fn_symbol(a), arity: length(t.in_types));


// BasicUntypedSgn untyped_sgn(<named_par(Atom)> var, UserExtType type):
//   named_par(a), UserType  = untyped_sgn(name: :fn_symbol(a), arity: 0),
//   named_par(a), UserClsType   = untyped_sgn(name: :fn_symbol(a), arity: length(type.in_types));

BasicUntypedSgn untyped_sgn(FnSymbol n, Nat a) = untyped_sgn(name: n, arity: a);

BasicUntypedSgn untyped_sgn(<named_par(Atom)> var, UserType type)    = untyped_sgn(name: :fn_symbol(_obj_(var)), arity: 0);
BasicUntypedSgn untyped_sgn(<named_par(Atom)> var, UserClsType type) = untyped_sgn(name: :fn_symbol(_obj_(var)), arity: length(type.in_types));

BasicUntypedSgn untyped_sgn(<var(Atom)> var, SynClsType type) = untyped_sgn(name: :fn_symbol(_obj_(var)), arity: length(type.in_types));

//BasicUntypedSgn* untyped_sgns((<named_par(Atom)> => UserExtType) nps) = {untyped_sgn(v, t) : v => t <- nps};

UntypedSgn untyped_sgn(FnDef fd) =
  untyped_sgn(
    name:         fd.name,
    arity:        arity(fd),
    named_params: untyped_sgns(fd.named_params) if fd.named_params /= ()
  );


// BasicUntypedSgn untyped_sgn(Var v, ExtExpr e):
//   var(a), Expr    = untyped_sgn(name: :fn_symbol(a), arity: 0),
//   var(a), ClsExpr = untyped_sgn(name: :fn_symbol(a), arity: length(e.params));

BasicUntypedSgn untyped_sgn(Var v, Expr e)    = untyped_sgn(name: :fn_symbol(_obj_(v)), arity: 0);
BasicUntypedSgn untyped_sgn(Var v, ClsExpr e) = untyped_sgn(name: :fn_symbol(_obj_(v)), arity: length(e.params));

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
  sgns = {s : s <- low_priority_sgns, not (? os <- high_priority_sgns : s.name == os.name, s.arity == os.arity)};
  return sgns & high_priority_sgns;
}

Nat arity(SynFnDef d) = length(d.params);

Nat arity(SynFnArg arg) =
  if arg.type?
    then
      match (arg.type)
        cls_type()  = length(arg.type.in_types),
        _           = 0;
    else 0
  end;

Bool is_def(FnSymbol name, Nat arity, UntypedSgn* env, BasicUntypedSgn* actual_named_params)
{
  return (? sgn <- env : could_match(name, arity, sgn, actual_named_params));
  
  Bool could_match(FnSymbol name, Nat arity, UntypedSgn sgn, BasicUntypedSgn* actual_named_params)
  {
    return false if sgn.name /= name or sgn.arity /= arity;
    //## IGNORING THE DIFFERENCE BETWEEN SCALARS AND CLOSURES FOR POSITIONAL PARAMETERS
    //## NOT SURE ABOUT NAMED PARAMETERS, I SEEM TO REMEMBERS THE ORIGINAL VERSION OF THIS FUNCTION (THE ONE THAT GOT DELETED) WAS DIFFERENT
    formal_named_params = if sgn.named_params? then sgn.named_params else {} end;
    return subset(formal_named_params, actual_named_params);
  }
}

//## FIND BETTER NAME
Bool is_almost_def(FnSymbol name, Nat arity, UntypedSgn* env) = (? s <- env : s.name == name, s.arity == arity);

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

Var* syn_new_vars(SynPtrn ptrn):
    ptrn_var()      = {ptrn.var} & syn_new_vars(ptrn.ptrn),
    ptrn_tag_obj()  = syn_new_vars(ptrn.tag) & syn_new_vars(ptrn.obj),
    _               = {};


Var* syn_new_vars(SynStmt stmt):
  assignment_stmt() = set(stmt.vars),
  if_stmt()         = {
    bodies = {b.body : b <- set(stmt.branches)} & {stmt.else};
    return intersection({syn_new_vars(ss) : ss <- bodies, not never_falls_through(ss)});
  },
  let_stmt()        = syn_new_vars(stmt.body),
  proc_call()       = {stmt.res_var if stmt.res_var?},
  _                 = {};


Var* syn_new_vars([<SynStmt, SynClause>] objs) = seq_union([syn_new_vars(obj) : obj <- objs]);


Var* syn_new_vars(SynClause clause):
  in_clause()           = syn_new_vars(clause.ptrn),
  map_in_clause()       = syn_new_vars(clause.key_ptrn) & syn_new_vars(clause.value_ptrn),
  eq_clause()           = {clause.var},
  and_clause(cs?)       = seq_union([syn_new_vars(c) : c <- cs]),
  or_clause()           = intersection(syn_new_vars(clause.left), syn_new_vars(clause.right));


Var* syn_new_vars(SynIter iter):
  seq_iter()    = set(iter.vars) & {iter.idx_var if iter.idx_var?},
  range_iter()  = {iter.var};

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

TypeSymbol syn_type_symbol_to_type_symbol(SynTypeSymbol ts):
  BasicTypeSymbol   = ts,
  par_type_symbol() = par_type_symbol(ts.symbol, [syn_type_to_user_type(p) : p <- ts.params]);


UserType syn_type_to_user_type(SynType type):
  LeafType                = type,
  TypeVar                 = type,
  type_ref(ts?)           = type_ref(syn_type_symbol_to_type_symbol(ts)),
  syn_int_range()         = int_range(type.min, type.max),
  ne_seq_type()           = ne_seq_type(syn_type_to_user_type(type.elem_type)),
  ne_set_type()           = ne_set_type(syn_type_to_user_type(type.elem_type)),
  ne_map_type()           = ne_map_type(syn_type_to_user_type(type.key_type), syn_type_to_user_type(type.value_type)),
  record_type([...] fs?)  = record_type((f.label => (type: syn_type_to_user_type(f.type), optional: f.optional) : f <- set(fs))),
  record_type((...))      = type,
  tuple_type(ts?)         = tuple_type([syn_type_to_user_type(t) : t <- ts]),
  tag_obj_type()          = tag_obj_type(type.tag_type, syn_type_to_user_type(type.obj_type)),
  union_type(ts?)         = union_type({syn_type_to_user_type(t) : t <- ts}),
  syn_union_type(ts?)     = union_type({syn_type_to_user_type(t) : t <- set(ts)});

UserExtType syn_type_to_user_type(SynClsType type) =
  user_cls_type([syn_type_to_user_type(t) : t <- type.in_types], syn_type_to_user_type(type.out_type));

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

// PseudoType syn_pseudotype(SynType type, (TypeName => AnonType) typedefs) = pseudotype(syn_type_to_user_type(type), typedefs);
// PseudoType syn_pseudotype(SynType type, (TypeName => AnonType) typedefs) = pseudotype(UserType(type), typedefs);

//## BAD: THIS SHOULD BE IMPLEMENTED AS SHOWN ABOVE. IT IS STILL IN USE ONLY BECAUSE ALL THE LEVEL 1 ERROR
//## CHECKING CODE HAS TO BE REWRITTEN FROM SCRATCH AND IT DOESN'T MAKE ANY SENSE TO CHANGE IT NOW
using (SynTypeSymbol => SynType) typedefs
{
  PseudoType syn_pseudotype(SynType type):
    LeafType                = pseudotype(type),
    syn_int_range()         = pseudotype_integers,
    //## BUG BUG BUG ASSUMING THERE ARE NO DIRECT CYCLES IN TYPEDEFS
    //## BUG BUG BUG ALSO ASSUMING NO TYPE REFERENCE IS "DANGLING"
    type_ref(ts?)           = syn_pseudotype(typedefs[ts]),
    TypeVar                 = pseudotype_any,
    ne_set_type()           = pseudotype_ne_seqs,
    ne_seq_type()           = pseudotype_ne_sets,
    ne_map_type()           = pseudotype_ne_maps,
    record_type((...) fs?)  = pseudotype_union({pseudotype_ne_maps, pseudotype_empty_map if (? l => f <- fs : not f.optional)}),
    record_type()           = syn_pseudotype(syn_type_to_user_type(type)),
    tuple_type()            = pseudotype_ne_seqs,
    union_type(ts?)         = pseudotype_union({syn_pseudotype(t) : t <- ts}),
    syn_union_type(ts?)     = pseudotype_union({syn_pseudotype(t) : t <- set(ts)}),
    tag_obj_type()          = match (type.tag_type)
                                symb_type(object(a?)) = pseudotype_tag_obj(a),
                                atom_type             = pseudotype_tag_objs;
                              ;
}
