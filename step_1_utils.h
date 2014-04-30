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

//BasicUntypedSgn untyped_sgn(Var v, ExtType t):
//  var(a), Type      = untyped_sgn(name: :fn_symbol(a), arity: 0),
//  var(a), ClsType   = untyped_sgn(name: :fn_symbol(a), arity: length(t.in_types));


BasicUntypedSgn untyped_sgn(<named_par(Atom)> var, ExtType type):
  named_par(a), Type    = untyped_sgn(name: :fn_symbol(a), arity: 0),
  named_par(a), ClsType = untyped_sgn(name: :fn_symbol(a), arity: length(type.in_types));

//BasicUntypedSgn* untyped_sgns((<named_par(Atom)> => ExtType) nps) = {untyped_sgn(v, t) : v => t <- nps};

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
BasicUntypedSgn* untyped_sgns((<named_par(Atom)> => <ExtType, ExtExpr>) nps) = {untyped_sgn(v, type_or_expr) : v => type_or_expr <- nps};

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

Var* syn_new_vars(SynStmt stmt):
  assignment_stmt() = {stmt.var},
  if_stmt()         = intersection(
                        {syn_new_vars(b.body) : b <- set(stmt.branches)} & {syn_new_vars(stmt.else)}
                      ),
  let_stmt()        = syn_new_vars(stmt.body),                      
  _                 = {};


Var* syn_new_vars([<SynStmt, SynClause>*] objs) = seq_union([syn_new_vars(obj) : obj <- objs]);


Var* syn_new_vars(SynClause clause):
  in_clause()           = new_vars(clause.ptrn),
  not_in_clause()       = {},
  map_in_clause()       = new_vars(clause.key_ptrn) & new_vars(clause.value_ptrn),
  map_not_in_clause()   = {},
  eq_clause()           = {clause.var},
  and_clause(cs)        = seq_union([syn_new_vars(c) : c <- cs]),
  or_clause()           = intersection(syn_new_vars(clause.left), syn_new_vars(clause.right));


Var* syn_new_vars(SynIter iter):
  seq_iter()    = {iter.var, iter.idx_var if iter.idx_var?},
  range_iter()  = {iter.var};

