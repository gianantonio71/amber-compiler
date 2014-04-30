
type LeafType     = type_any,
                    atom_type,
                    empty_seq_type,
                    empty_set_type,
                    empty_map_type,
                    SymbType,
                    IntType;

//type LeafClause   = incl_clause(ptrn: Pattern, src: Expr),  // UGLY
//                    excl_clause(ptrn: Pattern, src: Expr);
//
////## FIND A BETTER NAME
//type NuType       = type_any, atom_type, empty_set_type, SymbType, IntType, SetType, TermType;

////////////////////////////////////////////////////////////////////////////////

Int max(<int_range(min: Int, size: NzNat)> t) = t.min + t.size - 1; //## BAD BAD

////////////////////////////////////////////////////////////////////////////////

//Bool separated(IntType t1, IntType t2):
//  :integer,     _            = false,
//  
//  low_ints(),   low_ints()   = false,
//  low_ints(),   high_ints()  = t2.min > t1.max + 1,
//  low_ints(),   int_range()  = t2.min > t1.max + 1,
//
//  high_ints(),  high_ints()  = false,
//  high_ints(),  int_range()  = t1.min > t2.min + t2.size,
//  
//  int_range(),  int_range()  = t1.min > t2.min + t2.size or t2.min > t1.min + t1.size,
//  
//  _,            _            = separated(t2, t1);
//
//////////////////////////////////////////////////////////////////////////////////

using (Any => Type) typedefs
{
  //// Types are supposed to have already passed the "no direct ref cycles" test
  //Bool are_compatible(Type t1, Type t2):
  //  IntType,          IntType         = separated(t1, t2),
  //  _,                _               = are_disjoint(partitions(t1), partitions(t2));

  //## REENABLE THE ABOVE IMPLEMENTATION AT SOME STAGE
  Bool are_compatible(Type t1, Type t2) = are_disjoint(partitions(t1), partitions(t2));

//  NuType* expand(Type type):
//    type_id(id)    = expand(type_map[id]),
//    union_type(ts) = union({expand(t) : t <- ts}),
//    _              = {type};
}

////////////////////////////////////////////////////////////////////////////////

//Type bool_type = :union_type({:singleton(:symbol(true)), :singleton(:symbol(false))});
//Type nat_type  = high_ints(min: 0);

////////////////////////////////////////////////////////////////////////////////

Var first_unused_int_var(Var *vars)
{
  i := 0;
  while (in(:unique_var(i), vars))
    i := i + 1;;
  return :unique_var(i);
}

//Var new_unique_var = :unique_var(_counter_(nil));

////////////////////////////////////////////////////////////////////////////////

//Bool empty_set_is_member(SetType type) = not {? b <- untag(type) ; in(b.card, {:required, :multiple})};

////////////////////////////////////////////////////////////////////////////////



//Nat arity(<FnDef, Signature> obj) = length(obj.params);
Nat arity(FnDef fd) = length(fd.params);

NzNat arity(ClsType t) = length(t.in_types);
Nat arity(Type)        = 0;

NzNat arity(ClsExpr e) = length(e.params);
Nat arity(Expr)        = 0;


Var* scalar_vars(FnDef fn_def) = {p.var : p <- set(fn_def.params) ; p.var? and (not p.type? or p.type :: Type)} &
                                 set([:fn_par(i) : p, i <- fn_def.params, not p.type? or p.type :: Type])       &
                                 {v : v => Type t <- fn_def.named_params};

//## FOR THE TIME BEING, THE fn_par(Nat) VARIABLES ARE DEFINED ONLY FOR SCALAR PARAMETERS, NOT CLOSURES
// THIS FUNCTION FAILS IF THERE ARE DUPLICATE PARAMETER NAMES. THIS IS CHECHED BEFORE THE FUNCTION IS INVOKED THOUGH
(Var => NzNat) cls_vars(FnDef fn_def) = (p.var => length(p.type.in_types) : p <- set(fn_def.params) ; p.var? and (p.type? and p.type :: ClsType)) &
                                        (v => length(t.in_types) : v => ClsType t <- fn_def.named_params);


//Bool is_def(Var cls_var, NzNat arity, (Var* => NzNat) cls_vars_in_scope) = has_key(cls_vars_in_scope, cls_var) and cls_vars_in_scope[cls_var] == arity;

Bool op_< (SymbObj s1, SymbObj s2) = lower_than(untag(s1), untag(s2));

Bool lower_than(Atom a1, Atom a2)
{
  str1 := _str_(a1);
  str2 := _str_(a2);
  
  len1 := length(str1);
  len2 := length(str2);
  
  //return len1 < len2 if len1 /= len2;
  return (len2 - len1) :: NzNat if len1 /= len2; //## BAD BAD BAD UGLY HACK TO WORK AROUND A BUG IN THE INTERPRETER
  
  for (ch1, i : untag(str1))
    ch2 := str2[i];
    //return ch1 < ch2 if ch1 /= ch2;
    return (ch2 - ch1) :: NzNat if ch1 /= ch2; //## BAD BAD BAD UGLY HACK TO WORK AROUND A BUG IN THE INTERPRETER
  ;
  
  fail;
}
