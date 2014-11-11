
[UserType] params(TypeSymbol ts):
  type_symbol()     = [],
  par_type_symbol() = ts.params;


Int max(<int_range(min: Int, size: NzNat)> t) = t.min + t.size - 1; //## BAD BAD
Int max(<low_ints(max: Int)> t) = t.max;


TypeName type_symb_to_name(TypeSymbol ts):
  type_symbol()     = type_name(symbol: ts, arity: 0),
  par_type_symbol() = type_name(symbol: ts.symbol, arity: length(ts.params));


Bool are_compatible(UserType t1, UserType t2, (TypeName => AnonType) typedefs) = are_disjoint(pseudotype(t1, typedefs), pseudotype(t2, typedefs));


Bool anon_types_are_compatible(AnonType t1, AnonType t2) = anon_types_are_compatible(t1, t2, ());

//## BAD: I REALLY DON'T LIKE THIS FUNCTION. ISN'T THERE A WAY NOT TO USE IT?
Bool anon_types_are_compatible(AnonType t1, AnonType t2, (SelfPretype => PseudoType) self_pseudotypes) =
  are_disjoint(pretype_pseudotype(t1, self_pseudotypes), pretype_pseudotype(t2, self_pseudotypes));

////////////////////////////////////////////////////////////////////////////////

Var first_unused_int_var(Var *vars)
{
  i = 0;
  while (in(:unique_var(i), vars))
    i = i + 1;;
  return :unique_var(i);
}

////////////////////////////////////////////////////////////////////////////////

//Nat arity(<FnDef, Signature> obj) = length(obj.params);
Nat arity(FnDef fd) = length(fd.params);

NzNat arity(UserClsType t) = length(t.in_types);
Nat arity(UserType)        = 0;

NzNat arity(ClsExpr e) = length(e.params);
Nat arity(Expr)        = 0;


Var* scalar_vars(FnDef fn_def) = {p.var : p <- set(fn_def.params), p.var? and (not p.type? or p.type :: UserType)} &
                                 set([:fn_par(i) : p @ i <- fn_def.params, not p.type? or p.type :: UserType])       &
                                 {v : v => t <- fn_def.named_params, t :: UserType};

//## FOR THE TIME BEING, THE fn_par(Nat) VARIABLES ARE DEFINED ONLY FOR SCALAR PARAMETERS, NOT CLOSURES
// THIS FUNCTION FAILS IF THERE ARE DUPLICATE PARAMETER NAMES. THIS IS CHECHED BEFORE THE FUNCTION IS INVOKED THOUGH
(Var => NzNat) cls_vars(FnDef fn_def) = (p.var => length(p.type.in_types) : p <- set(fn_def.params), p.var? and (p.type? and p.type :: UserClsType)) &
                                        (v => length(t.in_types) : v => t <- fn_def.named_params, t :: UserClsType);


Bool (_<_) (SymbObj s1, SymbObj s2) = lower_than(_obj_(s1), _obj_(s2));

Bool lower_than(Atom a1, Atom a2)
{
  str1 = _str_(a1);
  str2 = _str_(a2);
  
  len1 = length(str1);
  len2 = length(str2);
  
  //return len1 < len2 if len1 /= len2;
  return (len2 - len1) :: NzNat if len1 /= len2; //## BAD BAD BAD UGLY HACK TO WORK AROUND A BUG IN THE INTERPRETER
  
  for (ch1 @ i : _obj_(str1))
    ch2 = str2[i];
    //return ch1 < ch2 if ch1 /= ch2;
    return (ch2 - ch1) :: NzNat if ch1 /= ch2; //## BAD BAD BAD UGLY HACK TO WORK AROUND A BUG IN THE INTERPRETER
  ;
  
  fail;
}
