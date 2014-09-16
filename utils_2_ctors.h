
SymbObj object(Atom a) = :object(a);
LeafObj object(Int n) = :object(n);

////////////////////////////////////////////////////////////////////////////////

BasicTypeSymbol type_symbol(Atom a) = :type_symbol(a);

ParTypeSymbol par_type_symbol(BasicTypeSymbol s, [UserType+] ps) = par_type_symbol(symbol: s, params: ps);

TypeName type_name(BasicTypeSymbol ts, Nat arity) = type_name(symbol: ts, arity: arity);

////////////////////////////////////////////////////////////////////////////////

void_type = :void_type;

atom_type = :atom_type;

SymbType symb_type(SymbObj obj) = :symb_type(obj);
SymbType symb_type(Atom symbol) = :symb_type(:object(symbol));

IntType integer = :integer;
IntType low_ints(Int max) = low_ints(max: max);
IntType high_ints(Int min) = high_ints(min: min);
IntType int_range(Int min, Int max) = int_range(min: min, size: max-min+1); //## BUG: WHAT HAPPENS IF max IS LOWER THAN min?

TypeRef type_ref(TypeSymbol s) = :type_ref(s);

TypeVar type_var(<Atom, Nat> n) = :type_var(n);

empty_seq_type = :empty_seq_type;
empty_set_type = :empty_set_type;
empty_map_type = :empty_map_type;

NeSeqType[T] ne_seq_type(T elem_type) = ne_seq_type(elem_type: elem_type);

NeSetType[T] ne_set_type(T elem_type) = ne_set_type(elem_type: elem_type);

NeMapType[T] ne_map_type(T key_type, T value_type) = ne_map_type(key_type: key_type, value_type: value_type);

TupleType[T] tuple_type((SymbObj => (type: T, optional: Bool)) fs) = :tuple_type(fs);

TagObjType[T] tag_obj_type(TagType tag_type, T obj_type) = tag_obj_type(tag_type: tag_type, obj_type: obj_type);

AnonType map_type(T key_type, T value_type, Bool may_be_empty)
{
  type := ne_map_type(key_type, value_type);
  return if may_be_empty then union_type({type, empty_map_type}) else type end;
}

T union_type(T+ types) //## BAD: HERE I SHOULD CONSTRAIN THE TYPE OF T SO THAT IT IS A SUBTYPE OF Type, SelfRecPretype or MutRecPretype
{
  norm_types := union({expand_union_types(t) : t <- types});
  assert not (? union_type() <- norm_types);
  return if size(norm_types) > 1 then :union_type(norm_types) else only_element(norm_types) end;

  // res := if size(norm_types) > 1 then :union_type(norm_types) else only_element(norm_types) end;
  // if (not anon_type_is_wf(res))
  //   print "* * * * * * * * * * * * *";
  //   print res;
  // ;

  T* expand_union_types(T type):
		union_type(ts) 	= union({expand_union_types(t) : t <- ts}),
		_								= {type};
}

SelfPretype self        = :self;
SelfPretype self(Nat n) = :self(n);

SelfRecType[T] self_rec_type(T pretype)              = :self_rec_type(pretype);

MutRecType[T] mut_rec_type(Nat index, [T+] pretypes) = :mut_rec_type(index: index, types: pretypes);

////////////////////////////////////////////////////////////////////////////////

ClsType cls_type([AnonType+] in_types, AnonType out_type) = cls_type(in_types: in_types, out_type: out_type);

FnType fn_type([ExtType*] ps, AnonType rt) = fn_type(ps, (), rt);
FnType fn_type([ExtType*] ps, (<named_par(Atom)> => ExtType) nps, AnonType rt) = fn_type(params: ps, named_params: nps, ret_type: rt);

////////////////////////////////////////////////////////////////////////////////

Pattern ptrn_symbol                             = :ptrn_symbol;
Pattern ptrn_integer                            = :ptrn_integer;

Pattern ptrn_empty_set                          = :ptrn_empty_set;
Pattern ptrn_ne_set                             = :ptrn_ne_set;
Pattern ptrn_empty_seq                          = :ptrn_empty_seq;
Pattern ptrn_ne_seq                             = :ptrn_ne_seq;
Pattern ptrn_empty_map                          = :ptrn_empty_map;
Pattern ptrn_ne_map                             = :ptrn_ne_map;

Pattern ptrn_seq                                = ptrn_union({ptrn_empty_seq, ptrn_ne_seq});
Pattern ptrn_set                                = ptrn_union({ptrn_empty_set, ptrn_ne_set});
Pattern ptrn_map                                = ptrn_union({ptrn_empty_map, ptrn_ne_map});

Pattern ptrn_tag_obj                            = :ptrn_tag_obj;
Pattern ptrn_any                                = :ptrn_any;
Pattern ptrn_symbol(Atom a)                     = :ptrn_symbol(:object(a));
Pattern ptrn_symbol(SymbObj s)                  = :ptrn_symbol(s);
Pattern ptrn_integer(Int n)                     = ptrn_integer(int_range(n, n));
Pattern ptrn_integer(IntObj n)                  = ptrn_integer(_obj_(n));
Pattern ptrn_integer(IntType type)              = :ptrn_integer(type);
Pattern ptrn_tag_obj(TagPtrn tag, Pattern obj)  = ptrn_tag_obj(tag: tag, obj: obj);
Pattern ptrn_var(Var v, Pattern p)              = ptrn_var(var: v, ptrn: p);
Pattern ptrn_union(Pattern+ ps)                 = :ptrn_union(ps);

////////////////////////////////////////////////////////////////////////////////

FnSymbol fn_symbol(Atom a) = :fn_symbol(a);

Var fn_par(Nat n)     = :fn_par(n);
Var named_par(Atom a) = :named_par(a);

Expr fn_call(FnSymbol name, [ExtExpr*] params, (<named_par(Atom)> => ExtExpr) named_params) = fn_call(name: name, params: params, named_params: named_params);
Expr membership(Expr obj, UserType type) = membership(obj: obj, type: type);
Expr if_expr(Expr cond, Expr true_expr, Expr false_expr) = if_expr(cond: cond, then: true_expr, else: false_expr);

ClsExpr cls_expr([<var(Atom), nil>+] params, Expr expr) = cls_expr(params: params, expr: expr);
