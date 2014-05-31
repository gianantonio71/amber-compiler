
BasicTypeSymbol type_symbol(Atom a) = :type_symbol(a);

ParTypeSymbol par_type_symbol(BasicTypeSymbol s, [Type+] ps) = par_type_symbol(symbol: s, params: ps);

////////////////////////////////////////////////////////////////////////////////

void_type = :void_type;

atom_type = :atom_type;

SymbType symb_type(SymbObj obj) = :symb_type(obj);
SymbType symb_type(Atom symbol) = :symb_type(:object(symbol));

IntType integer = :integer;
IntType low_ints(Int max) = low_ints(max: max);
IntType high_ints(Int min) = high_ints(min: min);
IntType int_range(Int min, Int max) = int_range(min: min, size: max-min+1);

TypeRef type_ref(TypeSymbol s) = :type_ref(s);

TypeVar type_var(Atom n) = :type_var(n);

empty_seq_type = :empty_seq_type;
empty_set_type = :empty_set_type;
empty_map_type = :empty_map_type;

NeSeqType[T] ne_seq_type(T elem_type) = ne_seq_type(elem_type: elem_type);

NeSetType[T] ne_set_type(T elem_type) = ne_set_type(elem_type: elem_type);

NeMapType[T] ne_map_type(T key_type, T value_type) = ne_map_type(key_type: key_type, value_type: value_type);

TupleType[T] tuple_type((SymbObj => (type: T, optional: Bool)) fs) = :tuple_type(fs);

TagObjType[T] tag_obj_type(TagType tag_type, T obj_type) = tag_obj_type(tag_type: tag_type, obj_type: obj_type);

UnionType[T] union_type(T+ types) //## BAD: HERE I SHOULD CONSTRAIN THE TYPE OF T SO THAT IT IS A SUBTYPE OF Type, SelfRecPretype or MutRecPretype
{
  norm_types := union({expand_union_types(t) : t <- types});
  assert not (? union_type() <- norm_types);
  return :union_type(norm_types);

  T* expand_union_types(T type):
		union_type(ts) 	= union({expand_union_types(t) : t <- ts}),
		_								= {type};


	// Type norm_type(SynType type)
	// {
	//   return replace UnionType t in type with norm_union_type(t) end;

	//   Type norm_union_type(UnionType utype)
	//   {
	//     ts := {norm_type(t) : t <- rem_nesting(utype)};
	//     return if size(ts) > 1 then :union_type(ts) else only_element(ts) end;
	//   }

	//   //## BAD NAME
	//   Type* rem_nesting(Type type):
	//     union_type(ts)  = union({rem_nesting(t) : t <- ts}),
	//     _               = {type};
	// }

}

SelfRecType[T] self_rec_type(T pretype)              = self_rec_type(pretype);

MutRecType[T] mut_rec_type(Nat index, [T+] pretypes) = mut_rec_type(index: index, types: pretypes);

////////////////////////////////////////////////////////////////////////////////

Var fn_par(Nat n)      = :fn_par(n);
