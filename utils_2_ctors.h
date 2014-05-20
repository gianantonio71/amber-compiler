
BasicTypeSymbol type_symbol(Atom a) = :type_symbol(a);

ParTypeSymbol par_type_symbol(BasicTypeSymbol s, [Type+] ps) = par_type_symbol(symbol: s, params: ps);

////////////////////////////////////////////////////////////////////////////////

Type atom_type = :atom_type;

SymbType symb_type(SymbObj obj) = :symb_type(obj);
SymbType symb_type(Atom symbol) = :symb_type(:object(symbol));

IntType integer = :integer;
IntType low_ints(Int max) = low_ints(max: max);
IntType high_ints(Int min) = high_ints(min: min);
IntType int_range(Int min, Int max) = int_range(min: min, size: max-min+1);

TypeRef type_ref(TypeSymbol s) = :type_ref(s);

TypeVar type_var(Atom n) = :type_var(n);

SeqType empty_seq_type = :empty_seq_type;
SeqType ne_seq_type(Type elem_type) = ne_seq_type(elem_type: elem_type);

SetType empty_set_type = :empty_set_type;
SetType ne_set_type(Type elem_type) = ne_set_type(elem_type: elem_type);

MapType empty_map_type = :empty_map_type;
MapType ne_map_type(Type key_type, Type value_type) = ne_map_type(key_type: key_type, value_type: value_type);

TupleType tuple_type((label: SymbObj, type: Type, optional: Bool)+ fs) = :tuple_type(fs);

TagObjType tag_obj_type(TagType tag_type, Type obj_type) = tag_obj_type(tag_type: tag_type, obj_type: obj_type);

UnionType union_type(Type+ types)
{
	assert not (? union_type() <- types); //## TEMPORARY HACK. IMPLEMENT PROPERLY
	return :union_type(types);
}

////////////////////////////////////////////////////////////////////////////////

Var fn_par(Nat n)      = :fn_par(n);
