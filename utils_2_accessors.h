
// type TupleType  = tuple_type((label: SymbObj, type: Type, optional: Bool)+);

ClosedType mandatory_tuple_field_type(TupleType[AnonType] type, SymbObj label)
{
	mfs := {f : l => f <- _obj_(type) ; l == label};
	assert size(mfs) >= 0;
	return void_type if mfs == {};
	mf := only_element(mfs);
	return if mf.optional then void_type else mf.type end;
}

Bool tuple_has_field(TupleType[AnonType] type, SymbObj label)
{
	//## IMPLEMENT
	fail;
}