
ClosedType mandatory_record_field_type(RecordType[AnonType] type, SymbObj label)
{
	mfs = {f : l => f <- _obj_(type), l == label};
	assert size(mfs) >= 0;
	return void_type if mfs == {};
	mf = only_element(mfs);
	return if mf.optional then void_type else mf.type end;
}

Bool record_has_field(RecordType[AnonType] type, SymbObj label)
{
	//## IMPLEMENT
	fail;
}