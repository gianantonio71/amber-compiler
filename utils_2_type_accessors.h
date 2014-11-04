
Bool includes_atom_type(AnonType type) = is_subset(atom_type, type);

Bool includes_empty_set(AnonType type) = is_subset(empty_set_type, type);

Bool includes_empty_seq(AnonType type) = is_subset(empty_seq_type, type);

Bool includes_empty_map(AnonType type) = is_subset(empty_map_type, type);


SymbType* symb_types(AnonType type) = {t : symb_type() t <- expand_type(type)};

<IntType, void_type> int_type(AnonType type) = only_element_or_def_if_empty({t : t <- expand_type(type), t :: IntType}, void_type);


ClosedType seq_elem_type(AnonType type)
{
  elem_types = {t.elem_type : ne_seq_type() t <- expand_type(type)};
  return if elem_types == {} then void_type else union_type(elem_types) end;
}

ClosedType set_elem_type(AnonType type)
{
  elem_types = {t.elem_type : ne_set_type() t <- expand_type(type)};
  return if elem_types == {} then void_type else union_type(elem_types) end;
}

ClosedType map_key_type(AnonType type)            = only_element_or_def_if_empty({t.key_type : ne_map_type() t <- expand_type(type)}, void_type);

ClosedType map_value_type(AnonType type)          = only_element_or_def_if_empty({t.value_type : ne_map_type() t <- expand_type(type)}, void_type);

<TupleType[AnonType], void_type> tuple_type(AnonType type)  = only_element_or_def_if_empty({t : tuple_type() t <- expand_type(type)}, void_type);

TagObjType[AnonType]* tagged_obj_types(AnonType type) = {t : tag_obj_type() t <- expand_type(type)};
// {
//   res = {t : tag_obj_type() t <- expand_type(type)};
//   print "tagged_obj_types():";
//   print type;
//   print res;
//   return res;
// }

<SelfRecType[AnonType], MutRecType[AnonType]>* rec_types(AnonType type):
  self_rec_type()     = {type},
  mut_rec_type()      = {type},
  union_type(ts?)     = union({rec_types(t) : t <- ts}),
  _                   = {};

//////////////////////////////////////////////////////////////////////////////

Bool is_ne_seq_type(AnonType type) = not (? t <- expand_type(type) : not t :: <ne_seq_type(Any)>); //## SUPER UGLY

Bool is_ne_set_type(AnonType type) = not (? t <- expand_type(type) : not t :: <ne_set_type(Any)>); //## DITTO

Bool is_type_var(AnonType type)
{
  types = expand_type(type);
  type_vars = {t : type_var() t <- types}; //## SUPER UGLY
  other_types = types - type_vars;
  assert type_vars & other_types == types;
  assert size(type_vars) <= 1;
  return type_vars /= {} and other_types == {};
}

////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////

// AnonType+ expand_type(AnonType type)
// {
//   res = expand_type_impl(type);

//   print "expand_type():";
//   print type;
//   print res;

//   return res;
// }

AnonType+ expand_type(AnonType type):
  union_type(ts?)   = union({expand_type(t) : t <- ts}),
  self_rec_type(t?) = expand_type(replace_rec_refs(t, (self => type))),
  mut_rec_type()    = expand_type(replace_rec_refs(type.types[type.index], (self(i) => mut_rec_type(i, type.types) : i <- indexes(type.types)))),
  _                 = {type};

// AnonType replace_rec_refs2(AnonType type, (SelfPretype => AnonType) rec_map)
// {
//   print "replace_rec_refs():";
//   print type;
//   print rec_map;
//   print replace_rec_refs(type, rec_map);
//   return replace_rec_refs(type, rec_map);
// }

AnonType replace_rec_refs(AnonType type, (SelfPretype => AnonType) rec_map):
  SelfPretype     = rec_map[type],
  ne_seq_type()   = ne_seq_type(replace_rec_refs(type.elem_type, rec_map)),
  ne_set_type()   = ne_set_type(replace_rec_refs(type.elem_type, rec_map)),
  ne_map_type()   = ne_map_type(replace_rec_refs(type.key_type, rec_map), replace_rec_refs(type.value_type, rec_map)),
  tuple_type(fs?) = tuple_type((l => (type: replace_rec_refs(f.type, rec_map), optional: f.optional) : l => f <- fs)),
  tag_obj_type()  = tag_obj_type(type.tag_type, replace_rec_refs(type.obj_type, rec_map)),
  union_type(ts?) = union_type({replace_rec_refs(t, rec_map) : t <- ts}),
  _               = type;
