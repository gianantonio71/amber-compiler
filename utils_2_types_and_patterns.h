
AnonType user_type_to_anon_type(UserType type, (TypeName => AnonType) typedefs) = user_type_to_anon_type(type; typedefs=typedefs);

using (TypeName => AnonType) typedefs
{
  ClsType user_type_to_anon_type(UserClsType type) = cls_type([user_type_to_anon_type(t) : t <- type.in_types], user_type_to_anon_type(type.out_type));


  AnonType user_type_to_anon_type(UserType type): //## BAD: SHOULD BE USING A REPLACE EXPRESSION HERE...
    LeafType        = type,
    TypeVar         = type,
    type_ref(ts?)   = dereference_type_symbol(ts),
    ne_seq_type()   = ne_seq_type(user_type_to_anon_type(type.elem_type)),
    ne_set_type()   = ne_set_type(user_type_to_anon_type(type.elem_type)),
    ne_map_type()   = ne_map_type(user_type_to_anon_type(type.key_type), user_type_to_anon_type(type.value_type)),
    tuple_type(fs?) = tuple_type((l => (type: user_type_to_anon_type(f.type), optional: f.optional) : l => f <- fs)),
    tag_obj_type()  = tag_obj_type(type.tag_type, user_type_to_anon_type(type.obj_type)),
    union_type(ts?) = union_type({user_type_to_anon_type(t) : t <- ts});


  AnonType dereference_type_symbol(TypeSymbol type_symbol)
  {
    generic_type = typedefs[type_symb_to_name(type_symbol)];
    actual_params = [user_type_to_anon_type(tp) : tp <- params(type_symbol)];
    return instantiate_generic_params(generic_type, actual_params);
  }

  //## BAD: IS THIS THE SAME AS replace_type_vars()?
  AnonType instantiate_generic_params(AnonType generic_type, [AnonType] actual_params): //## BAD: SHOULD BE USING A REPLACE EXPRESSION HERE...
    LeafType          = generic_type,
    SelfPretype       = generic_type,
    type_var(n?)      = actual_params[n],
    ne_seq_type()     = ne_seq_type(instantiate_generic_params(generic_type.elem_type, actual_params)),
    ne_set_type()     = ne_set_type(instantiate_generic_params(generic_type.elem_type, actual_params)),
    ne_map_type()     = ne_map_type(instantiate_generic_params(generic_type.key_type, actual_params), instantiate_generic_params(generic_type.value_type, actual_params)),
    tuple_type(fs?)   = tuple_type((l => (type: instantiate_generic_params(f.type, actual_params), optional: f.optional) : l => f <- fs)),
    tag_obj_type()    = tag_obj_type(instantiate_generic_params(generic_type.tag_type, actual_params), instantiate_generic_params(generic_type.obj_type, actual_params)),
    union_type(ts?)   = union_type({instantiate_generic_params(t, actual_params) : t <- ts}),
    self_rec_type(t?) = self_rec_type(instantiate_generic_params(t, actual_params)),
    mut_rec_type()    = mut_rec_type(index: generic_type.index, types: [instantiate_generic_params(t, actual_params) : t <- generic_type.types]);
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

Bool type_can_be_converted_into_pattern(AnonType type):
  atom_type         = true,
  symb_type()       = true,
  IntType           = true,
  tag_obj_type()    = type_can_be_converted_into_pattern(type.obj_type),
  union_type(ts?)   = not (? t <- ts : not type_can_be_converted_into_pattern(t)),
  _                 = false;


Pattern type_to_pattern(AnonType type):
  atom_type         = ptrn_symbol,
  symb_type(s?)     = ptrn_symbol(s),
  IntType           = if type == integer then ptrn_integer else ptrn_integer(type) end,
  tag_obj_type()    = ptrn_tag_obj(type_to_pattern(type.tag_type), type_to_pattern(type.obj_type)),
  union_type(ts?)   = ptrn_union({type_to_pattern(t) : t <- ts}),
  _                 = ptrn_any;


Pattern type_to_pseudotype_pattern(AnonType type) = pseudotype_pattern(pseudotype(type));

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

PseudoType pseudotype(UserType type, (TypeName => AnonType) typedefs) = pseudotype(user_type_to_anon_type(type, typedefs));

Bool user_type_can_be_converted_into_pattern(UserType type, (TypeName => AnonType) typedefs) = type_can_be_converted_into_pattern(user_type_to_anon_type(type; typedefs=typedefs));

Pattern user_type_to_pattern(UserType type, (TypeName => AnonType) typedefs) = type_to_pattern(user_type_to_anon_type(type; typedefs=typedefs));

Pattern user_type_to_pseudotype_pattern(UserType type, (TypeName => AnonType) typedefs) = type_to_pseudotype_pattern(user_type_to_anon_type(type; typedefs=typedefs));