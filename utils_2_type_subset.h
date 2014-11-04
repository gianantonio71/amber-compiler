Bool is_subset(AnonType t1, AnonType t2) = is_subset_if(t1, t2; inst_type_vars=false) == {};

(TypeVar => AnonType*) subset_conds(AnonType t1, AnonType t2)
{
  cs = is_subset_if(t1, t2; inst_type_vars=true);
  assert cs :: <<subset_when(type_var: TypeVar, inst_type: AnonType)>*>;
  return merge_values({(c.type_var => c.inst_type) : c <- cs});
}

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

type IsSubset = not_a_subset, <subset_if(subset: SelfPretype, superset: AnonType), subset_when(type_var: TypeVar, inst_type: AnonType)>*;

IsSubset not_a_subset = :not_a_subset;
IsSubset subset_if(SelfPretype self, AnonType type) = {subset_if(subset: self, superset: type)};
IsSubset subset_when(TypeVar var, AnonType type)    = {subset_when(type_var: var, inst_type: type)};

IsSubset all_conds(IsSubset* iss) = if in(not_a_subset, iss) then not_a_subset else union(iss) end;

IsSubset at_least_one_cond(IsSubset *iss)
{
  red_iss = iss - {not_a_subset};
  assert size(red_iss) <= 1;
  return if red_iss == {} then not_a_subset else only_element(red_iss) end;
}

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

using Bool inst_type_vars
{
  IsSubset is_self_rec_subset_if(SelfRecType[AnonType] t1, AnonType t2)
  {
    tested_supertypes   = {};
    untested_supertypes = {t2};

    loop
      new_hypotheses = all_conds({is_subset_if(_obj_(t1), t) : t <- untested_supertypes});
      return not_a_subset if new_hypotheses == not_a_subset;
      assert not (? h <- new_hypotheses : h.subset /= self);
      tested_supertypes = tested_supertypes & untested_supertypes;
      untested_supertypes = {h.superset : h <- new_hypotheses} - tested_supertypes;
      return {} if untested_supertypes == {};
    ;
  }


  IsSubset is_mut_rec_subset_if(MutRecType[AnonType] t1, AnonType t2)
  {
    tested_hypotheses   = {};
    untested_hypotheses = {(subtype: t1, supertype: t2)};

    loop
      new_hypotheses = all_conds({is_subset_if(h.subtype.types[h.subtype.index], h.type) : h <- untested_hypotheses});
      return not_a_subset if new_hypotheses == not_a_subset;
      tested_hypotheses = tested_hypotheses & untested_hypotheses;
      // untested_hypotheses = {(subtype: )}
      return {} if untested_hypotheses == {};
    ;
  }


  IsSubset is_subset_if(AnonType t1, AnonType t2):
    // Type vars only match themselves or type any
    _,                    type_var()          = if inst_type_vars then subset_when(t2, t1) else if t1 == t2 then {} else not_a_subset end end,

    type_var(),           _                   = if is_type_any(t2) then {} else not_a_subset end,

    // Dealing with all the recursive stuff
    SelfPretype,          _                   = subset_if(t1, t2), //## BUG: HERE WE ALSO NEED TO KNOW WHAT THE self/self() TERMS EXPAND TO
    _,                    SelfPretype         = {fail;},

    self_rec_type(pt1?),  _                   = is_self_rec_subset_if(t1, t2),
    _,                    self_rec_type()     = is_subset_if(t1, unfold(t2)),

    mut_rec_type(),       _                   = {fail;},
    _,                    mut_rec_type()      = is_subset_if(t1, unfold(t2)),

    // Type unions now
    union_type(ts1?),     _                   = all_conds({is_subset_if(t, t2) : t <- ts1}),
    _,                    union_type(ts2?)    = at_least_one_cond({is_subset_if(t1, t) : t <- ts2}),   //## INEFFICIENT

    // Leaf types
    symb_type(),          _                   = if t1 == t2 or t2 == atom_type then {} else not_a_subset end,
    atom_type,            _                   = if t1 == t2 then {} else not_a_subset end,
    IntType,              IntType             = if is_integer_subset(t1, t2) then {} else not_a_subset end,
    IntType,              _                   = not_a_subset,

    // Sequence types
    empty_seq_type,       empty_seq_type      = {},
    empty_seq_type,       _                   = not_a_subset,

    ne_seq_type(),        ne_seq_type()       = is_subset_if(t1.elem_type, t2.elem_type),
    ne_seq_type(),        _                   = not_a_subset,

    // Set types
    empty_set_type,       empty_set_type      = {},
    empty_set_type,       _                   = not_a_subset,

    ne_set_type(),        ne_set_type()       = is_subset_if(t1.elem_type, t2.elem_type),
    ne_set_type(),           _                = not_a_subset,

    // Map types
    empty_map_type,       empty_map_type      = {},
    empty_map_type,       tuple_type(fs?)     = if not (? l => f <- fs : not f.optional) then {} else not_a_subset end,
    empty_map_type,       _                   = not_a_subset,

    ne_map_type(),        ne_map_type()       = all_conds({is_subset_if(t1.key_type, t2.key_type), is_subset_if(t1.value_type, t2.value_type)}),
    ne_map_type(),        tuple_type(fs?)     = is_ne_map_tuple_subset_if(t1.key_type, t1.value_type, fs),
    ne_map_type(),        _                   = not_a_subset,

    // Tuple types
    tuple_type(fs1?),     tuple_type(fs2?)    = is_tuple_subset_if(fs1, fs2),
    tuple_type(fs?),      ne_map_type()       = is_tuple_map_subset_if(fs, t2),
    tuple_type(),         _                   = not_a_subset,

    // Tagged types
    tag_obj_type(),       tag_obj_type()      = all_conds({is_subset_if(t1.tag_type, t2.tag_type), is_subset_if(t1.obj_type, t2.obj_type)}),
    tag_obj_type(),       _                   = not_a_subset;


  IsSubset is_tuple_subset_if((SymbObj => (type: AnonType, optional: Bool)) fs1, (SymbObj => (type: AnonType, optional: Bool)) fs2)
  {
    labels_1 = keys(fs1);
    labels_2 = keys(fs2);
    mandatory_labels_1 = {l : l => f <- fs1, not f.optional};
    mandatory_labels_2 = {l : l => f <- fs2, not f.optional};
    optional_labels_1  = labels_1 - mandatory_labels_1;
    optional_labels_2  = labels_2 - mandatory_labels_2;

    // Mandatory labels in the subtype must be present in the supertype (can be either mandatory or optional)
    return not_a_subset if not subset(mandatory_labels_1, mandatory_labels_2 & optional_labels_2);

    // Optional labels in the subtype must be optional in the supertype as well
    return not_a_subset if not subset(optional_labels_1, optional_labels_2);

    // Mandatory labels in the supertype must be mandatory in the subtype as well
    return not_a_subset if not subset(mandatory_labels_2, mandatory_labels_1);

    // No particular requirement for optional labels in the supertype

    label_type_map_1 = (l => f.type : l => f <- fs1);
    label_type_map_2 = (l => f.type : l => f <- fs2);

    return all_conds({is_subset_if(label_type_map_1[l], label_type_map_2[l]) : l <- labels_1});
  }


  IsSubset is_tuple_map_subset_if((SymbObj => (type: AnonType, optional: Bool)) tuple_fields, MapType[AnonType] map_type) =
    all_conds(
      for (l => f <- tuple_fields) {
        all_conds(
          { is_subset_if(symb_type(l), map_type.key_type),
            is_subset_if(f.type, map_type.value_type)
          }
        )
      }
    );


  IsSubset is_ne_map_tuple_subset_if(AnonType key_type, AnonType value_type, (SymbObj => (type: T, optional: Bool)) tuple_fields)
  {
    return not_a_subset if not is_subset(key_type, union_type({symb_type(l) : l => _ <- tuple_fields}));

    if (key_type :: SymbType)
      only_key_obj = _obj_(key_type);
      return not_a_subset if (? l => f <- tuple_fields : l /= only_key_obj, not f.optional);
    else
      return not_a_subset if (? _ => f <- tuple_fields : not f.optional);
    ;

    return all_conds({is_subset_if(key_type, f.type) : l => f <- tuple_fields, includes_symbol(key_type, l)});
  }
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

Bool is_integer_subset(IntType t1, IntType t2):
  _,            integer     = true,
  integer,      _           = false,

  high_ints(),  high_ints() = t1.min >= t2.min,
  high_ints(),  _           = false,

  low_ints(),   low_ints()  = t1.max <= t2.max,
  low_ints(),   _           = false,

  int_range(),  int_range() = t1.min >= t2.min and max(t1) <= max(t2),
  int_range(),  high_ints() = t1.min >= t2.min,
  int_range(),  low_ints()  = max(t1) <= t2.max;


////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

AnonType unfold(AnonType type, (SelfPretype => AnonType) sub_map):
  LeafType        = type,
  TypeVar         = type,
  SelfPretype     = sub_map[type],
  ne_seq_type()   = ne_seq_type(unfold(type.elem_type, sub_map)),
  ne_set_type()   = ne_set_type(unfold(type.elem_type, sub_map)),
  ne_map_type()   = ne_map_type(unfold(type.key_type, sub_map), unfold(type.value_type, sub_map)),
  tuple_type(fs?) = tuple_type((l => (type: unfold(f.type, sub_map), optional: f.optional) : l => f <- fs)),
  tag_obj_type()  = tag_obj_type(type.tag_type, unfold(type.obj_type, sub_map)),
  union_type(ts?) = union_type({unfold(t, sub_map) : t <- ts}),
  self_rec_type() = type,
  mut_rec_type()  = type;


AnonType unfold(AnonType type):
  self_rec_type(t?) = unfold(t, (self => type)),
  mut_rec_type()    = unfold(type.types[type.index], (self(i) => mut_rec_type(i, type.types) : i <- index_set(type.types))),
  _                 = type;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

Bool is_type_any(AnonType type) = is_subset(type_any, type);

AnonType type_bool = union_type({symb_type(true), symb_type(false)});

AnonType type_nat = high_ints(0);

AnonType type_seq = type_seq(type_any);
AnonType type_set = type_set(type_any);
AnonType type_map = type_map(type_any, type_any);

AnonType type_tagged_obj = tag_obj_type(atom_type, type_any);

AnonType type_seq(AnonType elem_type)  = union_type({empty_seq_type, ne_seq_type(elem_type)});
AnonType type_set(AnonType elem_type)  = union_type({empty_set_type, ne_set_type(elem_type)});
AnonType type_mset(AnonType elem_type) = union_type({empty_map_type, ne_map_type(elem_type, high_ints(1))});

AnonType type_map(AnonType key_type, AnonType value_type)  = union_type({empty_map_type, ne_map_type(key_type, value_type)});

AnonType type_string = tag_obj_type(symb_type(:string), union_type({empty_seq_type, ne_seq_type(type_nat)}));

AnonType type_any =
  self_rec_type(
    union_type({
      atom_type,
      integer,
      empty_seq_type,
      empty_set_type,
      empty_map_type,
      ne_seq_type(self),
      ne_set_type(self),
      ne_map_type(self, self),
      tag_obj_type(atom_type, self)
    })
  );


Bool includes_symbol(AnonType type, SymbObj symb) = is_subset(symb_type(symb), type);