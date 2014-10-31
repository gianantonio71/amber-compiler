Bool union_superset(AnonType t1, AnonType t2) = union_superset({t1, t2});
Bool union_superset(AnonType+ types) = union_superset_impl(types; allow_incompatible_groups=false);


type Pretype = LeafType, TypeVar, SelfPretype, CompType[AnonType], UnionType[AnonType], RecType[AnonType], UnionPretype;

type UnionPretype = union_pretype(AnonType+);


UnionPretype union_pretype(AnonType+ types)
{
  assert size(types) > 1;
  return :union_pretype(types);
}


AnonType rec_type_union_superset(AnonType* types)
{
  pre_unions := ();
  type_sets_to_do := {types};

  while (type_sets_to_do /= {})
    pre_unions := pre_unions & (ts => union_superset_impl({unfold(t) : t <- ts}; allow_incompatible_groups=true) : ts <- type_sets_to_do);
    type_sets_to_do := union({illegal_unions(pu) : _ => pu <- pre_unions}) - keys(pre_unions);

  ;

  final_unions := ();
  pre_unions_left := pre_unions;
  types_left := keys(pre_unions);
  while (types_left /= {})
    cs := clusters(pre_unions_left);
    ncs := {normalize(c, pre_unions_left) : c <- cs};
    new_final_unions := merge(ncs);
    final_unions := final_unions & new_final_unions;
    types_left := types_left - keys(new_final_unions);
    pre_unions_left := (ts => replace_final_preunions(pre_unions_left[ts], final_unions) : ts <- types_left);
  ;

  return final_unions[types];


  (AnonType+ => AnonType) normalize(AnonType++ cluster, (AnonType+ => Pretype) pre_unions)
  {
    if (size(cluster) == 1)
      ts := only_element(cluster);
      type := replace_preunions(pre_unions[ts], (ts => self));
      type := self_rec_type(type) if has_rec_branches(type);
      return (ts => type);
    ;

    sort_type_sets := rand_sort(cluster);
    rec_map := (sort_type_sets[i] => self(i) : i <- index_set(sort_type_sets));
    types := [replace_preunions(pre_unions[ts], rec_map) : ts <- sort_type_sets];
    return (sort_type_sets[i] => mut_rec_type(i, types) : i <- index_set(sort_type_sets));
  }


  // AnonType replace_preunions(Pretype pretype, (AnonType+ => SelfPretype) rec_map) = replace union_pretype(ts) in pretype with rec_map[ts] end;

  //## replace_preunions() AND replace_final_unions() ARE SO SIMILAR. ISN'T THERE A WAY OF MERGING THEM?

  //## THERE MUST BE A BETTER WAY EVEN WITHOUT A REPLACE INSTRUCTION...
  AnonType replace_preunions(Pretype pretype, (AnonType+ => SelfPretype) rec_map):
    LeafType            = pretype,
    TypeVar             = pretype,
    SelfPretype         = pretype,
    ne_seq_type()       = ne_seq_type(replace_preunions(pretype.elem_type, rec_map)),
    ne_set_type()       = ne_set_type(replace_preunions(pretype.elem_type, rec_map)),
    ne_map_type()       = ne_map_type(replace_preunions(pretype.key_type, rec_map), replace_preunions(pretype.value_type, rec_map)),
    tuple_type(fs?)     = tuple_type((l => (type: replace_preunions(f.type, rec_map), optional: f.optional) : l => f <- fs)),
    tag_obj_type()      = tag_obj_type(pretype.tag_type, replace_preunions(pretype.obj_type, rec_map)),
    union_type(ts?)     = union_type({replace_preunions(t, rec_map) : t <- ts}),
    union_pretype(ts?)  = rec_map[ts],
    self_rec_type(t?)   = self_rec_type(replace_preunions(t, rec_map)),
    mut_rec_type()      = mut_rec_type(pretype.index, [replace_preunions(t, rec_map) : t <- pretype.types]);

  // Pretype replace_final_preunions(Pretype pretype, (AnonType+ => AnonType) final_unions) =
  //   replace union_pretype(ts) pt
  //   in pretype
  //   with lookup(final_unions, ts, pt) end; //## WHY DO WE HAVE TO PROVIDE A DEFAULT HERE? I CAN'T REMEMBER...

  //## THERE MUST BE A BETTER WAY EVEN WITHOUT A REPLACE INSTRUCTION...
  Pretype replace_final_preunions(Pretype pretype, (AnonType+ => AnonType) final_unions):
    LeafType            = pretype,
    TypeVar             = pretype,
    SelfPretype         = pretype,
    ne_seq_type()       = ne_seq_type(replace_final_preunions(pretype.elem_type, final_unions)),
    ne_set_type()       = ne_set_type(replace_final_preunions(pretype.elem_type, final_unions)),
    ne_map_type()       = ne_map_type(replace_final_preunions(pretype.key_type, final_unions), replace_final_preunions(pretype.value_type, final_unions)),
    tuple_type(fs?)     = tuple_type((l => (type: replace_final_preunions(f.type, final_unions), optional: f.optional) : l => f <- fs)),
    tag_obj_type()      = tag_obj_type(pretype.tag_type, replace_final_preunions(pretype.obj_type, final_unions)),
    union_type(ts?)     = union_type({replace_final_preunions(t, final_unions) : t <- ts}),
    union_pretype(ts?)  = lookup(final_unions, ts, pretype), //## WHY DO WE HAVE TO PROVIDE A DEFAULT HERE? I CAN'T REMEMBER...
    self_rec_type(t?)   = self_rec_type(replace_final_preunions(t, final_unions)),
    mut_rec_type()      = mut_rec_type(pretype.index, [replace_final_preunions(t, final_unions) : t <- pretype.types]);

  AnonType+** clusters((AnonType+ => Pretype) pre_unions)
  {
    ref_map        := (ts => illegal_unions(pu) : ts => pu <- pre_unions);
    deep_ref_map   := transitive_closure(ref_map);
    conn_comps     := {{s} & ss : s => ss <- deep_ref_map};
    min_conn_comps := {c1 : c1 <- conn_comps ; not (? c2 <- conn_comps : c1 /= c2, subset(c2, c1))};
    return min_conn_comps;
  }

  // AnonType+* illegal_unions(Pretype pretype) = retrieve ts from union_pretype(ts) in pretype end;
  AnonType+* illegal_unions(Pretype pretype) = {_obj_(pt) : pt <- select UnionPretype in pretype end}; //## THE ABOVE VERSION WITH RETRIEVE WAS LESS UGLY
}

using Bool allow_incompatible_groups
{
  Pretype union_superset_impl(AnonType+ types)
  {
    exp_types := union({expand_union_type(t) : t <- types});

    //## TODO: DEAL WITH RECURSIVE TYPES, RECURSIVE REFERENCES AND TYPE VARIABLES HERE
    assert not (? union_type() <- exp_types);

    return only_element(exp_types, type_any) if (? t <- exp_types : t :: TypeVar);

    rec_types := {t : self_rec_type() t <- exp_types};
    exp_types := exp_types - rec_types;


    assert exp_types :: <<LeafType, CompType[AnonType]>+>;

    types_by_group := merge_values({(type_group(t) => t) : t <- exp_types});

    res_types := union({
      {atom_type}                                           if types_by_group.atom?,
      types_by_group.symb                                   if types_by_group.symb? and not types_by_group.atom?,
      {int_types_union_superset(types_by_group.int)}        if types_by_group.int?,
      {empty_seq_type}                                      if types_by_group.empty_seq?,
      {seq_types_union_superset(types_by_group.ne_seq)}     if types_by_group.ne_seq?,
      {empty_set_type}                                      if types_by_group.empty_set?,
      {set_types_union_superset(types_by_group.ne_set)}     if types_by_group.ne_set?,
      tag_obj_types_union_superset(types_by_group.tag_obj)  if types_by_group.tag_obj?
    });

    if (types_by_group.ne_map?)
      res_ne_map_type := map_types_union_superset(types_by_group.ne_map);
      if (types_by_group.tuple?)
        res_tuple_type := tuple_types_union_superset(types_by_group.tuple);
        res_map_types := map_tuple_union_superset(res_ne_map_type, res_tuple_type, types_by_group.empty_map?);
      else
        res_map_types := {res_ne_map_type, empty_map_type if types_by_group.empty_map?};
      ;
    else
      if (types_by_group.tuple?)
        res_tuple_type := tuple_types_union_superset(types_by_group.tuple);
        if (types_by_group.empty_map?)
          res_tuple_type := tuple_type((l => (type: f.type, optional: true) : l => f <- _obj_(res_tuple_type)));
        ;
        res_map_types := {res_tuple_type};
      else
        res_map_types := {empty_map_type if types_by_group.empty_map?};
      ;
    ;

    res_types := res_types & res_map_types;

    // assert not (? t <- res_types : not anon_type_is_wf(t));
    // assert not (? t1 <- res_types, t2 <- res_types : t1 /= t2 and not anon_types_are_compatible(t1, t2));

    type_groups := group_types_by_incompatibility(res_types & rec_types);

    standalone_types := {only_element(g) : g <- type_groups ; size(g) == 1};  //## BAD: DOING MULTIPLE PASSES OVER THE SET IN ORDER TO PARTITION IT
    incompatible_groups := {g : g <- type_groups ; size(g) > 1};              //## BAD: DITTO

    if (allow_incompatible_groups)
      illegal_unions := {union_pretype(g) : g <- incompatible_groups};
      return union_type(standalone_types & illegal_unions);
    ;

    reformed_unions := {rec_type_union_superset(g) : g <- incompatible_groups};
    return union_type(standalone_types & reformed_unions);


    AnonType+ expand_union_type(type):
      union_type(ts?) = union({expand_union_type(t) : t <- ts}),
      _               = {type};


    type_group(AnonType type):
      atom_type         = :atom,
      SymbType          = :symb,
      IntType           = :int,
      empty_seq_type    = :empty_seq,
      empty_set_type    = :empty_set,
      empty_map_type    = :empty_map,
      ne_seq_type()     = :ne_seq,
      ne_set_type()     = :ne_set,
      ne_map_type()     = :ne_map,
      tuple_type()      = :tuple,
      tag_obj_type()    = :tag_obj;


    AnonType** group_types_by_incompatibility(AnonType* types)
    {
      inc_map := (t1 => {t2 : t2 <- types ; not anon_types_are_compatible(t1, t2)} : t1 <- types);
      return values(transitive_closure(inc_map));
    }
  }


  IntType int_types_union_superset(IntType+ int_types)
  {
    if (in(:integer, int_types) or (? low_ints() <- int_types, high_ints() <- int_types)) //## NOT SURE ABOUT THIS ONE
      return :integer;
    elif ((? low_ints() <- int_types))
      max_val := max({max(t) : t <- int_types});
      return low_ints(max: max_val);
    elif ((? high_ints() <- int_types))
      min_val := min({t.min : t <- int_types});
      return high_ints(min: min_val);
    else
      max_val := max({max(t) : t <- int_types});  //## IMPLEMENT max(Int+)
      min_val := min({t.min  : t <- int_types});  //## IMPLEMENT min(Int+)
      return int_range(min_val, max_val);
    ;
  }


  NeSeqType[AnonType] seq_types_union_superset(NeSeqType[AnonType]+ types) = ne_seq_type(union_superset_impl({t.elem_type : t <- types}));

  NeSetType[AnonType] set_types_union_superset(NeSetType[AnonType]+ types) = ne_set_type(union_superset_impl({t.elem_type : t <- types}));

  NeMapType[AnonType] map_types_union_superset(NeMapType[AnonType]+ types) = ne_map_type(union_superset_impl({t.key_type : t <- types}), union_superset_impl({t.value_type : t <- types}));


  TupleType[AnonType] tuple_types_union_superset(TupleType[AnonType]+ tuple_types)
  {
    fields_by_label := merge_values({fm : tuple_type(fm) <- tuple_types});
    res_fields := for (l => fs <- fields_by_label) (
      l => (type: union_superset_impl({f.type : f <- fs}), optional: (? f <- fs : f.optional) or (? tuple_type(fm) <- tuple_types : not has_key(fm, l)))
    );
    return tuple_type(res_fields);
  }


  AnonType+ map_tuple_union_superset(MapType[AnonType] map_type, TupleType[AnonType] tuple_type, Bool includes_empty_map)
  {
    fields := _obj_(tuple_type);
    res_key_type := union_superset_impl({map_type.key_type, union_type({symb_type(l) : l => f <- fields})});
    res_value_type := union_superset_impl({map_type.value_type} & {f.type : l => f <- fields});
    res_map_type := ne_map_type(res_key_type, res_value_type);
    needs_empty_map := includes_empty_map or not (? l => f <- fields : not f.optional);
    return if needs_empty_map then {empty_map_type, res_map_type} else {res_map_type} end;
  }


  TagObjType[AnonType]+ tag_obj_types_union_superset(TagObjType[AnonType]+ tagged_types)
  {
    tag_types := {t.tag_type : t <- tagged_types};
    if (in(atom_type, tag_types))
      return {tag_obj_type(atom_type, union_superset_impl({t.obj_type : t <- tagged_types}))};
    else
      assert tag_types :: <SymbType+>;
      tag_to_obj_types := merge_values({(t.tag_type => t.obj_type) : t <- tagged_types});
      return {tag_obj_type(tt, union_superset_impl(ots)) : tt => ots <- tag_to_obj_types};
    ;
  }
}

////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////

// The result must be a subset of the first type but not necessarily of the second.
ClosedType intersection_superset(ClosedType type1, ClosedType type2) = intersection_superset_implementation(type1, type2; already_expanded_rec_types={});

using AnonType* already_expanded_rec_types
{
  ClosedType intersection_superset_implementation(ClosedType type1, ClosedType type2) //## FIND BETTER NAME
  {
    return type1 if type1 == type2;

    return void_type if type1 == void_type or type2 == void_type;

    // Type vars can be instantiated to match any type, so in order to be safe, we must consider the worst case
    //## CAN WE IMPROVE ON THIS SOMEHOW?
    return type1 if is_type_var(type1) or is_type_var(type2);

    nu_types_1 := match(type1)
                    union_type(ts?) = ts,
                    _               = {type1};
                  ;
    rec_types_1 := {t : self_rec_type() t <- nu_types_1} & {t : mut_rec_type() t <- nu_types_1}; //## BAD: WE SHOULD USE A PATTERN UNION HERE, ONCE IT IS IMPLEMENTED
    return type1 if not disjoint(rec_types_1, already_expanded_rec_types);

    let (already_expanded_rec_types = already_expanded_rec_types & rec_types_1)
      res := {};

      // Symbols
      if (includes_atom_type(type1))
        if (includes_atom_type(type2))
          res := res & {atom_type};
        else
          res := res & symb_types(type2);
        ;
      else
        if (includes_atom_type(type2))
          res := res & symb_types(type1);
        else
          res := res & intersection(symb_types(type1), symb_types(type2));
        ;
      ;

      // Integers
      int_type_1 := int_type(type1);
      int_type_2 := int_type(type2);
      res := res & {int_types_intersection(int_type_1, int_type_2)} if int_type_1 /= void_type and int_type_2 /= void_type;

      // Sequences
      res := res & {empty_seq_type} if includes_empty_seq(type1) and includes_empty_seq(type2);

      seq_elem_type_1 := seq_elem_type(type1);
      seq_elem_type_2 := seq_elem_type(type2);
      res := res & {ne_seq_type_or_void(intersection_superset_implementation(seq_elem_type_1, seq_elem_type_2))} if seq_elem_type_1 /= void_type and seq_elem_type_2 /= void_type;

      // Sets
      res := res & {empty_set_type} if includes_empty_set(type1) and includes_empty_set(type2);

      set_elem_type_1 := set_elem_type(type1);
      set_elem_type_2 := set_elem_type(type2);
      res := res & {ne_set_type_or_void(intersection_superset_implementation(set_elem_type_1, set_elem_type_2))} if set_elem_type_1 /= void_type and set_elem_type_2 /= void_type;

      // Maps and tuples
      res := res & {empty_map_type} if includes_empty_map(type1) and includes_empty_map(type2);

      key_type_1   := map_key_type(type1);
      value_type_1 := map_value_type(type1);
      tuple_type_1 := tuple_type(type1);
      key_type_2   := map_key_type(type2);
      value_type_2 := map_value_type(type2);
      tuple_type_2 := tuple_type(type2);
      if (key_type_1 /= void_type and value_type_1 /= void_type)
        if (key_type_2 /= void_type and value_type_2 /= void_type)
          res := res & {ne_map_type_or_void(intersection_superset_implementation(key_type_1, key_type_2), intersection_superset_implementation(value_type_1, value_type_2))};
        else
          res := res & {map_tuple_intersection_superset(key_type_1, value_type_1, _obj_(tuple_type_2))} if tuple_type_2 /= void_type;
        ;
      else
        if (key_type_2 /= void_type and value_type_2 /= void_type)
          res := res & {map_tuple_intersection_superset(key_type_2, value_type_2, _obj_(tuple_type_1))} if tuple_type_1 /= void_type;
        else
          res := {tuple_types_intersection(_obj_(tuple_type_1), _obj_(tuple_type_2))} if tuple_type_1 /= void_type and tuple_type_2 /= void_type;
        ;
      ;

      // Tagged objects
      tag_obj_types_1 := tagged_obj_types(type1);
      tag_obj_types_2 := tagged_obj_types(type2);

      if (tag_obj_types_1 /= {} and tag_obj_types_2 /= {})
        tag_types_1 := {t.tag_type : t <- tag_obj_types_1};
        tag_types_2 := {t.tag_type : t <- tag_obj_types_2};

        // Type vars in the tag are treated just like the atom_type //## TYPE VARS ARE NOT ALLOWED IN THE TAG ANYMORE...
        if (may_include_all_symbols(tag_types_1))
          obj_type_1 := only_element(tag_obj_types_1).obj_type;
          if (may_include_all_symbols(tag_types_2))
            obj_type_2 := only_element(tag_obj_types_2).obj_type;
            res := res & {tag_obj_type_or_void(atom_type, intersection_superset_implementation(obj_type_1, obj_type_2))};
          else
            tag_to_obj_2 := (t.tag_type => t.obj_type : t <- tag_obj_types_2);
            res := res & {tag_obj_type_or_void(t, intersection_superset_implementation(obj_type_1, tag_to_obj_2[t])) : t <- tag_types_2};
          ;
        else
          assert tag_types_1 :: <SymbType+>;
          tag_to_obj_1 := (t.tag_type => t.obj_type : t <- tag_obj_types_1);
          if (may_include_all_symbols(tag_types_2))
            obj_type_2 := only_element(tag_obj_types_2).obj_type;
            res := res & {tag_obj_type_or_void(t, intersection_superset_implementation(tag_to_obj_1[t], obj_type_2)) : t <- tag_types_1};
          else
            tag_to_obj_2 := (t.tag_type => t.obj_type : t <- tag_obj_types_2);
            common_tags :=  intersection(tag_types_1, tag_types_2);
            res := res & {tag_obj_type_or_void(t, intersection_superset_implementation(tag_to_obj_1[t], tag_to_obj_2[t])) : t <- common_tags};
          ;
        ;
      ;
    ;

    res := res - {void_type};
    return if res /= {} then union_type(res) else void_type end;


    ClosedType ne_seq_type_or_void(ClosedType elem_type) = type_or_void(ne_seq_type(elem_type), {elem_type});
    ClosedType ne_set_type_or_void(ClosedType elem_type) = type_or_void(ne_set_type(elem_type), {elem_type});
    ClosedType ne_map_type_or_void(ClosedType key_type, ClosedType value_type) = type_or_void(ne_map_type(key_type, value_type), {key_type, value_type});
    ClosedType tag_obj_type_or_void(TagType tag_type, ClosedType obj_type) = type_or_void(tag_obj_type(tag_type, obj_type), {obj_type});

    ClosedType type_or_void(ClosedType type, ClosedType+ basic_types) = if in(void_type, basic_types) then void_type else type end;
  }

  Bool may_include_all_symbols(TagType+ types) //= in(atom_type, types) or (? TypeVar <- types); //## THIS IS THE VERSION WITHOUT ALL THE CHECKS
  {
    assert not (in(atom_type, types) and (? t <- types : t :: TypeVar));
    if (in(atom_type, types))
      assert types == {atom_type};
      return true;
    elif ((? t <- types : t :: TypeVar))
      assert size(types) == 1 and only_element(types) :: TypeVar;
      return true;
    else
      assert types :: <SymbType+>;
      return false;
    ;
  }

  <IntType, void_type> int_types_intersection(<IntType, void_type> int_type_1, <IntType, void_type> int_type_2):
    integer,      _             = int_type_2,

    low_ints(),   low_ints()    = low_ints(min(int_type_1.max, int_type_2.max)),
    low_ints(),   high_ints()   = maybe_int_range(int_type_2.min, int_type_1.max),
    low_ints(),   int_range()   = maybe_int_range(int_type_2.min, min(int_type_1.max, max(int_type_2))),

    high_ints(),  high_ints()   = high_ints(max(int_type_1.min, int_type_2.min)),
    high_ints(),  int_range()   = maybe_int_range(max(int_type_1.min, int_type_2.min), max(int_type_2)),

    int_range(),  int_range()   = maybe_int_range(max(int_type_1.min, int_type_2.min), min(max(int_type_1), max(int_type_2))),

    _,            _             = int_types_intersection(int_type_2, int_type_1);


  //## THIS SHOULD BE MOVED TO THE utils_2_ctors.h FILE
  <IntType, void_type> maybe_int_range(Int min, Int max) = if max >= min then int_range(min, max) else void_type end;

  <TupleType[AnonType], void_type> map_tuple_intersection_superset(AnonType key_type, AnonType value_type, (SymbObj => (type: AnonType, optional: Bool)) tuple_fields)
  {
    res_fs := ();
    for (l : rand_sort(keys(tuple_fields)))
      f := tuple_fields[l];
      intersection_type := intersection_superset_implementation(value_type, f.type);
      if (f.optional)
        if (includes_symbol(key_type, l) and intersection_type /= void_type)
          res_fs := res_fs & (l => (type: intersection_type, optional: true));
        ;
      else
        return void_type if not includes_symbol(key_type, l) or intersection_type == void_type;
        res_fs := res_fs & (l => (type: intersection_type, optional: false));
      ;
    ;

    //## WHAT CAN BE DONE TO EXCLUDE THE EMPTY MAP WHEN ALL THE FIELDS ARE OPTIONAL?

    return if res_fs /= () then tuple_type(res_fs) else void_type end;
  }

  <TupleType[AnonType], empty_map_type, void_type> tuple_types_intersection((SymbObj => (type: AnonType, optional: Bool)) fields1, (SymbObj => (type: AnonType, optional: Bool)) fields2)
  {
    labels1 := keys(fields1);
    labels2 := keys(fields2);

    common_labels := intersection(labels1, labels2);
    exclusive_labels_1 := labels1 - common_labels;
    exclusive_labels_2 := labels2 - common_labels;

    return void_type if (? l <- exclusive_labels_1 : not fields1[l].optional) or (? l <- exclusive_labels_2 : not fields2[l].optional);

    res_fields := ();
    for (l : common_labels)
      field1 := fields1[l];
      field2 := fields2[l];

      res_type := intersection_superset_implementation(field1.type, field2.type);
      if (res_type == void_type)
        return void_type if not field1.optional or not field2.optional;
      else
        res_fields := res_fields & (l => (type: res_type, optional: field1.optional and field2.optional));
      ;
    ;

    if (res_fields /= ())
      return tuple_type(res_fields);
    else
      return empty_map_type;
    ;
  }
}

////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////

//## THIS IS TOTALLY UNTESTED. IT SHOULD BE TESTED WITH THE TYPE SUBSET TESTING CODE,
//## AND MAYBE IT WOULD BE GOOD TO DO SOME MANUAL TESTING, ESPECIALLY FOR TUPLE TYPES
Bool type_contains_obj(AnonType type, Any obj):
  atom_type,        +           = true,
  atom_type,        _           = false,

  symb_type(s?),    _           = obj == s,

  integer,          *           = true,
  integer,          _           = false,

  low_ints(),       *           = obj <= type.max,
  low_ints(),       _           = false,

  high_ints(),      *           = obj >= type.min,
  high_ints(),      _           = false,

  int_range(),      *           = obj >= type.min and obj <= max(type),
  int_range(),      _           = false,

  type_var(),       _           = {fail;},

  empty_seq_type,   _           = obj == [],
  empty_set_type,   _           = obj == {},
  empty_map_type,   _           = obj == (),

  ne_seq_type(),    [...]       = obj /= [] and all([type_contains_obj(type.elem_type, e) : e <- obj]),
  ne_seq_type(),    _           = false,

  ne_set_type(),    {...}       = obj /= {} and not (? e <- obj : not type_contains_obj(type.elem_type, e)),
  ne_set_type(),    _           = false,

  ne_map_type(),    (...)       = obj /= () and not (? k => v <- obj : not type_contains_obj(type.key_type, k) or not type_contains_obj(type.value_type, v)),
  ne_map_type(),    _           = false,

  tuple_type(fs?),  (...)       = not (? k => v <- obj : not has_key(fs, k) or not type_contains_obj(fs[k].type, v)) and
                                  subset({l : l => f <- fs ; not f.optional}, keys(obj)),
  tuple_type(fs?),  _           = false,

  tag_obj_type(),   tag @ iobj  = type_contains_obj(type.tag_type, tag) and type_contains_obj(type.obj_type, iobj),
  tag_obj_type(),   _           = false,

  union_type(ts?),  _           = (? t <- ts : type_contains_obj(t, obj)),

  self_rec_type(),  _           = type_contains_obj(unfold(type), obj),
  mut_rec_type(),   _           = type_contains_obj(unfold(type), obj);


////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////

using (TypeName => AnonType) typedefs
{
  //## RIGHT NOW THIS IS ACTUALLY A SUPERSET OF THE ACTUAL INTERSECTION, BUT AFTER
  //## THE COMING REFACTORING OF PATTERNS, IT SHOULD RETURN THE EXACT INTERSECTION
  ClosedType pattern_type_intersection(Pattern ptrn, AnonType type):
    ptrn_any              = type,
    obj_ptrn(object(x?))  = intersection_superset(if x :: Atom then symb_type(x) else int_range(x, x) end, type),
    type_ptrn(t?)         = intersection_superset(user_type_to_anon_type(t), type),
    ext_var_ptrn()        = type, //## THIS IS GOING AWAY ANYWAY, NO NEED TO BOTHER
    var_ptrn()            = pattern_type_intersection(ptrn.ptrn, type),
    tag_ptrn()            = {
        tag_obj_types := tagged_obj_types(type);
        sel_types := {
          tag_obj_type(tag_type_int, obj_type_int):
          t <- tag_obj_types,
          tag_type_int = pattern_type_intersection(ptrn.tag, t.tag_type),
          obj_type_int = pattern_type_intersection(ptrn.obj, t.obj_type);
          tag_type_int /= void_type,
          obj_type_int /= void_type
        };
        assert sel_types /= {}; //## THIS ASSERTION IS JUST A TEMPORARY CHECK, IT SHOULD EVENTUALLY BE REMOVED
        assert sel_types == {} or anon_type_is_wf(union_type(sel_types));
        return if sel_types == {} then void_type else union_type(sel_types) end;
    };
}


<<LeafType, TypeVar, CompType[AnonType]>*> split_type(AnonType type):
  LeafType        = {type}, //## BAD: EXACT SAME EXPRESSION REPEATED 7 TIMES
  type_var()      = {type},
  ne_seq_type()   = {type},
  ne_set_type()   = {type},
  ne_map_type()   = {type},
  tuple_type()    = {type},
  tag_obj_type()  = {type},
  union_type(ts?) = {unfold(t) : t <- ts},
  self_rec_type() = {unfold(type)},
  mut_rec_type()  = {unfold(type)};


//## MAYBE THIS SHOULD JUST CALL replace_type_vars(). PREMATURE OPTIMIZATION?
//## EVEN BETTER, IN ORDER TO AVOID RETRIEVING ALL THE TYPE VARIABLES IN THE TYPE,
//## IT WOULD BE POSSIBLE TO PLACE A CLOSURE
AnonType replace_type_vars_with_type_any(AnonType type):
  LeafType          = type,
  SelfPretype       = type,
  TypeVar           = type_any,
  ne_seq_type()     = ne_seq_type(replace_type_vars_with_type_any(type.elem_type)),
  ne_set_type()     = ne_set_type(replace_type_vars_with_type_any(type.elem_type)),
  ne_map_type()     = ne_map_type(replace_type_vars_with_type_any(type.key_type), replace_type_vars_with_type_any(type.value_type)),
  tuple_type(fs?)   = tuple_type((l => (type: replace_type_vars_with_type_any(f.type), optional: f.optional) : l => f <- fs)), //## BAD: WOULD BE GOOD TO HAVE A "DECLARATIVE" UPDATE OPERATION
  tag_obj_type()    = tag_obj_type(type.tag_type, replace_type_vars_with_type_any(type.obj_type)),
  union_type(ts?)   = union_type({replace_type_vars_with_type_any(t) : t <- ts}),
  self_rec_type(t?) = self_rec_type(replace_type_vars_with_type_any(t)),
  mut_rec_type()    = mut_rec_type(index: type.index, types: [replace_type_vars_with_type_any(t) : t <- type.types]);


AnonType replace_type_vars(AnonType type, (TypeVar => AnonType) substitutions):
  LeafType          = type,
  SelfPretype       = type,
  TypeVar           = substitutions[type],
  ne_seq_type()     = ne_seq_type(replace_type_vars(type.elem_type, substitutions)),
  ne_set_type()     = ne_set_type(replace_type_vars(type.elem_type, substitutions)),
  ne_map_type()     = ne_map_type(replace_type_vars(type.key_type, substitutions), replace_type_vars(type.value_type, substitutions)),
  tuple_type(fs?)   = tuple_type((l => (type: replace_type_vars(f.type, substitutions), optional: f.optional) : l => f <- fs)), //## BAD: WOULD BE GOOD TO HAVE A "DECLARATIVE" UPDATE OPERATION
  tag_obj_type()    = tag_obj_type(type.tag_type, replace_type_vars(type.obj_type, substitutions)),
  union_type(ts?)   = union_type({replace_type_vars(t, substitutions) : t <- ts}),
  self_rec_type(t?) = self_rec_type(replace_type_vars(t, substitutions)),
  mut_rec_type()    = mut_rec_type(index: type.index, types: [replace_type_vars(t, substitutions) : t <- type.types]);


//## MAYBE THIS (AND ALL THE FUNCTIONS IT DEPENDS ON) SHOULD GO IN THE SAME FILE AS is_subset(AnonType, AnonType)
Bool is_subset(ClsType t1, ClsType t2)
{
  assert length(t1.in_types) == length(t2.in_types);

  for (i : indexes(t1.in_types))
    return false if not is_subset(t2.in_types[i], replace_type_vars_with_type_any(t1.in_types[i]));
  ;
  return is_subset(cls_call_type(t1, t2.in_types), t2.out_type);
}


AnonType cls_call_type(ClsType signature, [AnonType^] actual_types) //## FIND BETTER NAME
{
  cs := merge_value_sets({subset_conds(actual_types[i], signature.in_types[i]) : i <- index_set(actual_types)});
  type_var_insts := (v => union_superset(ts) : v => ts <- cs);
  return replace_type_vars(signature.out_type, type_var_insts);
}
