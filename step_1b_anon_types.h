//## WILL THIS WORK EVEN WITH STRANGE TEMPLATE TYPES?
//## FOR EXAMPLE, PARAMETRIC TYPES THAT CONTAIN ISTANTIATED VERSIONS OF THEMSELVES?
//## IS THAT EVEN POSSIBLE? TRY TO WORK OUT SOUND RULES FOR RECURSIVE PARAMETRIC TYPES


(TypeName => AnonType) normalize_and_anonymize_types((TypeSymbol => UserType) inst_types)
{
  all_anon_types := anonymize_types(inst_types);
  non_par_or_non_inst_anon_types := (ts => t : ts => t <- all_anon_types ; ts :: <BasicTypeSymbol, par_type_symbol(symbol: BasicTypeSymbol, params: [TypeVar+])>);
  pre_res := merge_values({(type_symb_to_name(s) => replace_named_type_vars(t, params(s))) : s => t <- non_par_or_non_inst_anon_types});
  return (s => only_element(ts) : s => ts <- pre_res);

  AnonType replace_named_type_vars(AnonType type, [TypeVar*] type_params) = replace TypeVar v in type with type_var(index_first(v, type_params)) end;
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


(TypeSymbol => AnonType) anonymize_types((TypeSymbol => UserType) types)
{
  anon_types  := ();
  types_to_do := types;

  while (types_to_do /= ())
    // Identifying clusters of type to expand. We can have three cases. Clusters can contain:
    //    one type that doesn't reference any other
    //    one type that only references itself
    //    a group of types, each of which references (generally indirectly) all other types in the cluster and only those.
    clusters := type_clusters_to_expand(types_to_do, keys(anon_types));

    // Expanding the types in each cluster, and merging the clusters together
    exp_types := merge({expand(c, types_to_do, anon_types) : c <- clusters});
    assert exp_types :: (TypeSymbol => AnonType);

    // Updating anon_types and types_to_do. All references to the types
    // that have just been expanded are replaces with the types themselves
    anon_types  := anon_types & exp_types;
    types_to_do := remove_keys(types_to_do, keys(exp_types));

    assert types_to_do :: (TypeSymbol => UserType);
    assert anon_types :: (TypeSymbol => AnonType);
  ;

  assert size(anon_types) == size(types);
  assert anon_types :: (TypeSymbol => AnonType);

  return anon_types;
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


TypeSymbol** type_clusters_to_expand((TypeSymbol => UserType) types, TypeSymbol* already_norm)
{
  ref_map        := (s => ref_type_symbols(t) - already_norm : s => t <- types);
  deep_ref_map   := transitive_closure(ref_map);
  conn_comps     := {{s} & rs : s => rs <- deep_ref_map};
  min_conn_comps := {c1 : c1 <- conn_comps ; not (? c2 <- conn_comps : c2 /= c1, subset(c2, c1))};
  return min_conn_comps;
}


////////////////////////////////////////////////////////////////////////////////
//////////////////////////////// Type expansion ////////////////////////////////


(TypeSymbol => AnonType) expand(TypeSymbol* type_symbs, (TypeSymbol => UserType) types, (TypeSymbol => AnonType) anon_types)
{
  anon_type_names := keys(anon_types);
  exp_types := ();
  rem_symbs := type_symbs;
  while (rem_symbs /= {})
    rem_types := select_by_key(types, rem_symbs);
    ref_map := (s => ref_type_symbols(t) - anon_type_names : s => t <- rem_types);
    exp_type_symbs := {s : s <- rem_symbs ; is_expandable(s, ref_map)};
    if (exp_type_symbs /= {})
      newly_exp_types := (s => expand_type(s, rem_types, exp_types & anon_types) : s <- exp_type_symbs);
    else
      newly_exp_types := expand_mutually_rec_types(rem_types, exp_types & anon_types);
      exp_type_symbs  := rem_symbs;
      assert keys(newly_exp_types) == rem_symbs;
    ;

    assert not (? ts => t <- newly_exp_types : not anon_type_is_wf(t));

    exp_types := exp_types & newly_exp_types;
    rem_symbs := rem_symbs - exp_type_symbs;
  ;

  return exp_types;


  Bool is_expandable(T node, (T => T*) edges)
  {
    reach := {node};
    for (i : inc_seq(size(edges) + 1)) //## BAD BAD BAD SHOULD BE <loop (n)> OR <for (n)>
      reach := union({edges[n] : n <- reach ; has_key(edges, n)}) - {node};
    ;
    return reach == {};
  }

  AnonType expand_type(TypeSymbol type_name, (TypeSymbol => UserType) types, (TypeSymbol => AnonType) anon_types)
  {
    type := types[type_name];
    has_self_refs := false;
    loop
      refs := ref_type_symbols(type);
      break if refs == {};
      type := replace_type_refs(type, types, anon_types, (type_name => self));
    ;
    type := self_rec_type(type) if has_rec_branches(type);
    assert anon_type_is_wf(type);
    return type;
  }

  (TypeSymbol => AnonType) expand_mutually_rec_types((TypeSymbol => UserType) types, (TypeSymbol => AnonType) anon_types)
  {
    type_names := rand_sort(keys(types));
    idxs := index_set(type_names);
    rec_subst_map  := (type_names[i] => self(i) : i <- idxs);
    mut_rec_anon_types := [replace_type_refs(types[tn], types, anon_types, rec_subst_map) : tn <- type_names];
    return (type_names[i] => mut_rec_type(i, mut_rec_anon_types) : i <- idxs);
  }
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


AnonType replace_type_refs(UserType type, (TypeSymbol => UserType) in_progress_type_map, (TypeSymbol => AnonType) subst_map, (TypeSymbol => SelfPretype) rec_subst_map) =
  normalize_type_unions(replace type_ref(ts) in type with replace_type_ref(ts, in_progress_type_map, subst_map, rec_subst_map) end);


AnonType replace_type_ref(TypeSymbol target_type_symbol, (TypeSymbol => UserType) in_progress_type_map, (TypeSymbol => AnonType) subst_map, (TypeSymbol => SelfPretype) rec_subst_map)
{
  assert disjoint(keys(in_progress_type_map), keys(subst_map));
  assert subset(keys(rec_subst_map), keys(in_progress_type_map));

  // If this is a self reference, then we return the self/self(Nat) object
  return rec_subst_map[target_type_symbol] if has_key(rec_subst_map, target_type_symbol);

  // We lookup the target type, and recursively replace all type references if it hasn't been done yet
  if (has_key(subst_map, target_type_symbol))
    return subst_map[target_type_symbol];
  else
    return replace_type_refs(in_progress_type_map[target_type_symbol], in_progress_type_map, subst_map, rec_subst_map);
  ;
}


TypeSymbol* ref_type_symbols(type) = retrieve ts from type_ref(ts) in type end;


AnonType normalize_type_unions(AnonType type):
  LeafType          = type,
  SelfPretype       = type,
  type_var(n)       = type,
  ne_seq_type()     = ne_seq_type(normalize_type_unions(type.elem_type)),
  ne_set_type()     = ne_set_type(normalize_type_unions(type.elem_type)),
  ne_map_type()     = ne_map_type(normalize_type_unions(type.key_type), normalize_type_unions(type.value_type)),
  tuple_type(fs)    = tuple_type((l => (type: normalize_type_unions(f.type), optional: f.optional) : l => f <- fs)),
  tag_obj_type()    = tag_obj_type(normalize_type_unions(type.tag_type), normalize_type_unions(type.obj_type)),
  union_type(ts)    = union_type({normalize_type_unions(t) : t <- ts}),
  self_rec_type(t)  = self_rec_type(normalize_type_unions(t)),
  mut_rec_type()    = mut_rec_type(index: type.index, types: [normalize_type_unions(t) : t <- type.types]);
