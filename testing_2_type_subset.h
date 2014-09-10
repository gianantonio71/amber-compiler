Nat bit(Bool b) = if b then 1 else 0 end;
// Bool bool([0..1] n) = if n == 0 then false else true end;

T*+ powerset(T* s)
{
  return {{}} if s == {};
  rand_elem := rand_elem(s);
  rec_ps := powerset(s - {rand_elem});
  return rec_ps & {ss & {rand_elem} : ss <- rec_ps};
}

T** powerset(T* s, Nat min_size) = {ss : ss <- powerset(s) ; size(ss) >= min_size};

T** ne_powerset(T* s) = powerset(s, 1) - {{}};



T*+ set_cart_prod(T++ s)
{
  if (size(s) == 1)
    ss := only_element(s);
    return {{e} : e <- ss};
  ;

  rand_set := rand_elem(s);
  rec_cp := set_cart_prod(s - {rand_set});
  return {cpe & {re} : cpe <- rec_cp, re <- rand_set};
}


AnonType* gen_self_rec_pretypes(NzNat max_depth, Atom* term_symbols, Atom* func_symbols)
{
  singl_types := {symb_type(s) : s <- term_symbols};
  if (max_depth == 1)
    // print "************ max_depth = " & to_str(max_depth);
    res := {union_type(ts) : ts <- powerset(singl_types & {self}) - {{}}};
    return res;
  ;

  pretypes := gen_self_rec_pretypes(max_depth-1, term_symbols, func_symbols);

  // print "************ max_depth = " & to_str(max_depth);

  pretypes := {{st} : st <- singl_types} & {{self}} & {{tag_obj_type(symb_type(f), pt) : pt <- pretypes} : f <- func_symbols};
  pretypes := set_cart_prod(pretypes);
  pretypes := union({powerset(pt) : pt <- pretypes});

  pretypes := {union_type(ts) : ts <- pretypes - {{}}};
  self_rec_types := {t : pt <- pretypes, t = self_rec_type(pt) ; anon_type_is_wf(t, {})};
  self_rec_types_bad := {t : pt <- pretypes, t = self_rec_type(pt) ; not anon_type_is_wf(t, {})};

  return pretypes & self_rec_types;
}


AnonType* gen_types(NzNat max_depth, Atom* term_symbols, Atom* func_symbols)
{
  pts := gen_self_rec_pretypes(max_depth, term_symbols, func_symbols);
  print "***";
  print size(pts);
  return {pt : pt <- pts ; anon_type_is_wf(pt, {})};
}


Set gen_objs(NzNat max_depth, Atom* term_symbols, Atom* func_symbols)
{
  return term_symbols if max_depth == 1;
  low_objs := gen_objs(max_depth-1, term_symbols, func_symbols);
  top_objs := {f @ o : o <- low_objs, f <- func_symbols};
  return low_objs & top_objs;
}


// Bool contains(AnonType type, Any object) = contains(type, object, nil);

// Bool contains(AnonType type, Any object, Maybe[AnonType] self_type):
//   symb_type(object(a)),       _           = object == a,
//   :self,                      _           = contains(untag(self_type), object, self_type),
//   tag_obj_type(),             tag @ obj   = contains(type.tag_type, tag, self_type) and contains(type.obj_type, obj, self_type),
//   union_type(ts),             _           = (? t <- ts : contains(t, object, self_type)),
//   self_rec_type(t),           _           = contains(t, object, just(type)),
//   _,                          _           = false;


Bool ref_is_subset([Nat*] incl_map_1, [Nat*] incl_map_2)
{
  // assert length(incl_map_1) == length(incl_map_2);

  // for (i : indexes(incl_map_1))
  //   incl_1 := incl_map_1[i];
  //   incl_2 := incl_map_2[i];
  //   return false if incl_1 and not incl_2;
  // ;

  len1 := length(incl_map_1);
  len2 := length(incl_map_2);

  i1 := 0;
  i2 := 0;
  while (i1 < len1 and i2 < len2)
    incl_1 := incl_map_1[i1];
    incl_2 := incl_map_2[i2];

    if (incl_1 == incl_2)
      i1 := i1 + 1;
      i2 := i2 + 1;

    elif (incl_1 > incl_2)
      i2 := i2 + 1;

    else
      return false;
    ;
  ;

  return i1 == len1;
}


Nat count_self_rec_types(AnonType type):
  LeafType          = 0,
  :self             = 0,
  tag_obj_type()    = count_self_rec_types(type.obj_type),
  union_type(ts)    = max({count_self_rec_types(t) : t <- ts}),
  self_rec_type(t)  = count_self_rec_types(t) + 1;


String type_to_str(AnonType type):
  symb_type(object(a))  = _str_(a),
  :self                 = "*",
  tag_obj_type()        = type_to_str(type.tag_type) & "(" & type_to_str(type.obj_type) & ")",
  union_type(ts)        = append(intermix([type_to_str(t) : t <- ts], ", ")),
  self_rec_type(t)      = "<" & type_to_str(t) & ">",
  _                     = {fail;};


String*  types_to_str(AnonType* types)         = {type_to_str(t) : t <- types};
String** typess_to_string(AnonType** typess)   = {{type_to_str(t) : t <- ts} : ts <- typess};


Bool test_type_subset_checking([AnonType*] types, [Any*] objs)
{
  incl_matrix := [[i : o, i <- objs, type_contains_obj(t, o)] : t <- types];
  ok := true;
  count := 0;
  for (i1 : indexes(types))
    t1 := types[i1];
    loc_count := 0;
    for (i2 : indexes(types))
      t2 := types[i2];
      res := is_subset(t1, t2);
      ref_res := ref_is_subset(incl_matrix[i1], incl_matrix[i2]);
      if (res /= ref_res)
        ok := false;
        print "********** ERROR! ERROR! ERROR! **********";
        print res;
        print ref_res;
        print type_to_str(t1);
        print type_to_str(t2);
        print t1;
        print t2;
        // fail;
      ;
      loc_count := loc_count + 1 if res and i1 /= i2;
    ;
    count := count + loc_count;
    print [i1, loc_count, type_to_str(t1)];
  ;
  print ["Number of subset relations found", count];
  return ok;
}


Bool check_intersection(ClosedType inters, [Any*] objs, [Nat*] ns1, [Nat*] ns2)
{
  l1 := length(ns1);
  l2 := length(ns2);
  i1 := 0;
  i2 := 0;
  while (i1 < l1 and i2 < l2)
    n1 := ns1[i1];
    n2 := ns2[i2];
    if (n1 == n2)
      obj := objs[n1];
      return false if inters == void_type or not type_contains_obj(inters, obj);
      i1 := i1 + 1;
      i2 := i2 + 1;
    elif (n1 < n2)
      i1 := i1 + 1;
    else
      i2 := i2 + 1;
    ;
  ;
  return true;
}


test_type_intersection_checking([AnonType*] types, [Any*] objs)
{
  incl_matrix := [[i : o, i <- objs, type_contains_obj(t, o)] : t <- types];
  low_counter := 0;
  high_counter := 0;
  for (t1, i1 : types; t2, i2 : types)
    inters := intersection_superset(t1, t2);
    if (not check_intersection(inters, objs, incl_matrix[i1], incl_matrix[i2]))
      print "ERROR ERROR ERROR ERROR:";
      print t1;
      print t2;
      print inters;
      fail;
    ;
    low_counter := low_counter + 1;
    if (low_counter == 100)
      high_counter := high_counter + 1;
      low_counter := 0;
      print high_counter;
    ;
  ;
  return nil;
}


Bool rand_bool = _rand_nat_(1) == 1;
Bool once_in(NzNat times) = _rand_nat_(times-1) == 0;
Bool rand_bool(NzNat true_freq, NzNat false_freq) = _rand_nat_(true_freq+false_freq-1) < true_freq;

Nat rand_nat(Nat max) = _rand_nat_(max);
Nat rand_nat(Nat min, Nat max) = min + _rand_nat_(max - min);

T rand_elem(T+ set)   = _rand_elem_(set);

T* rand_subset(T* set, Nat min_size)
{
  valid_subsets := {ss : ss <- powerset(set) ; size(ss) >= min_size};
  assert size(valid_subsets) > 0;
  return rand_elem(valid_subsets);
}


// using Bool compatible(T, T)
// {
//   T* rand_constr_subset(T* set, Nat min_size)
//   {
//     valid_subsets := {ss : ss <- powerset(set) ; size(ss) >= min_size, not (? x1 <- ss, x2 <- ss : x1 /= x2, not compatible(x1, x2))};
//     assert size(valid_subsets) > 0;
//     return rand_elem(valid_subsets);
//   }
// }


AnonType* gen_rand_types(NzNat max_depth, NzNat count, Atom* term_symbs, Atom* func_symbs)
{
  let (term_symbs=term_symbs, func_symbs=func_symbs, rec_is_allowed=false, rec_is_req=false, ground_is_req=true, self_term_symbs={}, self_fn_symbs={})
    ts := {gen_rand_type(rand_nat(1, max_depth), i) : i <- set(inc_seq(count))}; //## UGLY UGLY
    // bad_types := {t : t <- ts ; not anon_type_is_wf(t, {})};
    // for (t : bad_types)
    //   print type_to_str(t);
    //   // print t;
    //   // print t :: UnionType[AnonType];
    //   // if (t :: UnionType[AnonType])
    //   //   for (st : rand_sort(untag(t)))
    //   //     if (not anon_type_is_wf(st, {}))
    //   //       print st;
    //   //     ;
    //   //   ;
    //   // ;
    // ;
    assert not (? t <- ts : not anon_type_is_wf(t, {}));
    return ts;
  ;  

  AnonType gen_rand_type(NzNat depth, Nat idx)
  {
    // print idx;
    res := gen_rand_type(depth);
    // print type_to_str(res);
    if (not anon_type_is_wf(res, {}))
      print idx;
      print type_to_str(res);
      fail;
    ;
    return res;
  }
}


using
{
  Atom* term_symbs,             // All terminal symbols
  Atom* func_symbs,             // All function symbols
  Bool  rec_is_allowed,         // Whether a recursive reference is allowed
  Bool  rec_is_req,             // Whether a recursive reference somewhere is required
  Bool  ground_is_req,          // Whether a ground branch somewhere is required
  Atom* self_term_symbs,        // Terminal symbols incompatible with self
  Atom* self_fn_symbs;          // Function symbols incompatible with self


  AnonType gen_rand_union_type(NzNat depth)
  {
    assert depth > 1;
    assert term_symbs /= {} and func_symbs /= {};

    self_comp_term_symbs := term_symbs - self_term_symbs;
    self_comp_fn_symbs   := func_symbs - self_fn_symbs;

    self_comp_symbs_available := self_comp_term_symbs /= {} or self_comp_fn_symbs /= {};

    if (rec_is_req)
      self_in_fn_type := func_symbs /= {} and once_in(2);
      self_here := not self_in_fn_type or (size(self_comp_fn_symbs) > 1 and once_in(4));
    else
      self_in_fn_type := false;
      self_here := rec_is_allowed and once_in(4);
    ;

    if (self_here)
      types := {self};
      rem_term_symbs := self_comp_term_symbs;
      rem_fn_symbs := self_comp_fn_symbs;
    else
      types := {};
      rem_term_symbs := term_symbs;
      rem_fn_symbs   := func_symbs;
    ;

    if (self_in_fn_type)
      self_fn_symb := rand_elem(rem_fn_symbs);
      rem_fn_symbs := rem_fn_symbs - {self_fn_symb};
      type := gen_rand_tag_obj_type(depth, self_fn_symb);
      types := types & {type};
    ;

    if (rem_term_symbs /= {} or rem_fn_symbs /= {})
      types := types & gen_rand_non_union_types(depth, rem_term_symbs, rem_fn_symbs ; rec_is_req=false);
    ;

    assert not (rec_is_req and not (? t <- types : has_rec_branches(t)));

    return union_type(types);
  }


  AnonType+ gen_rand_non_union_types(NzNat max_depth, Atom* valid_term_symbs, Atom* valid_fn_symbs)
  {
    // We assume that all self references (both required ones and allowed ones) are dealt with somewhere else.
    assert not rec_is_req;

    rem_term_symbs := valid_term_symbs;
    rem_fn_symbs   := valid_fn_symbs;

    rec_types := {};
    // Let's decide whether we want another recursive type here
    while (rem_fn_symbs /= {} and max_depth >= 3 and once_in(3))
      sel_term_symbs := rand_subset(rem_term_symbs, 0);
      sel_fn_symbs := rand_subset(rem_fn_symbs, 1);
      type := gen_rand_self_rec_type(max_depth, sel_term_symbs, sel_fn_symbs);
      rec_types := rec_types & {type};
      rem_term_symbs := rem_term_symbs - sel_term_symbs;
      rem_fn_symbs := rem_fn_symbs - sel_fn_symbs;
    ;

    return rec_types if rem_term_symbs == {} and rem_fn_symbs == {};

    at_least_one_term := rem_term_symbs /= {} and (rem_fn_symbs == {} or once_in(2));
    used_term_symbs := rand_subset(rem_term_symbs, bit(at_least_one_term));
    used_fn_symbs := rand_subset(rem_fn_symbs, bit(not at_least_one_term));

    assert used_term_symbs /= {} or used_fn_symbs /= {};

    term_types := {symb_type(s) : s <- used_term_symbs};

    if (ground_is_req and rec_types == {} and term_types == {})
      ground_fn_symb := rand_elem(used_fn_symbs);
      fn_types := {gen_rand_tag_obj_type(max_depth, s; ground_is_req = s == ground_fn_symb) : s <- used_fn_symbs};
    else
      fn_types := {gen_rand_tag_obj_type(max_depth, s; ground_is_req=false) : s <- used_fn_symbs};
    ;

    return rec_types & term_types & fn_types;
  }


  // Depth does not include unions
  AnonType gen_rand_type(NzNat depth)
  {
    return union_type(gen_rand_term_types) if depth == 1;

    return match(rand_elem({:fn, :union, :self_rec if not rec_is_req and depth >= 3}))
             :fn        = gen_rand_tag_obj_type(depth),
             :union     = gen_rand_union_type(depth),
             :self_rec  = gen_rand_self_rec_type(depth);
           ;
  }


  AnonType* gen_rand_term_types =
  {
    ground_types := powerset({symb_type(s) : s <- term_symbs}, 1);
    self_types   := {s & {self} : s <- powerset({symb_type(s) : s <- term_symbs - self_term_symbs}, bit(ground_is_req))};
    all_types    := ground_types & self_types;
    sel_types    := if rec_is_req      then self_types,
                       rec_is_allowed  then all_types
                                       else ground_types;
                    ;
    return rand_elem(sel_types);
  };


  TagObjType[AnonType] gen_rand_tag_obj_type(NzNat depth) = gen_rand_tag_obj_type(depth, rand_elem(func_symbs));

  TagObjType[AnonType] gen_rand_tag_obj_type(NzNat depth, Atom fn_symb)
  {
    loop
      tag_type := symb_type(fn_symb);
      obj_type := gen_rand_type(depth-1);
      tag_obj_type := tag_obj_type(tag_type, obj_type);
      assert not (rec_is_req and not has_rec_branches(tag_obj_type));
      assert not (ground_is_req and not has_ground_branches(tag_obj_type));
      return tag_obj_type;
    ;
  }


  SelfRecType[AnonType] gen_rand_self_rec_type(NzNat depth) = gen_rand_self_rec_type(depth, rand_subset(term_symbs, 0), rand_subset(func_symbs, 1));

  SelfRecType[AnonType] gen_rand_self_rec_type(NzNat depth, Atom* sel_term_symbs, Atom+ sel_fn_symbs)
  {
    assert depth >= 3;
    symb_types         := {symb_type(s) : s <- sel_term_symbs};
    sel_rec_fn_symb    := rand_elem(sel_fn_symbs);
    sel_ground_fn_symb := rand_elem(sel_fn_symbs);
    let (incl_self=true, self_term_symbs=sel_term_symbs, self_fn_symbs=sel_fn_symbs)
      tag_obj_types := for (s <- sel_fn_symbs) {{
                         rec_is_req := s == sel_rec_fn_symb;
                         ground_is_req := sel_term_symbs == {} and s == sel_ground_fn_symb;
                         return gen_rand_tag_obj_type(depth-1, s; rec_is_req=rec_is_req, ground_is_req=ground_is_req);
                       }};
    ;
    inner_type := union_type(symb_types & tag_obj_types);
    rec_type   := self_rec_type(inner_type);
    assert anon_type_is_wf(rec_type, {});
    return rec_type;
  }
}

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

type LeafTypeGroup  = any_symb, int, empty_seq, empty_set, empty_map, symb(Atom);
type CompTypeGroup  = ne_seq, ne_set, ne_map, tuple, tag_obj_any_tag, tag_obj(Atom);
type TypeGroup      = LeafTypeGroup, CompTypeGroup;

Bool are_compatible(TypeGroup g1, TypeGroup g2)
{
  return g1 /= g2 and are_half_comp(g1, g2) and are_half_comp(g2, g1);

  are_half_comp(g1, g2):
    :any_symb,        symb()      = false,
    :empty_map,       :tuple      = false,
    :ne_map,          :tuple      = false,
    :tag_obj_any_tag, tag_obj()   = false,
    _,                _           = true;
}


AnonType+ gen_rand_non_rec_types(NzNat max_depth, NzNat count, Atom* term_symbs, Atom* func_symbs) 
{
  leaf_type_groups := {:any_symb, :int, :empty_seq, :empty_set, :empty_map} & {:symb(s) : s <- term_symbs};
  comp_type_groups := {:ne_seq, :ne_set, :ne_map, :tuple, :tag_obj_any_tag} & {:tag_obj(s) : s <- func_symbs};

  valid_sets_of_leaf_type_groups := {ss : ss <- powerset(leaf_type_groups) ; is_valid_subset(ss)};
  valid_sets_of_type_groups := {ss : ss <- powerset(leaf_type_groups & comp_type_groups) ; is_valid_subset(ss, comp_type_groups)};

  print size(valid_sets_of_leaf_type_groups);
  print size(valid_sets_of_type_groups);

  return {generate_checked_rand_non_rec_type(max_depth, term_symbs, func_symbs, leaf_type_groups, comp_type_groups, valid_sets_of_leaf_type_groups, valid_sets_of_type_groups) : i <- set(inc_seq(count))}; //## UGLY UGLY


  Bool is_valid_subset(TypeGroup+ ss) = size(ss) >= 2 and not (? x1 <- ss, x2 <- ss : x1 /= x2, not are_compatible(x1, x2));

  Bool is_valid_subset(TypeGroup+ ss, TypeGroup+ comp_type_groups) = is_valid_subset(ss) and not disjoint(ss, comp_type_groups);

  AnonType generate_checked_rand_non_rec_type(NzNat max_depth, Atom* term_symbs, Atom* func_symbs, TypeGroup+ leaf_type_groups, TypeGroup+ comp_type_groups, TypeGroup++ valid_sets_of_leaf_type_groups, TypeGroup++ valid_sets_of_type_groups)
  {
    let (term_symbs=term_symbs, func_symbs=func_symbs, leaf_type_groups=leaf_type_groups, comp_type_groups=comp_type_groups, valid_sets_of_leaf_type_groups=valid_sets_of_leaf_type_groups, valid_sets_of_type_groups=valid_sets_of_type_groups)
      type := gen_rand_non_rec_type(rand_nat(1, max_depth));
    ;
    if (not anon_type_is_wf(type, {}))
      print "ERROR ERROR ERROR!";
      print type;
      fail;
    ;
    return type;
  }
}




using
{
  Atom*       term_symbs,   // All terminal symbols
  Atom*       func_symbs,   // All function symbols
  TypeGroup+  leaf_type_groups,
  TypeGroup+  comp_type_groups,
  TypeGroup++ valid_sets_of_leaf_type_groups,
  TypeGroup++ valid_sets_of_type_groups;

  AnonType gen_rand_non_rec_type(NzNat max_depth)
  {
    return gen_rand_non_rec_union_type(max_depth) if once_in(3);

    type_groups := if max_depth == 1 then leaf_type_groups else comp_type_groups end;

    return gen_rand_non_rec_type_of_group(rand_elem(type_groups), max_depth);
  }

  AnonType gen_rand_non_rec_union_type(NzNat max_depth)
  {
    return union_type({gen_rand_non_rec_type_of_group(g, 1) : g <- rand_elem(valid_sets_of_leaf_type_groups)}) if max_depth == 1;

    groups := rand_elem(valid_sets_of_type_groups);
    max_depth_group := rand_elem(intersection(groups, comp_type_groups));
    max_depth_type := gen_rand_non_rec_type_of_group(max_depth_group, max_depth);
    types := {max_depth_type} & {gen_rand_non_rec_type_of_group(g, if in(g, comp_type_groups) then rand_nat(2, max_depth) else 1 end) : g <- groups ; g /= max_depth_group};
    return union_type(types);
  }    

  AnonType gen_rand_non_rec_type_of_group(_, NzNat max_depth):
    :any_symb         = atom_type,
    symb(s)           = symb_type(s),
    :int              = gen_rand_int_type,
    :empty_seq        = empty_seq_type,
    :empty_set        = empty_set_type,
    :empty_map        = empty_map_type,
    :ne_seq           = ne_seq_type(gen_rand_non_rec_type(max_depth-1)),
    :ne_set           = ne_set_type(gen_rand_non_rec_type(max_depth-1)),
    :ne_map           = ne_map_type(gen_rand_non_rec_type(max_depth-1), gen_rand_non_rec_type(max_depth-1)),
    :tuple            = gen_rand_non_rec_tuple_type(max_depth),
    tag_obj(s)        = tag_obj_type(symb_type(s), gen_rand_non_rec_type(max_depth-1)),
    :tag_obj_any_tag  = tag_obj_type(atom_type, gen_rand_non_rec_type(max_depth-1));

  SymbType rand_symb_type = symb_type(rand_elem(term_symbs));

  IntType gen_rand_int_type = rand_elem({integer, low_ints(rand_nat(1000)), high_ints(rand_nat(1000)), int_range(min: rand_nat(1000), size: rand_nat(1, 1000))});

  AnonType gen_rand_non_rec_tuple_type(NzNat max_depth) = tuple_type((object(l) => (type: gen_rand_non_rec_type(max_depth-1), optional: once_in(3)) : l <- rand_subset(term_symbs, 1)));
}


// IntType integer = :integer;
// IntType low_ints(Int max) = low_ints(max: max);
// IntType high_ints(Int min) = high_ints(min: min);
// IntType int_range(Int min, Int max) = int_range(min: min, size: max-min+1); //## BUG: WHAT HAPPENS IF max IS LOWER THAN min?



[T*] middle_subseq([T*] s, Nat left, Nat right) = _slice_(s, left, max(0, length(s)-left-right));

test_main =
{
  // o := _obj_("obj.txt");
  // print o;
  // print anon_type_is_wf(o);
  // return nil;

  // o := _obj_("obj.txt");
  // print o;
  // t1 := o[0];
  // t2 := o[1];
  // print anon_type_is_wf(t1);
  // print anon_type_is_wf(t2);
  // tu := union_superset({t1, t2});
  // print anon_type_is_wf(tu);
  // return nil;

  types := gen_rand_types(5, 400, {:a, :b}, {:f, :g});
  // types := gen_rand_non_rec_types(5, 400, {:a, :b}, {:f, :g});
  type_pairs := {[t1, t2] : t1 <- types, t2 <- types};

  print size(types);

  inters_semi_errors_count := 0;

  for (ts, i : rand_sort(type_pairs))
    print i;
    t0 := ts[0];
    t1 := ts[1];
    tu := union_superset(set(ts));
    ti := intersection_superset(t0, t1);

    if (not anon_type_is_wf(tu))
      print "ERROR ERROR ERROR ERROR!";
      print "UNION TYPE IS NOT WELL FORMED";
      print t0;
      print t1;
      print tu;
      fail;
    ;

    if (ti /= void_type and not anon_type_is_wf(ti))
      print "ERROR ERROR ERROR ERROR!";
      print "INTERSECTION TYPE IS NOT WELL FORMED";
      print t0;
      print t1;
      print ti;
      fail;
    ;

// print "#1";
    is_01 := is_subset(t0, t1);
// print "#2";
    is_0u := is_subset(t0, tu);
// print "#3";
    is_1u := is_subset(t1, tu);
// print "#4";
    is_i0 := ti == void_type or is_subset(ti, t0);
// print "#5";
    is_i1 := ti == void_type or is_subset(ti, t1);
// print "#6";

    if (not is_0u or not is_1u)
      print "ERROR ERROR ERROR ERROR!";
      print t0;
      print t1;
      print tu;
      print is_0u;
      print is_1u;
      fail;
    ;

    if (not is_i0 or not is_i1)
      inters_semi_errors_count := inters_semi_errors_count + 1;
    ;
  ;

  print inters_semi_errors_count;

  return nil;

  // AnonType* gen_rand_types(NzNat max_depth, NzNat count, Atom* term_symbs, Atom* func_symbs)
  // for (i : inc_seq(10000))
  //   types := gen_rand_types(5, 1000, {:a, :b}, {:f, :g});
  //   print i + 1;
  // ;
  // return nil;

  types := gen_rand_types(5, 400, {:a, :b}, {:f, :g});
  // types := set(middle_subseq(rand_sort(types), 200, 0));
  print types_to_str(types);
  print size(types);

  // return nil;

  // types := gen_types(2, {:a}, {:f, :g});
  // // types := gen_self_rec_pretypes(3, {:a}, {:f, :g});
  // print size(types);

  objs := gen_objs(8, {:a, :b}, {:f, :g});
  print size(objs);
  // print objs;
  
  types := rand_sort(types);
  objs  := rand_sort(objs);

  print "- - - - - - - - - - - - - - - - - - - - - -";
  for (c : [0, 1, 2, 3])
    print length([t : t <- types, count_self_rec_types(t) == c]);
  ;

  print length([t : t <- types, count_self_rec_types(t) > 0 and not t :: <self_rec_type(Any)>]);

  print "-------------------------------------------";

  // for (i1 : indexes(types))
  //   for (i2 : indexes(types))
  //     print [i1, i2];
  //     t1 := types[i1];
  //     t2 := types[i2];
  //     t12 := intersection_superset(t1, t2);
  //   ;
  // ;

  // return nil;

  // print [t : t <- types, count_self_rec_types(t) == 1];

  // for (t : types)
  //   if (count_self_rec_types(t) > 0 and not t :: <self_rec_type(Any)>)
  //     print t;
  //   ;
  // ;

  // print types_to_str(types);

  // ok := test_type_subset_checking(types, objs);

  ok := test_type_intersection_checking(types, objs);

  print "We are at the end and all is well!";

  return nil;
};


testcases r := test_main; end
