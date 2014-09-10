
Tautology types_are_wf((TypeSymbol => UserType) typedefs)
{
  //## COULD THE FOLLOWING BE PART OF A MORE GENERAL AND ELEGANT CONSTRAINT?
  // No top-level reference cycles
  tl_ref_map      := (s => top_level_refs(t) : s => t <- typedefs);
  tl_ref_deep_map := transitive_closure(tl_ref_map);
  return false if (? s => es <- tl_ref_deep_map : in(s, es));
  
  // Every Type must be well formed
  return not (? s => t <- typedefs : not type_is_wf(t, select TypeVar in s end; typedefs = typedefs));
  
  // Local functions
  TypeSymbol* top_level_refs(UserType type):
    type_ref(s)     = {s},
    union_type(ts)  = union({top_level_refs(t) : t <- ts}),
    _               = {};
}

using (TypeSymbol => UserType) typedefs
{
  Tautology type_is_wf(UserType type, TypeVar* type_vars):
    
    LeafType            = true,
    
    type_ref(ts)        = has_key(typedefs, ts),
    
    //type_var(a)         = in(type, type_vars),
    //## BUG FIX FIX FIX
    type_var(a)         = { print "Missing type var: " & _str_(a) if not in(type, type_vars);
                            return true;
                          },
    
    ne_seq_type()       = type_is_wf(type.elem_type, type_vars),
    
    ne_set_type()       = type_is_wf(type.elem_type, type_vars),
    
    ne_map_type()       = type_is_wf(type.key_type, type_vars) and
                          type_is_wf(type.value_type, type_vars),
    
    tuple_type(bs)      = not (? l => b <- bs : not type_is_wf(b.type, type_vars)),
    
    //## BUG BUG BUG THIS IS INCOMPLETE, THE TAG TYPE MUST BE A SUBSET OF atom_type
    tag_obj_type()      = type_is_wf(type.tag_type, type_vars) and
                          type_is_wf(type.obj_type, type_vars),
    
                          //## I DON'T LIKE ALL THESE DOUBLE NEGATIONS.
                          //## IT WOULD BE GOOD TO HAVE UNIVERSAL QUALIFICATION
    union_type(ts)      = size(ts) >= 2                                             and
                          //## BAD BAD BAD THIS SHOULD BE ENFORCED IN THE TYPE DEFINITION
                          not (? union_type() <- ts)                                and
                          not (? t <- ts : not type_is_wf(t, type_vars))            and
                          //## BAD BAD BAD
                          not (? t1 <- ts, t2 <- ts : t1 /= t2, not are_compatible(t1, t2));
}


Bool anon_type_is_wf(AnonType type) = anon_type_is_wf(type, select TypeVar in type end);

Bool anon_type_is_wf(AnonType type, TypeVar* type_vars) = not has_rec_branches(type) and anon_pretype_is_wf(type, (), type_vars);


Bool anon_pretype_is_wf(AnonType type, (SelfPretype => ObjPartSet) self_parts, TypeVar* type_vars)
{
  res := anon_pretype_is_wf_impl(type, self_parts, type_vars);
// if (not res)
//   print "--------------";
//   print type;
// ;
  return res;
}

Bool anon_pretype_is_wf_impl(AnonType type, (SelfPretype => ObjPartSet) self_parts, TypeVar* type_vars):
  LeafType              = true,

  :self                 = has_key(self_parts, type),

  self()                = has_key(self_parts, type),

  type_var(a)           = in(type, type_vars),

  ne_seq_type()         = anon_pretype_is_wf(type.elem_type, self_parts, type_vars),

  ne_set_type()         = anon_pretype_is_wf(type.elem_type, self_parts, type_vars),

  ne_map_type()         = anon_pretype_is_wf(type.key_type, self_parts, type_vars) and anon_pretype_is_wf(type.value_type, self_parts, type_vars),

  tag_obj_type()        = anon_pretype_is_wf(type.tag_type, self_parts, type_vars) and anon_pretype_is_wf(type.obj_type, self_parts, type_vars),

  tuple_type(fs)        = not (? l => f <- fs : not anon_pretype_is_wf(f.type, self_parts, type_vars)),

                          //## BAD: SEE ALL THE REASONS LISTED ABOVE
  union_type(ts)        = size(ts) > 1 and not (? union_type() <- ts) and
                          not (? t <- ts : not anon_pretype_is_wf(t, self_parts, type_vars)) and
                          not (? t1 <- ts, t2 <- ts : t1 /= t2, not anon_types_are_compatible(t1, t2, self_parts)), //## BAD: EVERY CONDITION IS EVALUATED TWICE

  self_rec_type(t)      = not has_top_level_self(t, self) and has_ground_branches(t) and has_rec_branches(t) and anon_pretype_is_wf(t, (self => anon_pretype_partitions(t, ())), type_vars),

  mut_rec_type()        = {
    //## THIS COULD BE MADE STRICTER BY MAKING SURE THAT THE TYPES DO HAVE CROSS REFERENCES AMONG THEM
    //## (OR, IDEALLY, THAT THEY CANNOT BE REDUCED TO SELF RECURSIVE TYPES)

    return false if type.index >= length(type.types);

    //## THIS CHECK IS NOT ENOUGH. IF TYPE 1 HAS JUST A TOP LEVEL REFERENCE TO TYPE 2 AND
    //## TYPE 2 HAS ONLY A TOP LEVEL REFERENCE TO TYPE 1, WE HAVE THE EQUIVALENT OF A TOP
    //## LEVEL SELF LOOP. IS THIS SOMEHOW CONNECTED WITH THE OTHER COMMENT ABOVE?
    for (t, i : type.types)
      return false if has_top_level_self(t, self(i));
    ;

    ground_branch_idxs := {};
    while (not in(type.index, ground_branch_idxs))
      ground_refs := {self(i) : i <- ground_branch_idxs};
      new_ground_branch_idxs := {i : i <- index_set(type.types) ; in(i, ground_branch_idxs) or has_ground_branches(type.types[i], ground_refs)};
      return false if new_ground_branch_idxs == ground_branch_idxs;
      assert subset(ground_branch_idxs, new_ground_branch_idxs);
      ground_branch_idxs := new_ground_branch_idxs;
    ;

    return not (? t <- set(type.types) : not anon_pretype_is_wf(t, mut_rec_type_partitions(type), type_vars));
  };


Bool has_top_level_self(AnonType type, SelfPretype self_ref) = in(self_ref, top_level_rec_refs(type));


Bool has_ground_branches(AnonType type) = has_ground_branches(type, {});

Bool has_ground_branches(AnonType type, SelfPretype* ground_refs):
  LeafType              = true,
  :self                 = false,
  self()                = in(type, ground_refs),
  type_var(a)           = true,
  ne_seq_type()         = has_ground_branches(type.elem_type, ground_refs),
  ne_set_type()         = has_ground_branches(type.elem_type, ground_refs),
  ne_map_type()         = has_ground_branches(type.key_type, ground_refs) and has_ground_branches(type.value_type, ground_refs),
  tuple_type(fs)        = (? l => f <- fs : has_ground_branches(f.type, ground_refs)), //## WHAT IF THAT PARTICULAR FIELD IS OPTIONAL?
  tag_obj_type()        = has_ground_branches(type.obj_type, ground_refs),
  union_type(ts)        = (? t <- ts : has_ground_branches(t, ground_refs)),
  self_rec_type(t)      = has_ground_branches(t, ground_refs), //## NOT SURE HERE...
  mut_rec_type()        = {fail;}; //## IMPLEMENT


Bool has_rec_branches(AnonType type):
  LeafType              = false,
  :self                 = true,
  self()                = true,
  type_var(a)           = false,
  ne_seq_type()         = has_rec_branches(type.elem_type),
  ne_set_type()         = has_rec_branches(type.elem_type),
  ne_map_type()         = has_rec_branches(type.key_type) or has_rec_branches(type.value_type),
  tuple_type(fs)        = (? l => f <- fs : has_rec_branches(f.type)), //## WHAT IF THAT PARTICULAR FIELD IS OPTIONAL?
  tag_obj_type()        = has_rec_branches(type.obj_type),
  union_type(ts)        = (? t <- ts : has_rec_branches(t)),
  self_rec_type(t)      = false, //## NOT SURE HERE...
  mut_rec_type()        = false; //## DITTO
