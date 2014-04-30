
Tautology types_are_wf((TypeSymbol => Type) typedefs)
{
  //## COULD THE FOLLOWING BE PART OF A MORE GENERAL AND ELEGANT CONSTRAINT?
  // No top-level reference cycles
  tl_ref_map      := (s => top_level_refs(t) : s => t <- typedefs);
  tl_ref_deep_map := transitive_closure(tl_ref_map);
  return false if (? s => es <- tl_ref_deep_map : in(s, es));
  
  // Every Type must be well formed
  return not (? s => t <- typedefs : not type_is_wf(t, select TypeVar in s end; typedefs = typedefs));
  
  // Local functions
  TypeSymbol* top_level_refs(Type type):
    type_ref(s)     = {s},
    union_type(ts)  = union({top_level_refs(t) : t <- ts}),
    _               = {};
}

using (TypeSymbol => Type) typedefs
{
  Tautology type_is_wf(Type type, TypeVar* type_vars):
    
    LeafType            = true,
    
    type_ref(ts)        = has_key(typedefs, ts),
    
    //type_var(a)         = in(type, type_vars),
    //## BUG FIX FIX FIX
    type_var(a)         = { print "Missing type var: " & _str_(a) if not in(type, type_vars);
                            return true;
                          },
    
    seq_type()          = type_is_wf(type.elem_type, type_vars),
    
    fixed_seq_type(ts)  = all([type_is_wf(t, type_vars) : t <- ts]),
    
    set_type()          = type_is_wf(type.elem_type, type_vars),
    
    map_type()          = type_is_wf(type.key_type, type_vars) and
                          type_is_wf(type.value_type, type_vars),
    
    tuple_type(bs)      = { ls := apply(bs; f(b) = b.label);
                            return not (? l => c <- ls : c > 1) and
                                   not (? b <- bs : not type_is_wf(b.type, type_vars));  
                          },
    
    //## BUG BUG BUG THIS IS INCOMPLETE, THE TAG TYPE MUST BE A SUBSET OF atom_type
    tag_type()          = type_is_wf(type.tag_type, type_vars) and
                          type_is_wf(type.obj_type, type_vars),
    
                        //## I DON'T LIKE ALL THESE DOUBLE NEGATIONS.
                        //## IT WOULD BE GOOD TO HAVE UNIVERSAL QUALIFICATION
    union_type(ts)      = size(ts) >= 2                                             and
                          //## BAD BAD BAD THIS SHOULD BE ENFORCED IN THE TYPE DEFINITION
                          not (? UnionType <- ts)                                   and
                          not (? t <- ts : not type_is_wf(t, type_vars))  and
                          //## BAD BAD BAD
                          not (? t1 <- ts, t2 <- ts : t1 /= t2, not are_compatible(t1, t2));
}