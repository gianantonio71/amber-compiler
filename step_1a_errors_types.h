using
{
  (SynTypeSymbol => SynType)                typedefs,
  (symbol: BasicTypeSymbol, arity: NzNat)*  all_par_type_symbols,
  TypeVar*                                  type_vars_in_scope;


  TDefUserErr* type_wf_errors(SynType type):
    LeafType                        = {},

    syn_int_range()                 = {assert type.min <= type.max; return {};}, //## HERE I SHOULD RETURN THE ERROR, NOT JUST ASSERT
    
    type_ref(type_symbol() ts?)     = {:undef_type_name(ts) if not has_key(typedefs, ts)},
    // type_ref(type_symbol() ts)      = {fail if not has_key(typedefs, ts); return {};},
    
    type_ref(par_type_symbol() ts?) = union({type_wf_errors(t) : t <- set(ts.params)}) &
                                      {
                                        undef_par_type_name(
                                          name:  ts.symbol,
                                          arity: length(ts.params)
                                        ) if not in((symbol: ts.symbol, arity: length(ts.params)), all_par_type_symbols)
                                      },

    TypeVar                         = {:undef_type_var(type) if not in(type, type_vars_in_scope)},

    //ne_seq_type(elem_type: Type)
    ne_seq_type()                   = type_wf_errors(type.elem_type),
    
    //ne_set_type(elem_type: Type);
    ne_set_type()                   = type_wf_errors(type.elem_type),

    //map_type(key_type: Type, value_type: Type);
    ne_map_type()                   = type_wf_errors(type.key_type) & type_wf_errors(type.value_type),

    //tuple_type([label: SymbObj, type: Type, optional: Bool^])
    tuple_type(fs?)                 = { lab_count = bag([f.label : f <- fs]); //## USING SEQUENCES WHERE BAGS WOULD SUFFICE FEELS WRONG...
                                        rep_labs  = {l : l => n <- lab_count, n > 1};
                                        lab_errs  = if rep_labs == {} then {} else {:rep_labels_in_map(rep_labs)} end;
                                        return union({type_wf_errors(f.type) : f <- set(fs)}) & lab_errs;
                                      },



    //tag_obj_type(tag_type: TagType, obj_type: Type)
    tag_obj_type()                  = { //## THIS DOES NOT HANDLE TYPE REFERENCES YET
                                        if (type.tag_type :: TagType)
                                          tag_errs = {};
                                        else
                                          tag_errs = {:invalid_type_for_tag(type.tag_type)};
                                        ;
                                      
                                        return tag_errs & type_wf_errors(type.obj_type);
                                      },

    union_type(ts?)                 = { nts = normalize_unions(ts);

                                        errs = union({type_wf_errors(t) : t <- nts});
                                        return errs if errs /= {};

                                        ncts = incompatibilities(nts);
                                        if (ncts == {})
                                          return {};
                                        else
                                          return {:incompatible_types_in_union_type(ncts)};
                                        ;
                                      },

    syn_union_type(ts?)             = type_wf_errors(:union_type(set(ts))); //## BAD


  SynType+* incompatibilities(SynType+ types)
  {
    //## BAD BAD, INEFFICIENT, EACH COMPARISON IS REPEATED TWICE        
    return for (t1 <- types, t2 <- types)
             if (t1 /= t2 and not are_syn_compatible(t1, t2))
               {{t1, t2}};

    Bool are_syn_compatible(SynType t1, SynType t2):
      TypeVar,  _         = false,
      _,        TypeVar   = false, //## BAD
      IntType,  IntType   = true,
      _,        _         = are_disjoint(syn_pseudotype(t1), syn_pseudotype(t2));
  }
}

//## THIS ONE MAYBE SHOULD GO IN A DIFFERENT FILE
SynType+ normalize_unions(SynType+ ts) = union({normalize_union(t) : t <- ts});

SynType+ normalize_union(SynType type):
  union_type(ts?) = normalize_unions(ts),
  _               = {type};
