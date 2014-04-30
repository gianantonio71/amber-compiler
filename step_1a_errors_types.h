using
{
  (TypeSymbol => SynType)   typedefs,
  [BasicTypeSymbol, NzNat]* all_par_type_symbols,
  TypeVar*                  type_vars_in_scope;


  TDefUserErr* type_wf_errors(SynType type):
    LeafType                      = {},
    
    type_ref(BasicTypeSymbol ts)  = {:undef_type_name(ts) if not has_key(typedefs, ts)},
    
    type_ref(ParTypeSymbol ts)    = union({type_wf_errors(t) : t <- set(ts.params)}) &
                                    {
                                      :undef_par_type_name(
                                        name:  ts.symbol,
                                        arity: length(ts.params)
                                      ) if not in([ts.symbol, length(ts.params)], all_par_type_symbols)
                                    },
                                     
    TypeVar                       = {:undef_type_var(type) if not in(type, type_vars_in_scope)},

    //seq_type(elem_type: Type, nonempty: Bool)
    seq_type()                    = type_wf_errors(type.elem_type),
    
    //fixed_seq_type([Type+])
    fixed_seq_type(ts)            = union({type_wf_errors(t) : t <- set(ts)}),

    //set_type(elem_type: Type, nonempty: Bool);
    set_type()                    = type_wf_errors(type.elem_type),

    //map_type(key_type: Type, value_type: Type);
    map_type()                    = type_wf_errors(type.key_type) & type_wf_errors(type.value_type),

    //tuple_type((label: SymbObj, type: Type, optional: Bool)+)
    tuple_type(fs)                = { lab_count := apply(fs; f(f) = f.label);
                                      rep_labs  := {l : l => n <- lab_count};
                                      lab_errs  := if rep_labs == {} then {} else :rep_labels_in_map(rep_labs) end;
                                      return union({type_wf_errors(f.type) : f <- fs});
                                    },

    //tag_type(tag_type: Type, obj_type: Type)
    tag_type()                    = { //## THIS DOES NOT HANDLE TYPE REFERENCES YET
                                      if (type.tag_type :: <SymbType, SymbType+, atom_type>)
                                        tag_errs := {};
                                      else
                                        tag_errs := :invalid_type_for_tag(type.tag_type);
                                      ;
                                      
                                      return tag_errs & type_wf_errors(type.obj_type);    
                                    },

    union_type(ts)                = { nts := normalize_unions(ts);

                                      errs := union({type_wf_errors(t) : t <- nts});
                                      return errs if errs /= {};

                                      ncts := incompatibilities(nts);
                                      if (ncts == {})
                                        return {};
                                      else
                                        return {:incompatible_types_in_union_type(ncts)};
                                      ;
                                    };


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
      _,        _         = are_disjoint(partitions(t1), partitions(t2));
  }
}

//## THIS ONE MAYBE SHOULD GO IN A DIFFERENT FILE
SynType+ normalize_unions(SynType+ ts) = union({normalize_union(t) : t <- ts});

SynType+ normalize_union(SynType type):
  union_type(ts)  = normalize_unions(ts),
  _               = {type};
