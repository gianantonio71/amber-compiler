Type norm_type(SynType type)
{
  return replace UnionType t in type with norm_union_type(t) end;

  Type norm_union_type(UnionType utype)
  {
    ts := {norm_type(t) : t <- rem_nesting(utype)};
    return if size(ts) > 1 then :union_type(ts) else only_element(ts) end;
  }

  //## BAD NAME  
  Type* rem_nesting(Type type):
    union_type(ts)  = union({rem_nesting(t) : t <- ts}),
    _               = {type};
}


//Type syn_type_to_type(SynType stype):
//  LeafType                      = stype,
//  seq_type(t)                   = mk_seq_type(t), //syn_type_to_type(t)),
//  ne_seq_type(t)                = mk_ne_seq_type(t), //syn_type_to_type(t)),
//  fixed_seq_type(ts)            = mk_fixed_seq_type([syn_type_to_type(t) : t <- ts]),
//  map_type()                    = mk_map_type(syn_type_to_type(stype.key), syn_type_to_type(stype.value), false),
//  ne_map_type()                 = mk_map_type(syn_type_to_type(stype.key), syn_type_to_type(stype.value), true),
//  //set_type(bs)                  = :set_type(syn_branch_to_branch(b) : b <- set(bs)),
//  term_type(root: r, type: t)   = term_type{root: r, type: syn_type_to_type(t)},
//  union_type(ts)                = mk_union_type({syn_type_to_type(t) : t <- set(ts)}),
//  type_ref(id)                  = type_id{id},
//  TypeVar                       = stype;
//
//syn_branch_to_branch(b) = {type: syn_type_to_type(b.type), card: if b.card? then b.card else :required end};
//
//Type mk_seq_type(SynType stype) = type_id{
//                                   par_type_symbol{
//                                     symbol: :impl_seq_type,
//                                     params: [stype]
//                                   }
//                                 };
//
//Type mk_ne_seq_type(SynType stype) = mk_head_tail_seq_type(syn_type_to_type(stype), mk_seq_type(stype));
//
//Type mk_fixed_seq_type([Type*]):
//  []      = singleton{symbol{[]}},
//  [h | t] = mk_head_tail_seq_type(h, mk_fixed_seq_type(t));
//
//Type mk_head_tail_seq_type(Type head, Type tail) = term_type{
//                                                     root: symbol{:seq},
//                                                     type: set_type{
//                                                             (type: wrap_type(:head, head), card: :required),
//                                                             (type: wrap_type(:tail, tail), card: :required)
//                                                           }
//                                                   };
//
//Type wrap_type(Atom root, Type type) = term_type{
//                                         root: symbol{root},
//                                         type: set_type{(type: type, card: :required)}
//                                       };
//
//Type mk_map_type(Type key_type, Type value_type, Bool nonempty)
//{
//  map_type := term_type{
//                root: symbol{:map},
//                type: set_type{(type: mk_fixed_seq_type([key_type, value_type]), card: :multiple)}
//              };
//
//  if (not nonempty)
//    map_type := union_type{singleton{symbol{:empty_map}}, map_type};
//  ;
//  
//  return map_type;  
//}
//
//Type mk_union_type(Type+ ts)
//{
//  nts := union(  
//           for (t <- ts) {
//             try (t)
//               union_type(sts+) = sts,
//               _                = {t};
//           }
//         );
//
//  assert nts :: {Type+};
//  assert not {? t <- nts ; t :: <union_type(Any+)>};  
//
//  int_ts     := {t : IntType t <- nts};
//  non_int_ts := nts - int_ts;
//  
//  int_ts     := merge_int_types(int_ts);
//  nts        := int_ts & non_int_ts;
//  
//  return if size(nts) = 1
//           then only_element(nts)
//           else :union_type @ nts;;
//}
//
//IntType* merge_int_types(IntType* types)
//{
//  return types if size(types) <= 1;
//
//  rand_type   := rand_elem(types);
//  other_types := types - {rand_type};
//  
//  loop
//    mergeable := {t : t <- other_types ; not separated(rand_type, t)};
//    break if mergeable = {};
//    
//    other_types := other_types - mergeable;
//    
//    while (mergeable /= {})
//      rand_mergeable := rand_elem(mergeable);
//      rand_type      := merge_int_types(rand_type, rand_mergeable);
//      mergeable      := mergeable - {rand_mergeable};
//    ;
//  ;
//
//  return {rand_type} & merge_int_types(other_types);
//
//
//  IntType merge_int_types(IntType t1, IntType t2):
//    :integer,     _             = :integer,
//
//    low_ints(),   low_ints()    = low_ints{max: max(t1.max, t2.max)},
//    low_ints(),   high_ints()   = {assert t2.min <= t1.max + 1; return :integer;}, //## BAD, VERY BAD. WITHOUT THE ASSERTION IT COULD PRODUCE AN INCORRECT RESULT
//    low_ints(),   int_range()   = {assert t2.min <= t1.max + 1; return low_ints{max: max(t1.max, t2.max)};}, //## BAD
//
//    high_ints(),  high_ints()   = high_ints{min: min(t1.min, t2.min)},
//    high_ints(),  int_range()   = {assert t1.min <= max(t2) + 1; return high_ints{min: min(t1.min, t2.min)};}, //## BAD
//
//    int_range(),  int_range()   = do assert t1.min <= max(t2) + 1 or t2.min <= max(t1) + 1; //## BAD
//                                     min := min(t1.min, t2.min);
//                                     max := max(max(t1), max(t2));
//                                     return int_range{min: min, size: max-min+1};
//                                  ;, // UGLY                                     
//
//    _,               _          = merge_int_types(t2, t1);
//}
