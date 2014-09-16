
type AtomicPseudoType = symbol(Atom), integers, empty_set, ne_sets, empty_seq, ne_seqs, empty_map, ne_maps, tag_obj(Atom);

type BasicPseudoType  = symbols, tag_objs, AtomicPseudoType;

type PseudoType       = pseudotype(BasicPseudoType*); //## BAD: THIS ALLOWS FOR INVALID COMBINATIONS, LIKE {symbol(a), symbols}


///////////////////////////////////////////////////////////////////////////////////////////////////

PseudoType pseudotype(BasicPseudoType* pts)
{
  red_symb_pts    := if in(:symbols, pts)  then {pt : symbol() pt <- pts} else {} end;
  red_tag_obj_pts := if in(:tag_objs, pts) then {pt : tag_obj() pt <- pts} else {} end;
  return :pseudotype(pts - (red_symb_pts & red_tag_obj_pts));
}


PseudoType pseudotype_any = pseudotype({:symbols, :integers, :empty_set, :ne_sets, :empty_seq, :ne_seqs, :empty_map, :ne_maps, :tag_objs});

PseudoType pseudotype_symbol(Atom a)  = pseudotype({:symbol(a)});
PseudoType pseudotype_symbols         = pseudotype({:symbols});
PseudoType pseudotype_integers        = pseudotype({:integers});
PseudoType pseudotype_empty_seq       = pseudotype({:empty_seq});
PseudoType pseudotype_empty_set       = pseudotype({:empty_set});
PseudoType pseudotype_empty_map       = pseudotype({:empty_map});
PseudoType pseudotype_ne_seqs         = pseudotype({:ne_seqs});
PseudoType pseudotype_ne_sets         = pseudotype({:ne_sets});
PseudoType pseudotype_ne_maps         = pseudotype({:ne_maps});
PseudoType pseudotype_seqs            = pseudotype({:empty_seq, :ne_seqs});
PseudoType pseudotype_sets            = pseudotype({:empty_set, :ne_sets});
PseudoType pseudotype_maps            = pseudotype({:empty_map, :ne_maps});
PseudoType pseudotype_tag_obj(Atom a) = pseudotype({:tag_obj(a)});
PseudoType pseudotype_tag_objs        = pseudotype({:tag_objs});

///////////////////////////////////////////////////////////////////////////////////////////////////

Bool includes(PseudoType pseudotype, AtomicPseudoType atomic_pseudotype):
  pseudotype(pts),  symbol()    = in(atomic_pseudotype, pts) or in(:symbols, pts),
  pseudotype(pts),  tag_obj()   = in(atomic_pseudotype, pts) or in(:tag_objs, pts),
  pseudotype(pts),  _           = in(atomic_pseudotype, pts);


Bool are_disjoint(PseudoType pseudotype, BasicPseudoType basic_pseudotype):
  pseudotype(pts),  :symbols    = not (? :symbols <- pts \/ symbol() <- pts),
  pseudotype(pts),  :tag_objs   = not (? :tag_objs <- pts \/ tag_obj() <- pts),
  _,                _           = not includes(pseudotype, basic_pseudotype);


Bool are_disjoint(PseudoType pt1, PseudoType pt2) = not (? bpt1 <- _obj_(pt1) : not are_disjoint(pt2, bpt1));

PseudoType pseudotype_union(PseudoType* pseudotypes) = pseudotype(union({pts : pseudotype(pts) <- pseudotypes}));

///////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////

PseudoType pseudotype(Obj obj) = pseudotype({atomic_pseudotype(obj)});

AtomicPseudoType atomic_pseudotype(Obj):
  object(+ a)         = :symbol(a),
  object(*)           = :integers,
  object({...} s)     = if s == {} then :empty_set else :ne_sets end,
  object([...] s)     = if s == [] then :empty_seq else :ne_seqs end,
  object((...) m)     = if m == () then :empty_map else :ne_maps end,
  object(tag @ obj)   = :tag_obj(tag); //## REPLACE THE obj VARIABLE WITH _ AS SOON AS THE PARSER ALLOWS IT

///////////////////////////////////////////////////////////////////////////////////////////////////

PseudoType pseudotype(Pattern ptrn):
  :ptrn_symbol            = pseudotype_symbols,
  :ptrn_integer           = pseudotype_integers,
  :ptrn_empty_set         = pseudotype_empty_set,
  :ptrn_ne_set            = pseudotype_ne_sets,
  :ptrn_empty_seq         = pseudotype_empty_seq,
  :ptrn_ne_seq            = pseudotype_ne_seqs,
  :ptrn_empty_map         = pseudotype_empty_map,
  :ptrn_ne_map            = pseudotype_ne_maps,
  :ptrn_tag_obj           = pseudotype_tag_objs,
  :ptrn_any               = pseudotype_any,
  ptrn_symbol(object(a))  = pseudotype_symbol(a),
  ptrn_integer()          = pseudotype_integers,
  ptrn_var()              = pseudotype(ptrn.ptrn),
  ptrn_union(ps)          = pseudotype_union({pseudotype(p) : p <- ps}),
  ptrn_tag_obj()          = match (ptrn.tag)
                              :ptrn_symbol            = pseudotype_tag_objs,
                              ptrn_symbol(object(a))  = pseudotype_tag_obj(a),
                              ptrn_var()              = pseudotype_tag_objs;
                            ;

///////////////////////////////////////////////////////////////////////////////////////////////////

Pattern pseudotype_pattern(PseudoType pseudotype) = ptrn_union({pseudotype_pattern(pt) : pt <- _obj_(pseudotype)});

Pattern pseudotype_pattern(BasicPseudoType pseudotype):
  symbol(a)   = ptrn_symbol(a),
  :symbols    = ptrn_symbol,
  :integers   = ptrn_integer,
  :empty_set  = ptrn_empty_set,
  :ne_sets    = ptrn_ne_set,
  :empty_seq  = ptrn_empty_seq,
  :ne_seqs    = ptrn_ne_seq,
  :empty_map  = ptrn_empty_map,
  :ne_maps    = ptrn_ne_map,
  tag_obj(a)  = ptrn_tag_obj(ptrn_symbol(a), ptrn_any),
  :tag_objs   = ptrn_tag_obj(ptrn_symbol, ptrn_any);

///////////////////////////////////////////////////////////////////////////////////////////////////

PseudoType pseudotype(AnonType type) = pretype_pseudotype(type, ());

PseudoType pretype_pseudotype(AnonType type, (SelfPretype => PseudoType) self_pseudotypes):
  :self                 = self_pseudotypes[type],
  self()                = self_pseudotypes[type],
  :atom_type            = pseudotype_symbols,
  symb_type(object(a))  = pseudotype_symbol(a),
  IntType               = pseudotype_integers,
  TypeVar               = pseudotype_any,
  :empty_set_type       = pseudotype_empty_set,
  ne_set_type()         = pseudotype_ne_sets,
  :empty_seq_type       = pseudotype_empty_seq,
  ne_seq_type()         = pseudotype_ne_seqs,
  :empty_map_type       = pseudotype_empty_map,
  ne_map_type()         = pseudotype_ne_maps,
  tuple_type(fs)        = pseudotype_union({pseudotype_ne_maps, pseudotype_empty_map if (? l => f <- fs : not f.optional)}),
  union_type(ts)        = pseudotype_union({pretype_pseudotype(t, self_pseudotypes) : t <- ts}),
  tag_obj_type()        = match (type.tag_type)
                            symb_type(object(a))  = pseudotype_tag_obj(a),
                            :atom_type            = pseudotype_tag_objs;
                          ,
  self_rec_type(t)      = pretype_pseudotype(t, ()), //## NOT ENTIRELY SURE
  mut_rec_type()        = pseudotypes[self(type.index)] let pseudotypes := mut_rec_type_pseudotype(type);;


(SelfPretype => PseudoType) mut_rec_type_pseudotype(MutRecType[AnonType] type)
{
  refs := [{s : s <- top_level_rec_refs(t)} : t <- type.types];
  pseudotypes := ();
  loop
    next_type_idxs := {i : i <- index_set(type.types) ; not has_key(pseudotypes, self(i)) and subset(refs[i], keys(pseudotypes))};
    assert next_type_idxs /= {} or keys(pseudotypes) == {self(i) : i <- index_set(type.types)};
    return pseudotypes if next_type_idxs == {};
    pseudotypes := pseudotypes & (self(i) => pretype_pseudotype(type.types[i], pseudotypes) : i <- next_type_idxs);
  ;
}


SelfPretype* top_level_rec_refs(AnonType type): //## THIS IS NOT THE RIGHT PLACE FOR THIS FUNCTION
  SelfPretype     = {type},
  union_type(ts)  = union({top_level_rec_refs(t) : t <- ts}),
  _               = {};
