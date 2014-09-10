
type ObjPart    = symbol(Atom), integers, empty_set, ne_sets, empty_seq, ne_seqs, empty_map, ne_maps, tagged_obj(Atom);

type ObjPartSet = <symbols, tagged_objs, ObjPart>+; //## BAD


ObjPartSet all_objects = {:symbols, :integers, :empty_set, :ne_sets, :empty_seq, :ne_seqs, :empty_map, :ne_maps, :tagged_objs};


Bool includes(ObjPartSet ps, ObjPart p)
{
  return true if in(p, ps);
  return in(:symbols, ps)     if (p :: <symbol(Atom)>);
  return in(:tagged_objs, ps) if (p :: <tagged_obj(Atom)>);
  return false;
}


Bool are_disjoint(ObjPartSet ps, <symbols, tagged_objs, ObjPart> p):
  _,  :symbols      = not (? :symbols <- ps \/ symbol() <- ps),
  _,  :tagged_objs  = not (? :tagged_objs <- ps \/ tagged_obj() <- ps),
  _,  _             = not includes(ps, p);


Bool are_disjoint(ObjPartSet ps1, ObjPartSet ps2) = not (? p <- ps1 : not are_disjoint(ps2, p));


ObjPartSet merge_partitions(ObjPartSet* part_sets)
{
  ps := union(part_sets);
  ps := {p : p <- ps ; not p :: <symbol(Atom)>}     if in(:symbols, ps);      //## BAD BAD BAD
  ps := {p : p <- ps ; not p :: <tagged_obj(Atom)>} if in(:tagged_objs, ps);  //## BAD BAD BAD
  return ps;
}


ObjPart partition(Obj):
  object(Atom a)  = :symbol(a),
  object(Int)     = :integers,
  object(Set s)   = if s == {} then :empty_set else :ne_sets end,
  object(Seq s)   = if s == [] then :empty_seq else :ne_seqs end,
  object(Map m)   = if m == () then :empty_map else :ne_maps end,
  tag @ obj       = :tagged_obj(tag);


using (TypeSymbol => UserType) typedefs
{
  ObjPartSet partitions(UserType type):
    :atom_type      = {:symbols},
    symb_type(s)    = {partition(s)},
    IntType         = {:integers},
    //## BUG BUG BUG ASSUMING THERE ARE NO DIRECT CYCLES IN TYPEDEFS
    //## BUG BUG BUG ALSO ASSUMING NO TYPE REFERENCE IS "DANGLING"
    type_ref(ts)    = partitions(typedefs[ts]),
    TypeVar         = all_objects,
    :empty_set_type = {:empty_set},
    ne_set_type()   = {:ne_sets},
    :empty_seq_type = {:empty_seq},
    ne_seq_type()   = {:ne_seqs},
    :empty_map_type = {:empty_map},
    ne_map_type()   = {:ne_maps},
    tuple_type(fs)  = {:ne_maps, :empty_map if (? l => f <- fs : not f.optional)},
    union_type(ts)  = merge_partitions({partitions(t) : t <- ts}),
    tag_obj_type()  = match (type.tag_type)
                        symb_type(object(a))  = {:tagged_obj(a)},
                        :atom_type            = {:tagged_objs},
                        TypeVar               = {:tagged_objs};
                      ;


  ObjPartSet partitions(Pattern ptrn):
    :ptrn_any         = all_objects,
    obj_ptrn(obj)     = {partition(obj)},
    type_ptrn(type)   = partitions(type),
    ext_var_ptrn()    = all_objects,  //## COULD THIS BE IMPROVED?
    var_ptrn()        = partitions(ptrn.ptrn),
    var_ptrn()        = all_objects,
    tag_ptrn()        = match (ptrn.tag)
                          obj_ptrn(object(a)) = {:tagged_obj(a)},
                          var_ptrn()          = {:tagged_objs};
                        ;
}


//## BAD: MUCH OF THE IMPLEMENTATION IS SHARED WITH THE CORRISPONDENT METHOD FOR USER TYPES...
ObjPartSet anon_pretype_partitions(AnonType type, (SelfPretype => ObjPartSet) self_partitions):
  :self             = self_partitions[type],
  self()            = self_partitions[type],
  :atom_type        = {:symbols},
  symb_type(s)      = {partition(s)},
  IntType           = {:integers},
  TypeVar           = all_objects,
  :empty_set_type   = {:empty_set},
  ne_set_type()     = {:ne_sets},
  :empty_seq_type   = {:empty_seq},
  ne_seq_type()     = {:ne_seqs},
  :empty_map_type   = {:empty_map},
  ne_map_type()     = {:ne_maps},
  tuple_type(fs)    = {:ne_maps, :empty_map if (? l => f <- fs : not f.optional)},
  union_type(ts)    = merge_partitions({anon_pretype_partitions(t, self_partitions) : t <- ts}),
  tag_obj_type()    = match (type.tag_type)
                        symb_type(object(a))  = {:tagged_obj(a)},
                        :atom_type            = {:tagged_objs},
                        TypeVar               = {:tagged_objs};
                      ,
  self_rec_type(t)  = anon_pretype_partitions(t, ()), //## NOT ENTIRELY SURE
  mut_rec_type()    = parts[self(type.index)] let parts := mut_rec_type_partitions(type);;


(SelfPretype => ObjPartSet) mut_rec_type_partitions(MutRecType[AnonType] type)
{
  refs := [{s : s <- top_level_rec_refs(t)} : t <- type.types];
  parts := ();
  loop
    next_type_idxs := {i : i <- index_set(type.types) ; not has_key(parts, self(i)) and subset(refs[i], keys(parts))};
    assert next_type_idxs /= {} or keys(parts) == {self(i) : i <- index_set(type.types)};
    return parts if next_type_idxs == {};
    parts := parts & (self(i) => anon_pretype_partitions(type.types[i], parts) : i <- next_type_idxs);
  ;
}


SelfPretype* top_level_rec_refs(AnonType type):
  SelfPretype     = {type},
  union_type(ts)  = union({top_level_rec_refs(t) : t <- ts}),
  _               = {};