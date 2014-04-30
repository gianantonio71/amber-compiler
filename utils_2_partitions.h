
type ObjPart    = symbol(Atom), integers, sets, sequences, maps, tagged_obj(Atom);

type ObjPartSet = <symbols, tagged_objs, ObjPart>+; //## BAD


ObjPartSet all_objects = {:symbols, :integers, :sets, :sequences, :maps, :tagged_objs};


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


//Bool is_subset(ObjPartSet ps1, ObjPartSet ps2) = not (? p <- ps1 : not include


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
  object(Set)     = :sets,
  object(Seq)     = :sequences,
  object(Map)     = :maps,
  tag @ obj       = :tagged_obj(tag);


using (TypeSymbol => Type) typedefs
{
  ObjPartSet partitions(Type type):
    :type_any       = all_objects,
    :atom_type      = {:symbols},
    symb_type(s)    = {partition(s)},
    IntType         = {:integers},
    //## BUG BUG BUG ASSUMING THERE ARE NO DIRECT CYCLES IN TYPEDEFS
    //## BUG BUG BUG ALSO ASSUMING NO TYPE REFERENCE IS "DANGLING"
    type_ref(ts)    = partitions(typedefs[ts]),
    TypeVar         = all_objects,
    SetType         = {:sets},
    SeqType         = {:sequences},
    MapType         = {:maps},
    TupleType       = {:maps},
    union_type(ts)  = merge_partitions({partitions(t) : t <- ts}),
    tag_type()      = { assert type.tag_type :: SymbType; //## BUG BUG BUG
                        return {:tagged_obj(untag(untag(type.tag_type)))};
                      };

  ObjPartSet partitions(Pattern ptrn):
    obj_ptrn(obj)                           = {partition(obj)},
    type_ptrn(type)                         = partitions(type),
    ext_var_ptrn()                          = all_objects,  //## COULD THIS BE IMPROVED?
    var_ptrn(ptrn: p, ...)                  = partitions(ptrn.ptrn),
    var_ptrn()                              = all_objects,
    tuple_ptrn()                            = {:maps},
    tag_ptrn(tag: obj_ptrn(object(a)), ...) = {:tagged_obj(a)},
    tag_ptrn(tag: var_ptrn(name: v), ...)   = {:tagged_objs};
}
