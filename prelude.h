
type Bool           = true, false;

type Nat            = [0..*];
type Int            = [*..*];
type NzNat          = [1..*];
//type NzInt          = [1..*], [*..-1];
type NegInt         = [*..-1] ;

type Rat            = Int, rat(num: Int, den: [2..*]);

type Atom           = <+>;
type Any            = Atom, Int, Seq, Set, Map, TagObj;

type Point          = point(x: Rat, y: Rat);

type BinTree[T]     = leaf, bin_tree(value: T, left: BinTree[T], right: BinTree[T]);
type BinTree        = BinTree[Any];

type Set            = Any*;
type NeSet          = Any+;

type Seq            = [Any];
type NeSeq          = [Any];

type Tuple          = (Atom => Any);
type Map            = (Any => Any);

type TagObj         = (<+> @ Any);

type Char           = char(Nat);
type String         = string([Nat]);

type Maybe[T]       = nil, just(T);

////////////////////////////////////////////////////////////////////////////////

// Replace this with === or ~=
Bool is_eq(T x, Maybe[T] maybe) = maybe == :just(x);

T just(T x) = :just(x);

////////////////////////////////////////////////////////////////////////////////

// Still not ideal, both of them. No need to always evaluate all arguments.
Bool some(Bool+ bs) = (? :true <- bs);
Bool all(Bool+ bs)  = not (? :false <- bs);

// No element is false
Bool all([Bool] s)   = not in(false, s);

// No element is true
Bool none([Bool] s)  = not in(true, s);

// At least one element is true
Bool at_least_one([Bool] s)  = in(true, s);

// At least one element is false
Bool not_all([Bool^] s) = in(true, s);

////////////////////////////////////////////////////////////////////////////////

Int op_-(Int n)         = _neg_(n);
Int op_+(Int a, Int b)  = _add_(a, b);

Int op_-(Int a, Int b) = a + -b;

Int op_*(Int a, Int b) = if a == 0      then 0,
                            a :: [1..*] then (a-1) * b + b
                                        else -(-a * b);
                         ;

Bool op_<(Int a, Int b) = (b - a) :: [1..*];

// Int op_*(Int a, Int b):
//   [0..0]  = 0,
//   [1..*]  = (a-1) * b + b,
//   [*..-1] = -(-a * b);

// Bool op_<(Int a, Int b):
//   [0..0], [1..*]  = true,
//   [0..0], _       = false,
//   _, _            = 0 < b - a;

Bool op_>(Int a, Int b) = b < a;
Bool op_>=(Int a, Int b) = a > b or a == b;
Bool op_<=(Int a, Int b) = a < b or a == b;

Int min(Int a, Int b) = if a < b then a else b end;
Int max(Int a, Int b) = if a > b then a else b end;

Int min(Int+ ns)
{
  ns_seq := rand_sort(ns);
  min := ns_seq[0];
  for (n : ns_seq)
    min := n if n < min;
  ;
  return min;
}

Int max(Int+ ns)
{
  ns_seq := rand_sort(ns);
  max := ns_seq[0];
  for (n : ns_seq)
    max := n if n > max;
  ;
  return max;
}

Int sum([Int] ns)
{
  res := 0;
  for (n : ns)
    res := res + n;
  ;
  return res;
}

////////////////////////////////////////////////////////////////////////////////

// Should it be defined for empty sequences (and negative integers)
// as well? It's always going to fail...

//T op_[]([T^] seq, Nat idx) = _at_(seq, idx);
op_[](Seq seq, Nat idx) = _at_(seq, idx); //## BAD BAD BAD

T rev_at([T^] seq, Nat idx) = _at_(seq, _len_(seq)-idx-1);

Nat length(Seq seq) = _len_(seq);

T at([T^] seq, Nat idx, T default) = if idx < _len_(seq) then _at_(seq, idx) else default end;

// Should be like this...
// T1 left((T1, T2) s)  = _at_(s, 0);
// T2 right((T1, T2) s) = _at_(s, 1);
T left([T] s)
{
  assert length(s) == 2;
  return s[0];
}

T right([T] s)
{
  assert length(s) == 2;
  return s[1];
}

T head([T^] s) = _at_(s, 0);
T tail([T^] s) = _slice_(s, 1, _len_(s)-1);
T last([T^] s) = _at_(s, _len_(s)-1);

op_&(Seq s1, Seq s2) = _cat_(s1, s2);

Bool in(Any e, Seq s)
{
  for (x : s)
    return true if x == e;
  ;
  return false;
}

Nat index_first(Any e, Seq s)
{
  for (x, i : s)
    return i if x == e;
  ;
  fail;
}

//[T] join([[T]] seqs)
join(Seq seqs)
{
  res := [];
  for (s : seqs)
    res := _cat_(res, s);
  ;
  return res;
}

reverse(Seq seq) = _rev_(seq);

[T] right_subseq([T] seq, Nat first) = _slice_(seq, first, length(seq) - first);

[T] subseq([T] seq, Nat first, Nat count) = _slice_(seq, first, count);

[T] subseq([T] s, <nil>, Nat m, Nat r) = subseq(s, length(s)-m-r, m);
[T] subseq([T] s, Nat l, <nil>, Nat r) = subseq(s, l, length(s)-l-r); 
[T] subseq([T] s, Nat l, Nat m, <nil>) = subseq(s, l, m);


[T] op_*(Nat count, [T] seq)
{
  res := [];
  for (i : inc_seq(count))
    for (x : reverse(seq))
      res := [x | res];
    ;
  ;
  return res;
}

[T] rep_seq(Nat size, T value)
{
  n := size;
  s := [];
  while (n > 0)
    s := [value | s];
    n := n - 1;
  ;
  return s;
}

[Nat] inc_seq(Nat n) = inc_seq(0, n);

[Nat] inc_seq(Nat m, Nat n)
{
  i := n - 1;
  s := [];
  while(i >= m)
    s := [i | s];
    i := i - 1;
  ;
  return s;
}

[Nat] dec_seq(Nat n) = reverse(inc_seq(n));

[Nat] indexes(Seq s) = inc_seq(length(s));

[Nat] indexes(Seq s, Nat m) = inc_seq(m, length(s));

Nat* index_set(Seq s) = set(indexes(s));

using Bool is_strictly_ordered(T, T) //## BAD BAD BAD
{
  [T] sort_set(T* s) = sort(rand_sort(s));
  
  [T] sort([T] s) = mergesort(s);

  //[T] quicksort([T] s) = quicksort(s, false);
  //
  //[T] quicksort([T], Bool (no_dups)):
  //  []       = [],
  //  [e]      = [e],
  //  [p | r]  = do
  //               head := [e : e <- r, e < p and (not no_dups or e /= p)];
  //               tail := [e : e <- r, not(e < p) and (not no_dups or e /= p)];

  //               return quicksort(head, no_dups) & [p] & quicksort(tail, no_dups);
  //             ;
  //;

  [T] mergesort([T] seq)
  {
    len := length(seq);
    return seq if len <= 1;
    ss := [[x] : x <- seq];
    while (len > 1)
      nss := [];
      idx := 0;
      //## BAD BAD BAD DOESN'T WORK WELL WITH A ROPE
      while (len > idx+1)
        nss := [merge(ss[idx], ss[idx+1]) | nss];
        idx := idx + 2;
      ;
      assert idx == length(ss) or idx == length(ss) - 1;
      ss  := if len > idx then [ss[idx] | nss] else nss end;
      len := length(ss); //## SHOULD BE len := (len + 1) / 2;
    ;
    return ss[0];
    
    [T] merge([T] seq1, [T] seq2)
    {
      l1 := length(seq1);
      l2 := length(seq2);
      rs := [];
      i1 := 0;
      i2 := 0;
      while (i1 < l1 or i2 < l2)
        if (i1 == l1 or (i2 < l2 and is_strictly_ordered(seq2[i2], seq1[i1])))
          rs := [seq2[i2] | rs];
          i2 := i2 + 1;
        else
          rs := [seq1[i1] | rs];
          i1 := i1 + 1;
        ;
      ;
      assert i1 <= l1 and i2 <= l2;
      return reverse(rs);
    }
  }
}

/////////////////////////////////////////////////////////////////////////////////////////

// Bool in(Any x, Set s) = (? e <- s : e == x);
Bool in(Any x, Set s) = _in_(x, s);

// [T1, T2]* cart_prod(T1* s1, T2* s2)  = {[e1, e2] : e1 <- s1, e2 <- s2};

//Set cart_prod([{T*}^] ss) = {[e1a, e1b, e2] : [e1a, e1b] <- s1 /\ e2 <- s2};

// T* union(T* s1, T* s2)         = {e : e <- s1 \/ e <- s2};
T* union(T* s1, T* s2)         = _union_({s1, s2});
T* intersection(T* s1, T* s2)  = {e : e <- s1, e <- s2};
T* difference(T* s1, T* s2)    = {e : e <- s1 ; not in(e, s2)};

T* op_&(T* s1, T* s2) = union(s1, s2);
T* op_-(T* s1, T* s2) = difference(s1, s2);

Bool disjoint(Set s1, Set s2)     = intersection(s1, s2) == {};
Bool subset(Set s1, Set s2)       = s1 - s2 == {};

T* union(T** sets) = _union_(sets);

// T* union(T** sets)
// {
//   ss := rand_sort(sets);
//   u  := {};
//   for (s : ss)
//     u := union(u, s);
//   ;
//   return u;
// }

T* intersection(T** sets)
{
  return {} if sets == {};
  ss  := rand_sort(sets);
  int := ss[0];
  for (i = 1..length(ss)-1)
    int := intersection(int, ss[i]);
  ;
  return int;
}

Nat size(Any* s) = length(rand_sort(s));

Bool is_singleton(Any* s) = size(s) == 1;

T only_element(T* set)
{
  seq := rand_sort(set);
  return seq[0] if length(seq) == 1;
  fail;
}

T only_element(T* set, T default)
{
  seq := rand_sort(set);
  return if length(seq) == 1 then seq[0] else default end;
}

T only_element_or_def_if_empty(T* set, T default)
{
  seq := rand_sort(set);
  len := length(seq);
  
  fail if len > 1;
 
  return if length(seq) == 1 then seq[0] else default end;
}

// Int max(Int+ set)
// {
//   seq := rand_sort(set);
  
//   max := seq[0];
//   for (x : seq)
//     max := x if x > max;
//   ;
  
//   return max;
// }

/////////////////////////////////////////////////////////////////////////////////////////

T* seq_union([T*] sets) = union(set(sets));

/////////////////////////////////////////////////////////////////////////////////////////

T2 op_[]((T1 => T2) map, T1 key) = _lookup_(map, key); // = only_element({v : k => v <- map ; k == key});
 
// T2 lookup((T1 => T2) map, T1 key, T2 default) = only_element_or_def_if_empty({v : k => v <- map ; k == key}, default);

T2 lookup((T1 => T2) map, T1 key, T2 default) = if has_key(map, key) then map[key] else default end;


(T1 => T2) update((T1 => T2) map, (T1 => T2) diffs) = (k => map[k] : k <- keys(map) - keys(diffs)) & diffs;

Nat size((Any => Any) map) = size(keys(map));

T1* keys((T1 => T2) map) = {k : k => _ <- map};

Bool has_key((T1 => T2) map, T1 key) = _has_key_(map, key); // = (? k => _ <- map : k == key);

(T1 => T2) op_&((T1 => T2) map1, (T1 => T2) map2) = _merge_({map1, map2});

// (T1 => T2) op_&((T1 => T2) map1, (T1 => T2) map2)
// {
//   assert {
//     ks1 := keys(map1);
//     ks2 := keys(map2);
    
//     for (k : rand_sort(intersection(ks1, ks2)))
//       return false if map1[k] /= map2[k];
//     ;

//     return true;

//     //disj  := disjoint(ks1, ks2);
//     //
//     //if (not disj)
//     //  print intersection(ks1, ks2);;

//     //return disj;
//   };

//   return (k => v : k => v <- map1 \/ k => v <- map2);
// }

(K => V+) merge_values((K => V)* maps)
{
  all_keys := union({keys(m) : m <- maps});
  return (k => {m[k] : m <- maps ; has_key(m, k)} : k <- all_keys);
}

(K => V+) merge_value_sets((K => V+)* maps) = (k => union(vss) : k => vss <- merge_values(maps));

// (T1 => T2) merge((T1 => T2)* maps) = (k => v : m <- maps, k => v <- m);
(T1 => T2) merge((T1 => T2)* maps) = _merge_(maps);

(T1 => T2) remove_keys((T1 => T2) m, T1* ks) = (k => m[k] : k <- keys(m) - ks);

(T1 => T2) select_by_key((T1 => T2) map, T1* keys) = (k => map[k] : k <- keys);

//#### (T1 => T2) merge((T1 => T2)* maps):
//####   {}          = [->],
//####   {m}         = m,
//####   {ms1 | ms2} = merge(merge(ms1), merge(ms2));
//#### 
//#### [T2 -> {T1+}] reverse([T1 -> {T2+}] map)
//#### {
//####   // HOW TO MAKE THIS EFFICIENT?
//####   vs := union({v : [k, v] <- map});
//####   return [v -> {k : [k, s] <- map ; in(v, s)} : v <- vs];
//#### }

/////////////////////////////////////////////////////////////////////////////////////////

T* set([T] seq) = _set_(seq);

//(T => NzNat) seq_to_multiset(


//## IMPLEMENT A seq_to_multiset FUNCTION AND SEE IF IT CAN BE USED TO IMPLEMENT dupl_elements efficiently

//## THIS IS DIFFICULT TO IMPLEMENT EFFICIENTLY WITHOUT ACCESS TO THE INTERNAL COMPARISON OPERATOR  
T* dupl_elems([T] s)
{
  r := {};
  for (e1, i1 : s ; e2, i2 : s)
    r := r & {e1, e2} if (e1 == e2 and i1 /= i2);
  ;
  return r;
}

Bool has_duplicates([Any] s) = dupl_elems(s) /= {};

[T] rand_sort(T* set) = _isort_(set);

//## Add the result type. Something like: [(TK, TV)]
rand_sort_pairs((TK => TV) map) = rand_sort({[k, v] : k => v <- map});


T an_elem(T+ s) = {ses := rand_sort(s); return ses[0];};

(T => NzNat) set_to_mset(T* s) = (e => 1 : e <- s);

(T => NzNat) multiset_union(T** s) = union({set_to_mset(e) : e <- s});

/////////////////////////////////////////////////////////////////////////////////////////

// using T2 f(T1)
// {
//   (T2 => NzNat) apply(T1* s) = _mset_([f(x) : x <- rand_sort(s)]);
// }

(T => NzNat) bag([T] s) = _mset_(s);

T2* values((T1 => T2) map) = {v : _ => v <- map};

untag(x): tag @ obj = obj;

//## THERE'S A BUG HERE, PROBABLY WHEN ONE OF THE SET OF TARGETS IS EMPTY
(T => T*) transitive_closure((T => T*) map)
{
  assert {
    all_starts := keys(map);
    all_refs   := union(values(map));
    
    missing := all_refs - all_starts;
    
    return true if missing == {};
    print "------------------------------------------------------------------------------";
    print map;
    print missing;
    return false;
  };
  
  closure := map;

  loop
    new_closure := (n => next_step(rs, closure) : n => rs <- closure);
    return closure if (new_closure == closure);
    closure := new_closure;
  ;

  next_step(rs, map) = rs & union({map[r] : r <- rs});
}

/////////////////////////////////////////////////////////////////////////////////////////

using Bool condition(Any)
{
  Any* select_expr_fn(Any obj)
  {
    return {obj} if condition(obj);
    
    return match (obj)
             +          = {},
             *          = {},
             {...}      = union({select_expr_fn(x) : x <- obj}),
             [...]      = union({select_expr_fn(x) : x <- set(obj)}),
             (...)      = union({select_expr_fn(k) & select_expr_fn(v) : k => v <- obj}),
             tag @ iobj = select_expr_fn(iobj); //## SHOULD I EXTEND THE SEARCH TO THE TAG AS WELL?
           ;
  }
}


using Bool condition(Any), Any eval(Any)
{
  Any replace_expr_fn(Any obj)
  {
    return eval(obj) if condition(obj);
    
    return match (obj)
             +          = obj,
             *          = obj, //## BAD
             {...}      = {replace_expr_fn(x) : x <- obj},
             [...]      = [replace_expr_fn(x) : x <- obj],
             (...)      = (replace_expr_fn(k) => replace_expr_fn(v) : k => v <- obj),
             tag @ iobj = tag @ replace_expr_fn(iobj); //## SHOULD I EXTEND THE REPLACEMENT TO THE TAG AS WELL?
           ;
  }
}


[T] intermix([T] seq, T obj)
{
  res := [];  
  for (x : reverse(seq))
    res := [obj | res] if res /= [];
    res := [x | res];
  ;
  return res;
}


String to_str(Int n)
{
  m   := n;
  neg := false;
  if (m < 0)
    m   := -m;
    neg := true;
  ;
  
  assert m >= 0;
  
  div  := 10;
  divs := [1];
  while (div <= m)
    divs := [div | divs];
    div  := 10 * div;
  ;
  
  str := "";

  for (d : divs)
    count := 0;
    while (m >= d)
      m     := m - d;
      count := count + 1;
    ;
    str := str & string([48 + count]); //## UGLY UGLY
  ;

  return if neg then "-" & str else str end;
}

///////////////////////////////////////////////////////////////////////////////

Int to_int(String str)
{
  assert length(str) > 0;
  
  res := 0;
  neg := false;

  for (ch, i : untag(str))
    if (ch == ascii_minus and i == 0)
      neg := true;
      assert length(str) > 1;
    else
      code := ch - 48;
      assert code >= 0 and code <= 9;
      res := 10 * res + code;
    ;
  ;

  return if neg then -res else res end;
}


///////////////////////////////////////////////////////////////////////////////

String to_text(Any obj)
{
  return to_txt(obj);

  String to_txt(Any obj):
    +           = _str_(obj),
    *           = to_str(obj),
    string()    = if obj :: String then quote(obj) else to_txt_tag_obj(:string, _obj_(obj)) end,
    [...]       = "[" & append(intermix([to_txt(x) : x <- obj], ", ")) & "]",
    {...}       = "{" & append(intermix([to_txt(x) : x <- rand_sort(obj)], ", ")) & "}",
    (...)       = to_txt(obj, if keys(obj) :: <Atom*> then ": " else " => " end),
    // tag @ iobj  = to_txt(tag,  iobj);
    tag @ iobj  = to_txt_tag_obj(tag,  iobj);

  String to_txt_tag_obj(Atom tag, Any obj)
  {
    str := to_txt(obj);
    str := "(" & str & ")" if not obj :: Tuple;
    return _str_(tag) & str;
  }
    
  String to_txt(Map map, String key_val_sep)
  {
    es   := rand_sort({(key: k, value: v) : k => v <- map});
    strs := [to_txt(e.key) & key_val_sep & to_txt(e.value) : e <- es];
    return "(" & append(intermix(strs, ", ")) & ")";
  }
}


String quote(String str)
{
  qr_str := [];
  for (ch : untag(str))
    if (ch == 10)   // '\n'
      qr_str := [110, 92 | qr_str];
    elif (ch == 92) // '\\'
      qr_str := [92, 92 | qr_str];
    elif (ch == 34) // '\"'
      qr_str := [34, 92 | qr_str];
    else
      qr_str := [ch | qr_str];
    ;
  ;
  return "\"" & string(reverse(qr_str)) & "\"";
}


String to_text(Any obj, Nat line_len, Nat indent_level)
{
  ind_str := rep_str(2 * indent_level, ascii_space);
  return append(intermix([ind_str & l : l <- to_text(obj, line_len)], "\n"));
}


[String^] to_text(Any obj, Nat line_len)
{
  return to_txt(obj, line_len);

  [String^] to_txt(Any obj, Nat line_len):
    +           = [_str_(obj)],
    *           = [to_str(obj)],
    string()    = if obj :: String then [quote(obj)] else to_txt_tag_obj(:string, _obj_(obj), line_len) end,
    [...]       = to_txt_collection(obj, line_len, "[", "]"),
    {...}       = to_txt_collection(rand_sort(obj), line_len, "{", "}"),
    (...)       = to_txt_map(obj, line_len),
    tag @ iobj  = to_txt_tag_obj(tag, iobj, line_len);

  [String^] to_txt_tag_obj(Atom tag, Any obj, Nat line_len)
  {
    obj_is_tuple := match (obj)
                      (...)   = keys(obj) :: <Atom*>,
                      _       = false;
                    ;
    tag_str      := _str_(tag);
    obj_lines    := to_txt(obj, line_len);
    line_count   := length(obj_lines);
    first_line   := obj_lines[0];

    if (line_count == 1)
      if (obj_is_tuple or length(first_line) + length(tag_str) + 2 <= line_len)
        return [tag_str & if obj_is_tuple then first_line else "(" & first_line & ")" end];
      else
        return [tag_str & "(", "  " & first_line, ")"];
      ;
    else
      middle_lines := subseq(obj_lines, 1, line_count-2);
      last_line    := rev_at(obj_lines, 0);
      if (length(first_line) == 1)
        indent := "";
        head   := [tag_str & if obj_is_tuple then "" else "(" end & first_line];
        tail   := [last_line & if obj_is_tuple then "" else ")" end];
      else
        indent := "  ";
        head := [tag_str & "(", "  " & first_line];
        tail := ["  " & last_line, ")"];
      ;
    ;

    return head & [indent & l : l <- middle_lines] & tail;
  }

  [String^] to_txt_collection(Seq seq, Nat line_len, String left_del, String right_del)
  {
    lines_seq := [to_txt(obj, line_len) : obj <- seq];
    if (all([length(ls) == 1 : ls <- lines_seq]))
      len_sum := sum([length(ls[0]) : ls <- lines_seq]);
      if (len_sum + 2 * length(seq) + 2 < line_len)
        return [left_del & append(intermix([ls[0] : ls <- lines_seq], ", ")) & right_del];
      ;
    ;
    last_idx := length(lines_seq) - 1;
    indented_lines_with_commas := join([["  " & l : l <- if i /= last_idx then append_to_last(ls, ",") else ls end] : ls, i <- lines_seq]);
    return [left_del] & indented_lines_with_commas & [right_del];
  }

  [String^] append_to_last([String^] lines, String str) = [if i /= last_idx then l else l & str end : l, i <- lines] let last_idx := length(lines) - 1;;
  

  [String^] to_txt_map(Map map, Nat line_len)
  {
    is_tuple    := keys(map) :: <Atom*>;
    key_val_sep := if is_tuple then ": " else " => " end;
    size        := size(map);
    es          := rand_sort({(key: k, value: v) : k => v <- map});
    lines       := [];
    single_line := "";
    is_single_line_so_far := true;
    for (e, i : es)
      key_ls := to_txt(e.key, line_len);
      value_ls := to_txt(e.value, line_len);
      // The pair goes in a single line if both key and value must be on a single line and
      // either it's a tuple or the entire pair (including the separator) fits in a single line
      if (length(key_ls) == 1 and length(value_ls) == 1 and (is_tuple or length(key_ls[0]) + length(value_ls[0]) + 2 < line_len))
        ls := [key_ls[0] & key_val_sep & value_ls[0]];
      else
        ls := append_to_last(key_ls, key_val_sep) & value_ls;
      ;
      ls := append_to_last(ls, ",") if i < size - 1;
      lines := lines & ls;
      if (is_single_line_so_far)
        if (length(ls) == 1 and length(single_line) + length(ls[0]) < line_len)
          single_line := single_line & if single_line == "" then "" else " " end & ls[0];
        else
          is_single_line_so_far := false;
        ;
      ;
    ;
    if (is_single_line_so_far)
      return ["(" & single_line & ")"];
    else
      return ["("] & ["  " & l : l <- lines] & [")"];
    ;
  }
}

///////////////////////////////////////////////////////////////////////////////

String string([Int] raw)   = :string(raw); //## SHOULDN't IT BE string([Nat] raw) ?

Nat length(String s)        = length(untag(s));
Nat op_[](String s, Nat n)  = op_[](untag(s), n);

String op_&(String s1, String s2)     = string(untag(s1) & untag(s2));
String append([String] ss)           = string(join([untag(s) : s <- ss]));
String reverse(String s)              = string(reverse(untag(s)));
String substr(String s, Nat n, Nat m) = string(subseq(untag(s), n, m));

String rep_str(Nat len, Nat ch)       = string(rep_seq(len, ch));
<Nat, nil> at(String str, Nat idx)    = at(untag(str), idx, nil);

Bool op_<(String str1, String str2)
{
  len1 := length(str1);
  len2 := length(str2);
  
  min_len := min(len1, len2);
  
  i := 0;
  while (i < min_len)
    ch1 := str1[i];
    ch2 := str2[i];
    
    return true if ch1 < ch2;
    return false if ch1 > ch2;
    
    i := i + 1;
  ;
  
  return len1 < len2;
}

Bool is_digit(Nat ch) = ch >= 48 and ch <= 57;
Bool is_lower(Nat ch) = ch >= 97 and ch <= 122;
Bool is_upper(Nat ch) = ch >= 65 and ch <= 90;

Nat upper(Nat ch) = if is_lower(ch) then ch - 32 else ch end;

String upper(String str) = :string([upper(ch) : ch <- untag(str)]);

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////


type ParType        = parenthesis, bracket, brace;
//type PunctSymb      = left(ParType), right(ParType), underscore, column, comma;
type PunctSymb      = left(ParType), right(ParType), comma, right_arrow;

type Token          = symbol(Atom), label(Atom), Int, String, Char, PunctSymb;

///////////////////////////////////////////////////////////////////////////////

PunctSymb left_parenthesis  = :left(:parenthesis);
PunctSymb right_parenthesis = :right(:parenthesis);

PunctSymb left_bracket      = :left(:bracket);
PunctSymb right_bracket     = :right(:bracket);

PunctSymb left_brace        = :left(:brace);
PunctSymb right_brace       = :right(:brace);

///////////////////////////////////////////////////////////////////////////////

Bool is_space(Int ch) = ch == ascii_space or ch == ascii_newline;

Bool is_symbol(Int ch) = in(ch, {40, 41, 91, 93, 123, 125, 44});

Int ascii_space         = 32;
Int ascii_newline       = 10;
Int ascii_minus         = 45;
Int ascii_underscore    = 95;
Int ascii_column        = 58;
Int ascii_double_quotes = 34;
Int ascii_backslash     = 92;

Int ascii_comma         = 44;

Int ascii_left_parenthesis  = 40;
Int ascii_right_parenthesis = 41;
Int ascii_left_bracket      = 91;
Int ascii_right_bracket     = 93;
Int ascii_left_brace        = 123;
Int ascii_right_brace       = 125;

Token symbol_to_token(Int ch):
  40    = left_parenthesis,
  41    = right_parenthesis,
  91    = left_bracket,
  93    = right_bracket,
  123   = left_brace,
  125   = right_brace,
  44    = :comma;

///////////////////////////////////////////////////////////////////////////////


type LexerError   = lexer_error(line: NzNat, col: NzNat);

//## REMOVE REMOVE REMOVE
symbol(Atom a) = :symbol(a);
label(Atom a)  = :label(a);


//## CURRENTLY IT DOESN'T RECOGNIZE THE RIGHT ARROW

<[Token], LexerError> tokenize([Int] bytes)
//tokenize(bytes)
{
  len        := length(bytes);
  tokens     := [];
  line       := 1;
  line_start := 0;
  
  i := 0;
  while (i < len)
    ch := bytes[i];
    i  := i + 1;
    
    if (is_lower(ch))
      token := [ch];
      while (i < len)
        ch := bytes[i];
        break if not (is_lower(ch) or is_digit(ch) or ch == ascii_underscore);
        token := token & [ch];
        i     := i + 1;
      ;
      if (i < len and bytes[i] == ascii_column)
        tokens := [label(_symb_(string(token))) | tokens];
        i      := i + 1;
      else
        tokens := [symbol(_symb_(string(token))) | tokens];
      ;
    
    elif (ch == ascii_minus or is_digit(ch))
      token := [ch];
      return error(line, i-line_start) if ch == ascii_minus and not (i < len and is_digit(bytes[i]));
      while (i < len and is_digit(bytes[i]))
        token := token & [bytes[i]];
        i     := i + 1;
      ;
      tokens := [to_int(string(token)) | tokens];
    
    elif (ch == ascii_double_quotes)
      rev_str := [];
      while (i < len)
        ch := bytes[i];
        i  := i + 1;

        if (ch == ascii_double_quotes)
          break;

        elif (ch == ascii_backslash)
          return error(line, i-line_start) if not (i < len);
          ch := bytes[i];
          i  := i + 1;
          if (ch == 110) // 'n'
            rev_str := [ascii_newline | rev_str];
          elif (ch == ascii_backslash or ch == ascii_double_quotes)
            rev_str := [ch | rev_str];
          else
            return error(line, i-line_start);
          ;
        
        elif (ch == ascii_newline)
          return error(line, i-line_start);
        
        else
          rev_str := [ch | rev_str];
        ;
      ;
      
      tokens := [string(reverse(rev_str)) | tokens];
    
    elif (is_symbol(ch))
      tokens := [symbol_to_token(ch) | tokens];
    
    else
      return error(line, i-line_start) if not is_space(ch);
      if (ch == ascii_newline)
        line       := line + 1;
        line_start := i;
      ;      
    ;
  ;
  
  return reverse(tokens);


  error(line, col) = lexer_error(line: line, col: col);
}

///////////////////////////////////////////////////////////////////////////////

<[Token], LexerError> fast_tokenize([Int] bytes)
{
  len        := length(bytes);
  tokens     := [];
  line       := 1;
  line_start := 0;
  
  i := 0;
  while (i < len)
    ch := bytes[i];
    i  := i + 1;
    
    if (is_lower(ch))
      token := [ch];
      while (i < len)
        ch := bytes[i];
        break if not (is_lower(ch) or is_digit(ch) or ch == ascii_underscore);
        token := token & [ch];
        i     := i + 1;
      ;
      if (i < len and bytes[i] == ascii_column)
        tokens := [label(_symb_(string(token))), tokens];
        i      := i + 1;
      else
        tokens := [symbol(_symb_(string(token))), tokens];
      ;
    
    elif (ch == ascii_minus or is_digit(ch))
      token := [ch];
      return error(line, i-line_start) if ch == ascii_minus and not (i < len and is_digit(bytes[i]));
      while (i < len and is_digit(bytes[i]))
        token := token & [bytes[i]];
        i     := i + 1;
      ;
      tokens := [to_int(string(token)), tokens];
    
    elif (ch == ascii_double_quotes)
      rev_str := [];
      while (i < len)
        ch := bytes[i];
        i  := i + 1;

        if (ch == ascii_double_quotes)
          break;

        elif (ch == ascii_backslash)
          return error(line, i-line_start) if not (i < len);
          ch := bytes[i];
          i  := i + 1;
          if (ch == 110) // 'n'
            rev_str := [ascii_newline | rev_str];
          elif (ch == ascii_backslash or ch == ascii_double_quotes)
            rev_str := [ch | rev_str];
          else
            return error(line, i-line_start);
          ;
        
        elif (ch == ascii_newline)
          return error(line, i-line_start);
        
        else
          rev_str := [ch | rev_str];
        ;
      ;
      
      tokens := [string(reverse(rev_str)), tokens];
    
    elif (is_symbol(ch))
      tokens := [symbol_to_token(ch), tokens];
    
    else
      return error(line, i-line_start) if not is_space(ch);
      if (ch == ascii_newline)
        line       := line + 1;
        line_start := i;
      ;      
    ;
  ;
  
  return reverse(_list_to_seq_(tokens));


  error(line, col) = lexer_error(line: line, col: col);
}

///////////////////////////////////////////////////////////////////////////////

type ParseError       = parser_error(token: Nat);
type ParseSuccess     = obj(Any);
type ParseResult      = ParseSuccess, ParseError;
type MultParseResult  = [ParseSuccess], ParseError;

type ParseIntermRes     = (obj: Any, offset: Nat);//, ParseError;
type ParseIntermMultRes = (objs: [Any], offset: Nat);//, ParseError;



ParseResult parse_obj([Token] tokens)
{
  return error(0) if tokens == [];
  res := parse_obj(tokens, 0);
  return res if res :: ParseError;
  return error(res.offset) if res.offset /= length(tokens);
  return :obj(res.obj);
    
  error(token) = parser_error(token: token);

  //ParseIntermRes parse_obj([Token^] tokens, Nat offset)
  parse_obj(tokens, offset)
  {
    assert offset < length(tokens);

    res := match (tokens[offset])
             symbol()                 = parse_tagged_obj_or_symbol(tokens, offset),
             // <Int, String, Char> obj  = (obj: obj, offset: offset+1),
             Int obj                  = (obj: obj, offset: offset+1), //## SHOULD USE A PATTERN UNION HERE ONCE IT IS IMPLEMENTED
             Char obj                 = (obj: obj, offset: offset+1),
             string() obj             = (obj: obj, offset: offset+1),
             left(:brace)             = parse_set(tokens, offset),
             left(:parenthesis)       = parse_map_or_tuple(tokens, offset),
             left(:bracket)           = parse_seq(tokens, offset),
             _                        = error(offset);
           ;
    
    return res;
  }

  //ParseIntermRes parse_tagged_obj_or_symbol([Token^] tokens, Nat offset)
  parse_tagged_obj_or_symbol(tokens, offset)
  {
    assert offset < length(tokens) and tokens[offset] :: <symbol(Atom)>;

    if (at(tokens, offset+1, nil) /= left_parenthesis)
      return (obj: untag(tokens[offset]), offset: offset+1);
    ;

    res := parse_map_or_tuple(tokens, offset+1);
    is_tuple := not res :: ParseError;
    if (not is_tuple)
      res := parse_obj(tokens, offset+2);
      return res if res :: ParseError;
      return error(res.offset) if at(tokens, res.offset, nil) /= right_parenthesis;
    ;
    
    obj := untag(tokens[offset]) @ res.obj;
    return (obj: obj, offset: res.offset + if is_tuple then 0 else 1 end);
  }

  //ParseIntermRes parse_set([Token^] tokens, Nat offset)
  parse_set(tokens, offset)
  {
    assert offset < length(tokens) and tokens[offset] == left_brace;

    res := parse_objs(tokens, offset+1, right_brace);
    return res if res :: ParseError;

    return (obj: set(res.objs), offset: res.offset);
  }

  //ParseIntermRes parse_seq([Token^] tokens, Nat offset)
  parse_seq(tokens, offset)
  {
    assert offset < length(tokens);
    assert tokens[offset] == left_bracket;

    res := parse_objs(tokens, offset+1, right_bracket);
    return res if res :: ParseError;

    return (obj: res.objs, offset: res.offset);
  }
  
  //<ParseIntermRes, ParseError> parse_map_or_tuple([Token^] tokens, Nat offset)
  parse_map_or_tuple(tokens, offset)
  {
    assert offset < length(tokens) and tokens[offset] == left_parenthesis;
    
    len := length(tokens);
    os  := offset + 1;
    
    is_tuple := at(tokens, os, nil) :: <label(Atom)>;
    
    keys   := [];
    values := [];

    loop
      return error(os) if os >= len;
      head := tokens[os];
      break if head == right_parenthesis;
      
      if (is_tuple)
        return error(os) if not head :: <label(Atom)>;
        key    := untag(head);
        val_os := os + 1;

      else
        res := parse_obj(tokens, os);
        return res if res :: ParseError;
        return error(res.offset) if at(tokens, res.offset, nil) /= :right_arrow;
        key    := res.obj;
        val_os := res.offset + 1;
      ;

      return error(os) if in(key, keys);

      res := parse_obj(tokens, val_os);
      return res if res :: ParseError;
      
      keys   := [key | keys];
      values := [res.obj | values];
      
      os   := res.offset;
      head := at(tokens, os, nil);
      
      if (head == :comma)
        os := os + 1;
      elif (head /= right_parenthesis)
        return error(os);
      ;
    ;

    obj := (k => values[index_first(k, keys)] : k <- set(keys)); //## BAD

    return (obj: obj, offset: os+1);
  }

  //ParseIntermMultRes parse_objs([Token^] tokens, Nat offset, Token eof)
  parse_objs(tokens, offset, eof)
  {
    len  := length(tokens);
    os   := offset;
    objs := [];
    
    loop
      break if at(tokens, os, nil) == eof; //## NOT SURE, WHAT IF Token WHERE MADE TO INCLUDE nil?
      
      res := parse_obj(tokens, os);
      return res if res :: ParseError;
      
      objs := objs & [res.obj];
      os   := res.offset;
      head := at(tokens, os, nil);
      
      if (head == :comma)
        os := os + 1;
      else
        return error(os) if head /= eof;
      ;
    ;
    
    return (objs: objs, offset: os+1);
  }
}
