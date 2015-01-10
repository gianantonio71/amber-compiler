
type Bool           = true, false;

type Nat            = [0..*];
type Int            = [*..*];
type NzNat          = [1..*];
//type NzInt          = [1..*], [*..-1];
type NegInt         = [*..-1];

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

type Record         = (Atom => Any);
type Map            = (Any => Any);

type TagObj         = (<+> @ Any);

type Char           = char(Nat);
type String         = string([Nat]);

type Maybe[T]       = nil, just(T);

type Result[TS, TF] = success(TS), failure(TF);

type List[T]        = nil, list(head: T, tail: List[T]);

type Stack[T]       = nil, stack(top: T, rest: Stack[T]);

////////////////////////////////////////////////////////////////////////////////

Stack[T] push(Stack[T] stack, T item) = stack(top: item, rest: stack);

Stack[T] pop(Stack[T] stack):
  stack()   = stack.rest,
  _         = {fail;};

T peek(Stack[T] stack):
  stack()   = stack.top,
  _         = {fail;};

Stack[T] replace_top(Stack[T] stack, T new_top):
  stack()   = push(stack.rest, new_top),
  _         = {fail;};

////////////////////////////////////////////////////////////////////////////////

// Replace this with === or ~=
Bool is_eq(T x, Maybe[T] maybe) = maybe == :just(x);

Maybe[T] just(T x) = :just(x);

T value(Maybe[T]):
  just(x?)  = x,
  _         = {fail;};

Maybe[T] maybe(T x, Bool cond) = if cond then :just(x) else nil end;

////////////////////////////////////////////////////////////////////////////////

<success(T)> success(T r) = :success(r);
<failure(T)> failure(T e) = :failure(e);

Bool is_success(Result[TS, TF]):
  success()   = true,
  failure()   = false;

Bool is_failure(Result[TS, TF]):
  success()   = false,
  failure()   = true;

TS get_result(Result[TS, TF]):
  success(r?) = r,
  _           = {fail;};

TF get_error(Result[TS, TF]):
  failure(e?) = e,
  _           = {fail;};

////////////////////////////////////////////////////////////////////////////////

// Still not ideal, both of them. No need to always evaluate all arguments.
Bool some(Bool+ bs) = (? b <- bs : b);
Bool all(Bool+ bs)  = not (? b <- bs : not b);

// No element is false
Bool all([Bool] s)   = not in(false, s);

// No element is true
Bool none([Bool] s)  = not in(true, s);

// At least one element is true
Bool at_least_one([Bool] s)  = in(true, s);

// At least one element is false
Bool not_all([Bool^] s) = in(true, s);

////////////////////////////////////////////////////////////////////////////////

Nat bit(Bool b) = if b then 1 else 0 end;

////////////////////////////////////////////////////////////////////////////////

Int (-_)  (Int n)         = _neg_(n);
Int (_+_) (Int a, Int b)  = _add_(a, b);
Int (_-_) (Int a, Int b)  = _sub_(a, b);
Int (_*_) (Int a, Int b)  = _mult_(a, b);
Int (_/_) (Int a, Int b)  = _div_(a, b);

Int mod(Int a, Int b)     = _mod_(a, b);

Bool (_<_) (Int a, Int b) = (b - a) :: [1..*];

Bool (_>_)  (Int a, Int b) = b < a;
Bool (_>=_) (Int a, Int b) = a > b or a == b;
Bool (_<=_) (Int a, Int b) = a < b or a == b;

Int min(Int a, Int b) = if a < b then a else b end;
Int max(Int a, Int b) = if a > b then a else b end;

Int min(Int+ ns)
{
  ns_seq = rand_sort(ns);
  min = ns_seq[0];
  for (n : ns_seq)
    min = n if n < min;
  ;
  return min;
}

Int max(Int+ ns)
{
  ns_seq = rand_sort(ns);
  max = ns_seq[0];
  for (n : ns_seq)
    max = n if n > max;
  ;
  return max;
}

Int sum([Int] ns)
{
  res = 0;
  for (n : ns)
    res = res + n;
  ;
  return res;
}

////////////////////////////////////////////////////////////////////////////////

// Should it be defined for empty sequences (and negative integers)
// as well? It's always going to fail...

//T (_[_]) ([T^] seq, Nat idx) = _at_(seq, idx);
(_[_])(Seq seq, Nat idx) = _at_(seq, idx); //## BAD BAD BAD

T rev_at([T^] seq, Nat idx) = _at_(seq, _len_(seq)-idx-1);

Nat length(Seq seq) = _len_(seq);

T at([T^] seq, Nat idx, T default) = if idx < _len_(seq) then _at_(seq, idx) else default end;

T1 left((T1, T2) s)  = _at_(s, 0);
T2 right((T1, T2) s) = _at_(s, 1);

[(T1, T2)] zip([T1] s1, [T2] s2)
{
  assert length(s1) == length(s2);
  return [(e1, s2[i]) : e1 @ i <- s1]; //## NOT PARTICULARLY ELEGANT...
}

[(T1, T2, T3)] zip([T1] s1, [T2] s2, [T3] s3)
{
  assert length(s1) == length(s2) and length(s2) == length(s3);
  return [(e1, s2[i], s3[i]) : e1 @ i <- s1]; //## NOT PARTICULARLY ELEGANT...

}

([T1], [T2]) unzip([(T1, T2)] ts) = ([left(t) : t <- ts], [right(t) : t <- ts]); //## NOT PARTICULARLY ELEGANT EITHER...

T head([T^] s) = _at_(s, 0);
T tail([T^] s) = _slice_(s, 1, _len_(s)-1);
T last([T^] s) = _at_(s, _len_(s)-1);

Bool is_valid_idx(Seq seq, Int idx) = idx >= 0 and idx < length(seq);

(_&_)(Seq s1, Seq s2) = _cat_(s1, s2);

Bool in(Any e, Seq s)
{
  for (x : s)
    return true if x == e;
  ;
  return false;
}

Nat index_first(Any e, Seq s)
{
  for (x @ i : s)
    return i if x == e;
  ;
  fail;
}

[T] join([[T]] seqs) = _mcat_(seqs);

reverse(Seq seq) = _rev_(seq);

[T] right_subseq([T] seq, Nat first) = _slice_(seq, first, length(seq) - first);

[T] subseq([T] seq, Nat first, Nat count) = _slice_(seq, first, count);

[T] subseq([T] s, <nil>, Nat m, Nat r) = subseq(s, length(s)-m-r, m);
[T] subseq([T] s, Nat l, <nil>, Nat r) = subseq(s, l, length(s)-l-r);
[T] subseq([T] s, Nat l, Nat m, <nil>) = subseq(s, l, m);


[[T]] split([T] seq, T sep)
{
  len = length(seq);
  subseqs = [];
  start = 0;
  for (x @ i : seq)
    if (x == sep)
      subseqs = subseqs & [subseq(seq, start, i-start)];
      start = i + 1;
    ;
  ;
  subseqs = subseqs & [subseq(seq, start, len-start)] if start < len;
  return subseqs;
}


Maybe[Nat] left_search(Seq seq, Seq subseq)
{
  last_idx = length(seq) - length(subseq);
  for (i : inc_seq(max(0, last_idx+1)))
    return just(i) if subseq_matches(seq, subseq, i);
  ;
  return nil;

  Bool subseq_matches(Seq seq, Seq subseq, Nat offset)
  {
    for (i : indexes(subseq))
      return false if seq[offset+i] /= subseq[i];
    ;
    return true;
  }
}


[T] (_*_)(Nat count, [T] seq)
{
  l = length(seq);
  res = [];
  for (i : inc_seq(count))
    for (x : seq)
      res = res & [x];
    ;
  ;
  return res;
}

[T] rep_seq(Nat size, T value)
{
  n = 0;
  s = [];
  while (n < size)
    s = s & [value];
    n = n + 1;
  ;
  return s;
}

[Nat] inc_seq(Nat n) = inc_seq(0, n, 1);

[Nat] inc_seq(Nat m, Nat n) = inc_seq(m, n, 1);

[Nat] inc_seq(Nat m, Nat n, NzNat s)
{
  r = [];
  i = m;
  while (i < n)
    r = r & [i];
    i = i + s;
  ;
  return r;
}

[Nat] dec_seq(Nat n) = reverse(inc_seq(n));

[Nat] indexes(Seq s) = inc_seq(length(s));

[Nat] indexes(Seq s, Nat m) = inc_seq(m, length(s));

Nat* index_set(Seq s) = set(indexes(s));

[Bool] bit_map([Int] idxs, Nat len) = [in(i, idxs) : i < len]; //## BAD: HORRIBLY INEFFICIENT

//## BAD: THE NAME IS TOTALLY MEANINGLESS, AND THE IMPLEMENTATION IS INEFFICIENT
[Maybe[Nat]] packed_indexes([Bool] bs)
{
  idxs = [];
  for (b : bs)
    idxs = idxs & [if b then just(length(idxs)) else nil end];
  ;
  return idxs;
}

using Bool is_strictly_ordered(T, T) //## BAD BAD BAD
{
  [T] sort_set(T* s) = sort(rand_sort(s));

  [T] sort([T] s) = mergesort(s);

  [T] mergesort([T] seq)
  {
    len = length(seq);
    return seq if len <= 1;
    ss = [[x] : x <- seq];
    while (len > 1)
      nss = [];
      idx = 0;
      //## BAD BAD BAD DOESN'T WORK WELL WITH A ROPE
      while (len > idx+1)
        nss = [merge(ss[idx], ss[idx+1])] & nss;
        idx = idx + 2;
      ;
      assert idx == length(ss) or idx == length(ss) - 1;
      ss  = if len > idx then [ss[idx]] & nss else nss end;
      len = length(ss); //## SHOULD BE len = (len + 1) / 2;
    ;
    return ss[0];

    [T] merge([T] seq1, [T] seq2)
    {
      l1 = length(seq1);
      l2 = length(seq2);
      rs = [];
      i1 = 0;
      i2 = 0;
      while (i1 < l1 or i2 < l2)
        if (i1 == l1 or (i2 < l2 and is_strictly_ordered(seq2[i2], seq1[i1])))
          rs = [seq2[i2]] & rs;
          i2 = i2 + 1;
        else
          rs = [seq1[i1]] & rs;
          i1 = i1 + 1;
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
T* difference(T* s1, T* s2)    = {e : e <- s1, not in(e, s2)};

T* (_&_)(T* s1, T* s2) = union(s1, s2);
T* (_-_)(T* s1, T* s2) = difference(s1, s2);

Bool disjoint(Set s1, Set s2)     = intersection(s1, s2) == {};
Bool subset(Set s1, Set s2)       = s1 - s2 == {};

T* union(T** sets) = _union_(sets);

// T* union(T** sets)
// {
//   ss = rand_sort(sets);
//   u  = {};
//   for (s : ss)
//     u = union(u, s);
//   ;
//   return u;
// }

T* intersection(T** sets)
{
  return {} if sets == {};
  ss  = rand_sort(sets);
  int = ss[0];
  for (i = 1..length(ss)-1)
    int = intersection(int, ss[i]);
  ;
  return int;
}

Nat size(Any* s) = length(rand_sort(s));

Bool is_singleton(Any* s) = size(s) == 1;

T only_element(T* set)
{
  seq = rand_sort(set);
  return seq[0] if length(seq) == 1;
  fail;
}

T only_element(T* set, T default)
{
  seq = rand_sort(set);
  return if length(seq) == 1 then seq[0] else default end;
}

T only_element_or_def_if_empty(T* set, T default)
{
  seq = rand_sort(set);
  len = length(seq);

  fail if len > 1;

  return if length(seq) == 1 then seq[0] else default end;
}

// Int max(Int+ set)
// {
//   seq = rand_sort(set);

//   max = seq[0];
//   for (x : seq)
//     max = x if x > max;
//   ;

//   return max;
// }

/////////////////////////////////////////////////////////////////////////////////////////

T* seq_union([T*] sets) = union(set(sets));

/////////////////////////////////////////////////////////////////////////////////////////

T2 (_[_])((T1 => T2) map, T1 key) = _lookup_(map, key); // = only_element({v : k => v <- map ; k == key});

// T2 lookup((T1 => T2) map, T1 key, T2 default) = only_element_or_def_if_empty({v : k => v <- map ; k == key}, default);

T2 lookup((T1 => T2) map, T1 key, T2 default) = if has_key(map, key) then map[key] else default end;


(T1 => T2) update((T1 => T2) map, (T1 => T2) diffs) = (k => map[k] : k <- keys(map) - keys(diffs)) & diffs;

Nat size((Any => Any) map) = size(keys(map));

T1* keys((T1 => T2) map) = {k : k => _ <- map};

Bool has_key((T1 => T2) map, T1 key) = _has_key_(map, key); // = (? k => _ <- map : k == key);

(T1 => T2) (_&_)((T1 => T2) map1, (T1 => T2) map2) = _merge_({map1, map2});

// (T1 => T2) (_&_)((T1 => T2) map1, (T1 => T2) map2)
// {
//   assert {
//     ks1 = keys(map1);
//     ks2 = keys(map2);

//     for (k : rand_sort(intersection(ks1, ks2)))
//       return false if map1[k] /= map2[k];
//     ;

//     return true;

//     //disj  = disjoint(ks1, ks2);
//     //
//     //if (not disj)
//     //  print intersection(ks1, ks2);;

//     //return disj;
//   };

//   return (k => v : k => v <- map1 \/ k => v <- map2);
// }

(K => V+) merge_values((K => V)* maps)
{
  all_keys = union({keys(m) : m <- maps});
  return (k => {m[k] : m <- maps, has_key(m, k)} : k <- all_keys);
}

(K => V+) merge_value_sets((K => V+)* maps) = (k => union(vss) : k => vss <- merge_values(maps));

// (T1 => T2) merge((T1 => T2)* maps) = (k => v : m <- maps, k => v <- m);
(T1 => T2) merge((T1 => T2)* maps) = _merge_(maps);

(T1 => T2) remove_keys((T1 => T2) m, T1* ks) = (k => m[k] : k <- keys(m) - ks);

(T1 => T2) select_by_key((T1 => T2) map, T1* keys) = (k => map[k] : k <- keys);

// [T2 -> {T1+}] reverse([T1 -> {T2+}] map)
// {
//   // HOW TO MAKE THIS EFFICIENT?
//   vs = union({v : [k, v] <- map});
//   return [v -> {k : [k, s] <- map ; in(v, s)} : v <- vs];
// }

/////////////////////////////////////////////////////////////////////////////////////////

T* set([T] seq) = _set_(seq);

//(T => NzNat) seq_to_multiset(


//## IMPLEMENT A seq_to_multiset FUNCTION AND SEE IF IT CAN BE USED TO IMPLEMENT dupl_elements efficiently

//## THIS IS DIFFICULT TO IMPLEMENT EFFICIENTLY WITHOUT ACCESS TO THE INTERNAL COMPARISON OPERATOR
T* dupl_elems([T] s)
{
  r = {};
  for (e1 @ i1 : s ; e2 @ i2 : s)
    r = r & {e1, e2} if (e1 == e2 and i1 /= i2);
  ;
  return r;
}

Bool has_duplicates([Any] s) = dupl_elems(s) /= {};

[T] rand_sort(T* set) = _isort_(set);

[(TK, TV)] rand_sort_pairs((TK => TV) map) = rand_sort({(k, v) : k => v <- map});


T an_elem(T+ s) = {ses = rand_sort(s); return ses[0];};

(T => NzNat) set_to_mset(T* s) = (e => 1 : e <- s);

(T => NzNat) multiset_union(T** s) = union({set_to_mset(e) : e <- s});

/////////////////////////////////////////////////////////////////////////////////////////

// using T2 f(T1)
// {
//   (T2 => NzNat) apply(T1* s) = _mset_([f(x) : x <- rand_sort(s)]);
// }

(T => NzNat) bag([T] s) = _mset_(s);

T2* values((T1 => T2) map) = {v : _ => v <- map};

//## THERE'S A BUG HERE, PROBABLY WHEN ONE OF THE SET OF TARGETS IS EMPTY
(T => T*) transitive_closure((T => T*) map)
{
  assert {
    all_starts = keys(map);
    all_refs   = union(values(map));

    missing = all_refs - all_starts;

    return true if missing == {};
    print "------------------------------------------------------------------------------";
    print map;
    print missing;
    return false;
  };

  closure = map;

  loop
    new_closure = (n => next_step(rs, closure) : n => rs <- closure);
    return closure if (new_closure == closure);
    closure = new_closure;
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


[T] intermix([T] seq, T obj) = join([[obj if i /= 0, e] : e @ i <- seq]);

///////////////////////////////////////////////////////////////////////////////

String to_str(Int n)
{
  m   = n;
  neg = false;
  if (m < 0)
    m   = -m;
    neg = true;
  ;

  assert m >= 0;

  div  = 10;
  divs = [1];
  while (div <= m)
    divs = [div] & divs;
    div  = 10 * div;
  ;

  str = "";

  for (d : divs)
    count = 0;
    while (m >= d)
      m     = m - d;
      count = count + 1;
    ;
    str = str & string([ascii_0 + count]);
  ;

  return if neg then "-" & str else str end;
}


String float_to_str(Int mantissa, Int dec_exp)
{
  mant_str = to_str(mantissa);
  shift = -dec_exp;
  padd_zeros = max(0, shift + 1 - length(mant_str));
  mant_str = append(padd_zeros * ["0"]) & mant_str;
  left = substr(mant_str, 0, nil, shift);
  right = substr(mant_str, nil, shift, 0);
  return left & "." & right;
}

///////////////////////////////////////////////////////////////////////////////

Int to_int(String str)
{
  assert length(str) > 0;

  res = 0;
  neg = false;

  for (ch @ i : _obj_(str))
    if (ch == ascii_minus and i == 0)
      neg = true;
      assert length(str) > 1;
    else
      code = ch - ascii_0;
      assert code >= 0 and code <= 9;
      res = 10 * res + code;
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
    ^           = float_to_str(_mantissa_(obj), _dec_exp_(obj)),
    string()    = if obj :: String then quote(obj) else to_txt_tag_obj(:string, _obj_(obj)) end,
    [...]       = "[" & append(intermix([to_txt(x) : x <- obj], ", ")) & "]",
    {...}       = "{" & append(intermix([to_txt(x) : x <- rand_sort(obj)], ", ")) & "}",
    (...)       = to_txt(obj, if keys(obj) :: <Atom*> then ": " else " => " end),
    // tag @ iobj  = to_txt(tag,  iobj);
    tag @ iobj  = to_txt_tag_obj(tag,  iobj);

  String to_txt_tag_obj(Atom tag, Any obj)
  {
    str = to_txt(obj);
    str = "(" & str & ")" if not obj :: Record;
    return _str_(tag) & str;
  }

  String to_txt(Map map, String key_val_sep)
  {
    es   = rand_sort({(key: k, value: v) : k => v <- map});
    strs = [to_txt(e.key) & key_val_sep & to_txt(e.value) : e <- es];
    return "(" & append(intermix(strs, ", ")) & ")";
  }
}


String quote(String str)
{
  qstr = [];
  for (ch : _obj_(str))
    if (ch == ascii_newline)
      qchs = [ascii_backslash, ascii_lower_n];
    elif (ch == ascii_backslash)
      qchs = [ascii_backslash, ascii_backslash];
    elif (ch == ascii_double_quotes)
      qchs = [ascii_backslash, ascii_double_quotes];
    else
      qchs = [ch];
    ;

    qstr = qstr & qchs;
  ;
  return "\"" & string(qstr) & "\"";
}


String to_text(Any obj, Nat line_len, Nat indent_level)
{
  ind_str = rep_str(2 * indent_level, ascii_space);
  return append(intermix([ind_str & l : l <- to_text(obj, line_len)], "\n"));
}


[String^] to_text(Any obj, Nat line_len)
{
  return to_txt(obj, line_len);

  [String^] to_txt(Any obj, Nat line_len):
    +           = [_str_(obj)],
    *           = [to_str(obj)],
    ^           = [float_to_str(_mantissa_(obj), _dec_exp_(obj))],
    string()    = if obj :: String then [quote(obj)] else to_txt_tag_obj(:string, _obj_(obj), line_len) end,
    [...]       = to_txt_collection(obj, line_len, "[", "]"),
    {...}       = to_txt_collection(rand_sort(obj), line_len, "{", "}"),
    (...)       = to_txt_map(obj, line_len),
    tag @ iobj  = to_txt_tag_obj(tag, iobj, line_len);

  [String^] to_txt_tag_obj(Atom tag, Any obj, Nat line_len)
  {
    obj_is_record = match (obj)
                      (...)   = keys(obj) :: <Atom*>,
                      _       = false;
                    ;
    tag_str      = _str_(tag);
    obj_lines    = to_txt(obj, line_len);
    line_count   = length(obj_lines);
    first_line   = obj_lines[0];

    if (line_count == 1)
      if (obj_is_record or length(first_line) + length(tag_str) + 2 <= line_len)
        return [tag_str & if obj_is_record then first_line else "(" & first_line & ")" end];
      else
        return [tag_str & "(", "  " & first_line, ")"];
      ;
    else
      middle_lines = subseq(obj_lines, 1, line_count-2);
      last_line    = rev_at(obj_lines, 0);
      if (length(first_line) == 1)
        indent = "";
        head   = [tag_str & if obj_is_record then "" else "(" end & first_line];
        tail   = [last_line & if obj_is_record then "" else ")" end];
      else
        indent = "  ";
        head = [tag_str & "(", "  " & first_line];
        tail = ["  " & last_line, ")"];
      ;
    ;

    return head & [indent & l : l <- middle_lines] & tail;
  }

  [String^] to_txt_collection(Seq seq, Nat line_len, String left_del, String right_del)
  {
    lines_seq = [to_txt(obj, line_len) : obj <- seq];
    if (all([length(ls) == 1 : ls <- lines_seq]))
      len_sum = sum([length(ls[0]) : ls <- lines_seq]);
      if (len_sum + 2 * length(seq) + 2 < line_len)
        return [left_del & append(intermix([ls[0] : ls <- lines_seq], ", ")) & right_del];
      ;
    ;
    last_idx = length(lines_seq) - 1;
    indented_lines_with_commas = join([["  " & l : l <- if i /= last_idx then append_to_last(ls, ",") else ls end] : ls @ i <- lines_seq]);
    return [left_del] & indented_lines_with_commas & [right_del];
  }

  // [String^] append_to_last([String^] lines, String str) = [if i /= last_idx then l else l & str end : l @ i <- lines] let last_idx = length(lines) - 1;;
  [String^] append_to_last([String^] lines, String str)
  {
    last_idx = length(lines) - 1;
    return [if i /= last_idx then l else l & str end : l @ i <- lines];
  }

  [String^] to_txt_map(Map map, Nat line_len)
  {
    is_record   = keys(map) :: <Atom*>;
    key_val_sep = if is_record then ": " else " => " end;
    size        = size(map);
    es          = rand_sort({(key: k, value: v) : k => v <- map});
    lines       = [];
    single_line = "";
    is_single_line_so_far = true;
    for (e @ i : es)
      key_ls = to_txt(e.key, line_len);
      value_ls = to_txt(e.value, line_len);
      // The pair goes in a single line if both key and value must be on a single line and
      // either it's a record or the entire pair (including the separator) fits in a single line
      if (length(key_ls) == 1 and length(value_ls) == 1 and (is_record or length(key_ls[0]) + length(value_ls[0]) + 2 < line_len))
        ls = [key_ls[0] & key_val_sep & value_ls[0]];
      else
        ls = append_to_last(key_ls, key_val_sep) & value_ls;
      ;
      ls = append_to_last(ls, ",") if i < size - 1;
      lines = lines & ls;
      if (is_single_line_so_far)
        if (length(ls) == 1 and length(single_line) + length(ls[0]) < line_len)
          single_line = single_line & if single_line == "" then "" else " " end & ls[0];
        else
          is_single_line_so_far = false;
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

String string([Int] raw)      = :string(raw); //## SHOULDN't IT BE string([Nat] raw) ?

Nat length(String s)          = length(_obj_(s));
Nat (_[_]) (String s, Nat n)  = (_[_])(_obj_(s), n);

String (_&_) (String s1, String s2)   = string(_obj_(s1) & _obj_(s2));
String append([String] ss)            = string(join([_obj_(s) : s <- ss]));
String reverse(String s)              = string(reverse(_obj_(s)));
String substr(String s, Nat n, Nat m) = string(subseq(_obj_(s), n, m));

String substr(String s, <Nat, nil> l, <Nat, nil> m, <Nat, nil> r) = string(subseq(_obj_(s), l, m, r));

String rep_str(Nat len, Nat ch)       = string(rep_seq(len, ch));
<Nat, nil> at(String str, Nat idx)    = at(_obj_(str), idx, nil);

Bool (_<_)(String str1, String str2)
{
  len1 = length(str1);
  len2 = length(str2);

  min_len = min(len1, len2);

  i = 0;
  while (i < min_len)
    ch1 = str1[i];
    ch2 = str2[i];

    return true if ch1 < ch2;
    return false if ch1 > ch2;

    i = i + 1;
  ;

  return len1 < len2;
}

Bool is_digit(Nat ch) = ch >= ascii_0 and ch <= ascii_9;
Bool is_lower(Nat ch) = ch >= ascii_lower_a and ch <= ascii_lower_z;
Bool is_upper(Nat ch) = ch >= ascii_upper_a and ch <= ascii_upper_z;

Bool is_space(Int ch) = ch == ascii_space or ch == ascii_tab or ch == ascii_newline or ch == ascii_carriage_return;

Bool is_ascii_symbol(Nat ch) = (ch >= ascii_exclamation_mark and ch <= ascii_slash)     or
                               (ch >= ascii_colon            and ch <= ascii_at)        or
                               (ch >= ascii_left_bracket     and ch <= ascii_backquote) or
                               (ch >= ascii_left_brace       and ch <= ascii_tilde);

Bool is_ascii_printable(Nat ch) = ch >= ascii_space and ch <= ascii_tilde;

Bool is_lower_or_digit(Nat ch) = is_lower(ch) or is_digit(ch);

Nat lower(Nat ch) = if is_upper(ch) then ch + 32 else ch end;
Nat upper(Nat ch) = if is_lower(ch) then ch - 32 else ch end;

String lower(String str) = :string([lower(ch) : ch <- _obj_(str)]);
String upper(String str) = :string([upper(ch) : ch <- _obj_(str)]);

///////////////////////////////////////////////////////////////////////////////

Nat ascii_null              = 0;
Nat ascii_tab               = 9;
Nat ascii_newline           = 10;
Nat ascii_carriage_return   = 13;

Nat ascii_space             = 32;
Nat ascii_exclamation_mark  = 33;
Nat ascii_double_quotes     = 34; // quotation marks, quote, double quote
Nat ascii_hash              = 35;
Nat ascii_dollar            = 36;
Nat ascii_percent           = 37; // percent sign
Nat ascii_ampersand         = 38;
Nat ascii_single_quote      = 39;
Nat ascii_left_parenthesis  = 40;
Nat ascii_right_parenthesis = 41;
Nat ascii_asterisk          = 42;
Nat ascii_plus              = 43;
Nat ascii_comma             = 44;
Nat ascii_minus             = 45; // dash, hyphen
Nat ascii_dot               = 46; // period, point, decimal point
Nat ascii_slash             = 47;
Nat ascii_0                 = 48;
Nat ascii_1                 = 49;
Nat ascii_2                 = 50;
Nat ascii_3                 = 51;
Nat ascii_4                 = 52;
Nat ascii_5                 = 53;
Nat ascii_6                 = 54;
Nat ascii_7                 = 55;
Nat ascii_8                 = 56;
Nat ascii_9                 = 57;
Nat ascii_colon             = 58;
Nat ascii_semicolon         = 59;
Nat ascii_lower             = 60; // less than, bra
Nat ascii_equals            = 61;
Nat ascii_greater           = 62; // greater than, ket
Nat ascii_question_mark     = 63;
Nat ascii_at                = 64;
Nat ascii_upper_a           = 65;
Nat ascii_upper_b           = 66;
Nat ascii_upper_c           = 67;
Nat ascii_upper_d           = 68;
Nat ascii_upper_e           = 69;
Nat ascii_upper_f           = 70;
Nat ascii_upper_g           = 71;
Nat ascii_upper_h           = 72;
Nat ascii_upper_i           = 73;
Nat ascii_upper_j           = 74;
Nat ascii_upper_k           = 75;
Nat ascii_upper_l           = 76;
Nat ascii_upper_m           = 77;
Nat ascii_upper_n           = 78;
Nat ascii_upper_o           = 79;
Nat ascii_upper_p           = 80;
Nat ascii_upper_q           = 81;
Nat ascii_upper_r           = 82;
Nat ascii_upper_s           = 83;
Nat ascii_upper_t           = 84;
Nat ascii_upper_u           = 85;
Nat ascii_upper_v           = 86;
Nat ascii_upper_w           = 87;
Nat ascii_upper_x           = 88;
Nat ascii_upper_y           = 89;
Nat ascii_upper_z           = 90;
Nat ascii_left_bracket      = 91;
Nat ascii_backslash         = 92;
Nat ascii_right_bracket     = 93;
Nat ascii_circumflex        = 94;
Nat ascii_underscore        = 95;
Nat ascii_backquote         = 96;
Nat ascii_lower_a           = 97;
Nat ascii_lower_b           = 98;
Nat ascii_lower_c           = 99;
Nat ascii_lower_d           = 100;
Nat ascii_lower_e           = 101;
Nat ascii_lower_f           = 102;
Nat ascii_lower_g           = 103;
Nat ascii_lower_h           = 104;
Nat ascii_lower_i           = 105;
Nat ascii_lower_j           = 106;
Nat ascii_lower_k           = 107;
Nat ascii_lower_l           = 108;
Nat ascii_lower_m           = 109;
Nat ascii_lower_n           = 110;
Nat ascii_lower_o           = 111;
Nat ascii_lower_p           = 112;
Nat ascii_lower_q           = 113;
Nat ascii_lower_r           = 114;
Nat ascii_lower_s           = 115;
Nat ascii_lower_t           = 116;
Nat ascii_lower_u           = 117;
Nat ascii_lower_v           = 118;
Nat ascii_lower_w           = 119;
Nat ascii_lower_x           = 120;
Nat ascii_lower_y           = 121;
Nat ascii_lower_z           = 122;
Nat ascii_left_brace        = 123;
Nat ascii_bar               = 124; // vertical bar, pipe
Nat ascii_right_brace       = 125;
Nat ascii_tilde             = 126;

///////////////////////////////////////////////////////////////////////////////

[[Nat]] split_lines([Nat] chs)
{
  return [rem_trail_cr(l) : l <- split(chs, ascii_newline)];

  [Nat] rem_trail_cr([Nat] line)
  {
    has_cr = line /= [] and rev_at(line, 0) == ascii_carriage_return;
    return if has_cr then subseq(line, 0, length(line)-1) else line end;
  }
}


[String] split(String str)
{
  len = length(str);
  frags = [];
  start = 0;
  for (ch @ i : _obj_(str))
    if (is_space(ch))
      frags = [frags | substr(str, start, i-start)] if start /= i;
      start = i + 1;
    ;
  ;
  frags = [frags | substr(str, start, len-start)] if start < len;
  return frags;
}
