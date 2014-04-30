type CCodeOutput = (body: [String*], header: [String*]);

CCodeOutput compile_to_c(ProcDef* prg)
{
  tss := retrieve ts from memb_test(ts) in prg end;

  btss := {ts : BasicTypeSymbol ts <- tss};
  ptss := {ts : ParTypeSymbol ts <- tss};

  btss := rand_sort(btss);
  ptss := rand_sort(ptss);

  bool_proc_defs := rand_sort({p : BoolProcDef p <- prg});
  obj_proc_defs  := rand_sort({p : ObjProcDef  p <- prg});

  symbs := select SymbObj in prg end & {obj_true, obj_false, :object(:string)};
  symbs := sort_set(symbs; is_strictly_ordered(s1, s2) = s1 < s2);

  symb_decls := ["const Obj " & to_c_expr(s; typesymb2name(ts) = typesymb2str(ts, ptss)) & " = " & to_str(16*(i+1)+1) & ";" : s, i <- symbs] & rep_seq(4, "");
  symb_decls := symb_decls & ["const int EMB_SYMB_COUNT = " & to_text(length(symbs)) & ";"] & rep_seq(4, "");

  c_code := symb_decls;
  
  if (symbs /= [])
    symb_strs  := ["  \"" & _str_(untag(s)) & "\"," : s <- symbs];
    c_code     := c_code & ["const char *map_symb_to_str[EMB_SYMB_COUNT] = {"] & symb_strs & ["};"] & rep_seq(4, "");
    symb_decls := symb_decls & ["extern const char *map_symb_to_str[EMB_SYMB_COUNT];"] & rep_seq(4, "");
  ;
  
  print "Symbol declarations generated";

  cls_defs := select ClsDef in prg end;
  loop
    new_cls_defs := select ClsDef in {cd.body : cd <- cls_defs} end;
    break if subset(new_cls_defs, cls_defs); //## WHY BREAK WHEN IT'S A SUBSET AND NOT WHEN IT'S EMPTY?
    cls_defs := cls_defs & new_cls_defs;
  ;

  all_named_pars := merge_values(set([p.named_params : p <- obj_proc_defs]));
  all_param_arity_pairs := rand_sort({(var: v, arity: a) : v => ars <- all_named_pars, a <- ars});

  env_decl := ["struct Env {"];
  
  for (na, i : all_param_arity_pairs)
    var   := na.var;
    arity := na.arity;
    
    name := _str_(untag(var));
    
    if (arity > 0)
      ls := [ "  Obj (*n" & to_str(arity) & "_" & name & ")(" & append(["Obj p" & to_str(j) & ", " : j <- inc_seq(na.arity)]) & "const Obj *C, Env &env);",
              "  const Obj *C" & to_str(arity) & "_" & name & ";"
            ];
    else
      ls := ["  Obj n_" & name & ";"];
    ;

    ls := [""] & ls if i > 0;
    env_decl := env_decl & ls;
  ;

  env_decl := env_decl & ["};"] & rep_seq(4, "");
  
  c_code := c_code & env_decl;
  
//  print "compile_to_c#1";
//  
//  //## BAD CONSTRUCTION OF TUPLE IS REPEATED IN TWO DIFFERENT PLACES
//  set_cls_sgns    := {(name: cls.name, arity: cls.arity) : cls <- cls_defs};
//  print "compile_to_c#2";
//  called_cls_sgns := retrieve (cls_var: c.cls_var, arity: length(c.params)) from call_cls() c in prg end;
//  print "compile_to_c#3";
//  cls_sgns        := set_cls_sgns & called_cls_sgns;
//
////                    call_cls(var: ObjVar, cls_var: Var, params: [ObjExpr*]), //## NEW
//
//  //## BAD BAD BAD EXPRESSION TOO MESSY
//  part_to_max_size := for (s <- cls_sgns) (s => {
//                        sizes := for (cls <- cls_defs)
//                                   if (cls.name == s.name, s.arity == cls.arity)
//                                     {length(cls.env)};
//                        return if sizes == {} then 0 else max(sizes) end;
//                      });

  ////## MOST OF THIS CODE IS DUPLICATED (LOOK FOR VARIABLE TMP)
  //for (sgn : rand_sort(cls_sgns))
  //  //print sgn;
  //  cls_var  := to_c_imp_var_name(sgn.name, sgn.arity; typesymb2name(ts) = typesymb2str(ts, ptss));
  //  //print "----------------------------";
  //  env_var  := to_c_env_var_name(sgn.name, sgn.arity; typesymb2name(ts) = typesymb2str(ts, ptss));

  //  par_list := append(intermix(["const Obj *"] & rep_seq(sgn.arity, "Obj"), ", "));
  //  max_size := part_to_max_size[sgn];

  //  cls_decl := ["Obj (*" & cls_var & ")(" & par_list & ");"];
  //  env_decl := [if max_size == 0 then "const Obj *" & env_var & ";" else "Obj " & env_var & "[" & to_str(max_size) & "];" end];
  //  
  //  c_code := c_code & cls_decl & env_decl & ["", ""];
  //;

  sorted_cls_defs := rand_sort(cls_defs);
  
  proc_code := compile_to_c(
                 obj_proc_defs,
                 bool_proc_defs,
                 sorted_cls_defs;
                 typesymb2name(ts) = typesymb2str(ts, ptss),
                 cls2id(cls)       = index_first(cls, sorted_cls_defs)
                 //obj2var(obj)    = {assert false; return to_str(_counter_(nil));};
               );

  body := ["#include \"lib.h\"\n\n", "", "namespace generated", "{"] & indent(c_code & proc_code.body) & ["}"];
  header := ["namespace generated", "{"] & indent(symb_decls & env_decl & proc_code.header) & ["}"];
  
  return (body: body, header: header);


  String typesymb2str(ts, par_types):
    type_symbol(a)      = _str_(a),
    par_type_symbol()   = typesymb2str(ts.symbol, par_types) & "__" & to_str(index_first(ts, par_types));
}


//## THIS SHOULD NOT GO HERE
type FnCallParam = ObjExpr, VecVar, BoolExpr, IntExpr, ItVar, StreamVar;


using String typesymb2name(TypeSymbol), Nat cls2id(ClsDef)
{
  CCodeOutput compile_to_c([ObjProcDef*] obj_proc_defs, [BoolProcDef*] bool_proc_defs, [ClsDef*] cls_defs)
  {
    type_checking_fn_decls := [gen_c_decl(pd) : pd <- bool_proc_defs] & rep_seq(4, "");
    print "Type checking function declarations generated";

    closure_decls := [gen_c_decl(d, i) : d, i <- cls_defs] & rep_seq(4, "");
    print "Closure declarations generated";

    fn_decls := [gen_c_decl(pd) : pd <- obj_proc_defs] & rep_seq(4, "");
    print "Function declarations generated";

    type_checking_fns := join([compile_to_c(d) & ["", ""] : d <- bool_proc_defs]) & rep_seq(4, "");
    print "Type checking functions generated";

    closures := join([compile_to_c(d, i) & ["", ""] : d, i <- cls_defs]) & rep_seq(4, "");
    print "Closures generated";

    functions := join([compile_to_c(d) & ["", ""] : d <- obj_proc_defs]);
    print "Functions generated";

    body := join([type_checking_fn_decls, closure_decls, fn_decls, type_checking_fns, closures, functions]);

    return (body: body, header: fn_decls);
  }


  //## ALL THE CODE HERE IS DUPLICATED FROM compile_to_c()
  String gen_c_decl(ProcDef pd)
  {
    par_list := append(intermix(rep_seq(arity(pd), "Obj") & extra_params(pd), ", "));

    return ret_type_str(pd) & to_c_fn_name(pd.name) & "(" & par_list & ");";
    
    Nat arity(ProcDef pd):
      ObjProcDef    = pd.in_arity,
      BoolProcDef   = pd.arity;
    
    String ret_type_str(ProcDef):
      ObjProcDef    = "Obj ",
      BoolProcDef   = "bool ";
    
    [String*] extra_params(ProcDef):
      ObjProcDef    = ["Env &"],
      BoolProcDef   = [];
  }

  String gen_c_decl(ClsDef cd, Nat id)
  {
    par_list := append(intermix(rep_seq(cd.arity, "Obj") & ["const Obj *", "Env &"], ", "));
    //return "Obj " & to_c_imp_var_name(cd.name, cd.arity) & "__" & to_str(id) & "(" & par_list & ");";
    return "Obj cls_" & to_str(id) & "(" & par_list & ");";
  }


  [String*] compile_to_c(ProcDef pd)
  {
    par_list  := ["Obj p" & to_str(n) : n <- inc_seq(arity(pd))] & extra_params(pd); //## BAD
    signature := ret_type_str(pd) & to_c_fn_name(pd.name) & "(" & append(intermix(par_list, ", ")) & ")";

    body := pd.body;

    vars_to_decl := vars_to_declare(body);
    
    vector_vars := {v : VecVar v <- vars_to_decl};
    scalar_vars := vars_to_decl - vector_vars;
    
    vec_var_ids  := {v.id : v <- vector_vars};
    new_vec_vars := for (id <- vec_var_ids) {
                      vvar(id, max({v.size : v <- vector_vars ; v.id == id}))
                    };

    vars_to_decl := scalar_vars & new_vec_vars;
    
    var_decls := [var_decl(v) : v <- rand_sort(vars_to_decl)];
    comp_body := compile_to_c(body, nil);

    return [signature, "{"] & indent(var_decls) & [""] & indent(comp_body) & ["}"];

    
    Nat arity(ProcDef pd):
      ObjProcDef    = pd.in_arity,
      BoolProcDef   = pd.arity;
    
    String ret_type_str(ProcDef):
      ObjProcDef    = "Obj ",
      BoolProcDef   = "bool ";

    [String*] extra_params(ProcDef):
      ObjProcDef    = ["Env &env"],
      BoolProcDef   = [];
  }

  //## DUPLICATED CODE
  [String*] compile_to_c(ClsDef cd, Nat id)
  {
    par_list  := ["Obj p" & to_str(n) : n <- inc_seq(cd.arity)] & ["const Obj C[]", "Env &env"] ; //## BAD
    signature := "Obj cls_" & to_str(id) & "(" & append(intermix(par_list, ", ")) & ")";
    //signature := "Obj " & to_c_imp_var_name(cd.name, cd.arity) & "__" & to_str(id) & "(" & append(intermix(par_list, ", ")) & ")";

    body := cd.body;
    vars_to_decl := vars_to_declare(body);
    
    var_decls := [var_decl(v) : v <- rand_sort(vars_to_decl)];
    comp_body := compile_to_c(body, nil);

    return [signature, "{"] & indent(var_decls) & [""] & indent(comp_body) & ["}"];
  }

  AnyVar* vars_to_declare([Instr*] instrs) //## BAD BAD BAD
  {
    //vs := {if x :: <mk_seq(Any+)> then x.elems else x end
    //       : x <- select <AnyVar, mk_seq(Any+), ClsDef> in instrs end
    //       ; not x :: <fn_par(Nat), cls_ext_par(Nat), evar(id: Nat, idx: Nat), ClsDef>
    //      };

//                    cls_ext_par(Nat), //## RENAME THIS
//                    lvar(Nat), //## THIS IS REDUNDANT, WE ALREADY HAVE unique_var(Nat)
//                    evar(id: Nat, idx: <Nat, IntVar>);
//
//var(Atom), fn_par(Nat), named_par(Atom), unique_var(Nat)

    vs := {x : x <- select <AnyVar, ClsDef> in instrs end ;
               not x :: <fn_par(Nat), named_par(Atom), cls_ext_par(Nat), evar(id: Nat, idx: <Nat, IntVar>), ClsDef>
          };
    
    //print rand_sort(vs);
    return vs;
  }

  String var_decl(AnyVar v):
    ObjVar    = "Obj "      & to_c_var_name(v) & ";",
    VecVar    = "Obj "      & to_c_var_name(v) & "[" & to_str(v.size) & "];",
    BoolVar   = "bool "     & to_c_var_name(v) & ";",
    IntVar    = "int "      & to_c_var_name(v) & ";",
    SetItVar  = "SetIter "  & to_c_var_name(v) & ";",
    SeqItVar  = "SeqIter "  & to_c_var_name(v) & ";",
    MapItVar  = "MapIter "  & to_c_var_name(v) & ";",
    StreamVar = "Stream "   & to_c_var_name(v) & ";";


  [String*] compile_to_c([Instr*] instrs, <Nat, nil> block_id) = join([compile_to_c(instr, block_id) : instr <- instrs]);

  [String*] compile_to_c(Instr instr, <Nat, nil> block_id):

    init_stream(v)        = mk_call("init", [v]),
    append()              = mk_call("append", [instr.stream, instr.obj]),

    mk_set_from_stream()  = mk_call(instr.var, "make_set", [instr.stream]),
    mk_set()              = mk_call(instr.var, "make_set", [instr.elems, instr.size]),

    mk_seq_from_stream()  = mk_call(instr.var, "make_seq", [instr.stream]),
    mk_seq()              = mk_call(instr.var, "make_seq", [instr.elems, instr.size]),

    mk_map_from_streams() = mk_call(instr.var, "make_map", [instr.key_stream, instr.value_stream]),
    mk_map()              = mk_call(instr.var, "make_map", [instr.keys, instr.values, instr.size]),

    mk_tagged_obj()       = mk_call(instr.var, "make_tagged_obj", [instr.tag, instr.obj]),

    mk_array()            = mk_call(instr.var, "make_array", [instr.size, instr.value]),
    get_seq_slice()       = mk_call(instr.var, "get_seq_slice", [instr.seq, instr.idx_first, instr.len]),
    join_seqs()           = mk_call(instr.var, "join_seqs", [instr.left, instr.right]),
    rev_seq()             = mk_call(instr.var, "rev_seq", [instr.seq]),
    get_at()              = mk_call(instr.var, "get_at", [instr.seq, instr.idx]),
    
    set_at()              = mk_call("set_at", [instr.var, instr.idx, instr.value]),

    lookup()              = mk_call(
                              instr.var,
                              "lookup",
                              [instr.map, instr.key] & //## BAD BAD
                              if instr.success_var? then [instr.success_var] else [] end
                            ),
    
    //## BAD BAD IT'S ALMOST THE SAME AS THE EXPRESSION ABOVE
    ext_lookup()          = mk_call(
                              instr.var,
                              "ext_lookup",
                              [instr.map, instr.key] & //## BAD BAD
                              if instr.success_var? then [instr.success_var] else [] end
                            ),
    
    merge_maps()          = mk_call(instr.var, "merge_maps", [instr.map1, instr.map2]),
    
    seq_to_set()          = mk_call(instr.var, "seq_to_set", [instr.seq]),
    seq_to_mset()         = mk_call(instr.var, "seq_to_mset", [instr.seq]),
    list_to_seq()         = mk_call(instr.var, "list_to_seq", [instr.list]),
    internal_sort()       = mk_call(instr.var, "internal_sort", [instr.set]),
    
    get_set_iter()        = mk_call("get_set_iter", [instr.var, instr.src]),
    get_seq_iter()        = mk_call("get_seq_iter", [instr.var, instr.src]),
    get_map_iter()        = mk_call("get_map_iter", [instr.var, instr.src]),
    
    move_forward(v)       = mk_call("move_forward", [v]),
    
    set_var()             = mk_assignment(instr.var, instr.value),
    set_bvar()            = mk_assignment(instr.var, instr.value), //## BAD
    set_ivar()            = mk_assignment(instr.var, instr.value), //## BAD

    :terminate            = ["fail();"],

    add_ref(v)            = mk_call("add_ref", [v]),
    release(v)            = mk_call("release", [v]),
    
    print_obj()           = mk_call("print", [instr.obj]),
    
    ret_val(e)            = ["return " & to_c_expr(e) & ";"],
    
    :no_op                = [],

    repeat(body)          = ["for ( ; ; )", "{"] & indent(compile_to_c(body, block_id)) & ["}"],

    :break_loop           = ["break;"],


    execute_block(body)   = { new_block_id := _counter_(nil);
                              body_code := compile_to_c(body, new_block_id);
                              label := ["block_" & to_str(new_block_id) & "_end:;"];
                              return body_code & label;
                            },

    :exit_block           = { assert block_id /= nil; //## BAD
                              return ["goto block_" & to_str(block_id) & "_end;"];
                            },

    call_proc()           = mk_fn_call(instr.var, to_c_fn_name(instr.name), instr.params),

    //call_cls()            = mk_cls_call(instr.var, instr.cls_var, instr.params), //## INLINE THE FUNCTION

    call_cls()            = mk_cls_call(instr.var, instr.cls_var, instr.params), //## INLINE THE FUNCTION

    branch() =
    {
      assert instr.when_true? or instr.when_false?;
      cond       := instr.cond;
      when_true  := []; //## BAD BAD BAD I SHOULD CHANGE THE SCOPE RULES
      when_false := [];
      if (instr.when_true?)
        when_true  := instr.when_true;
        when_false := instr.when_false if instr.when_false?;
      else
        cond      := neg(cond);
        when_true := instr.when_false;
      ;
      code := ["if (" & to_c_expr(cond) & ")", "{"]     &
              indent(compile_to_c(when_true, block_id)) &
              ["}"];
      if (when_false /= [])
        code := code & ["else", "{"] & indent(compile_to_c(when_false, block_id)) & ["}"];
      ;
      return code;
    },

    //## HUGE BUG HERE: IF THE CODE IN ONE OF THE CASE STATEMENTS CONTAINS A BREAK
    //## THAT AFFECTS A LOOP THAT CONTAINS THE SWITCH STATEMENT, THEN THE BREAK WILL
    //## MISTAKINGLY TERMINATE THE SWITCH, NOT THE LOOP
    symbol_switch() =
    {
      code := ["switch (" & to_c_expr(instr.val) & ")", "{"];
      for (c : rand_sort(instr.cases))
        case_code := ["case S_" & _str_(untag(s)) & ":" : s <- rand_sort(c.vals)] & //## BAD
                     indent(compile_to_c(c.instrs, block_id) & ["break;"]);
        code := code & indent(case_code);
      ;
      if (instr.else?)
        code := code & ["default:"] & indent(compile_to_c(instr.else, block_id));
      ;
      return code & ["}"];
    },


    // var_scope(var: <named_par(Atom)>, new_value: AtomicExpr, body: [Instr+]),     //## STILL NEW

    var_scope() =
    {
      scope_id := to_str(_counter_(nil));
      
      var := instr.var;
      val := instr.new_value;
      
      //var_str := _str_(untag(var));  //## BAD, DUPLICATED LOGIC
      val_str := to_c_expr(val);
      
      env_var := to_c_var_name(var); //"env.n_" & var_str;  //## BAD, DUPLICATED LOGIC
      bk_var  := "BK" & scope_id;
      
      code := [ "Obj " & bk_var & " = " & env_var & ";",
                env_var & " = " & val_str & ";",
                "add_ref(" & env_var & ");"
              ];

      code := code & compile_to_c(instr.body, block_id);
      
      code := code & [ "release(" & env_var & ");",
                       env_var & " = " & bk_var & ";"
                     ];
      
      return code;
    },

    //cls_scope(cls: ClsDef, body: [Instr+]);
    //cls_def(
    //  name:   FnSymbol,
    //  arity:  NzNat,
    //  env:    [Var*],
    //  body:   [Instr+]
    //);

    cls_scope() =
    {
      scope_id := to_str(_counter_(nil));
       
      var   := instr.var;
      arity := instr.cls.arity;
      env   := instr.env;
      env_size := length(env);
      
      var_str := _str_(untag(var)); //## BAD, DUPLICATED LOGIC
      arity_str := to_str(arity);
      env_size_str := to_str(env_size);
       
      fn_var := "env.n" & arity_str & "_" & var_str;  //## BAD, DUPLICATED LOGIC
      data_var := "env.C" & arity_str & "_" & var_str; //## BAD, DUPLICATED LOGIC
      fn_bk_var := "BF" & scope_id;
      data_bk_var := "BD" & scope_id;
      new_data_var := "ND" & scope_id;
      

      tmp := rep_seq(arity, "Obj") & ["const Obj *", "Env &"];
      tmp := intermix(tmp, ", ");
      tmp := append(tmp);

      code := [ "Obj (*" & fn_bk_var & ")(" & tmp & ") = " & fn_var & ";",
                "const Obj *BD" & scope_id & " = " & data_var & ";"
              ];

      code := code & ["Obj " & new_data_var & "[" & env_size_str & "];"] if env_size > 0;

      //## HERE I'M ADDING THE add_ref/release PAIRS IN THE WRONG LAYERS
      for (i : inc_seq(env_size))
        code := code & [ new_data_var & "[" & to_str(i) & "] = " & to_c_var_name(env[i]) & ";",
                         "add_ref(" & new_data_var & "[" & to_str(i) & "]);"
                       ];
      ;
      
      code := code & [ fn_var & " = cls_" & to_str(cls2id(instr.cls)) & ";",
                       data_var & " = " & if env_size > 0 then new_data_var else "0" end & ";"
                     ];
      
      code := code & compile_to_c(instr.body, block_id);

      code := code & [ fn_var & " = " & fn_bk_var & ";",
                       data_var & " = " & data_bk_var & ";"
                     ];

      for (i : inc_seq(env_size))
        code := code & ["release(" & new_data_var & "[" & to_str(i) & "]);"];
      ;
       
      return code;
    };

  ///////////////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////////////////////////////

  String mk_gen_call(String fn_name, [FnCallParam*] params, [String*] trailing_params) =
    fn_name & "(" & append(intermix([to_c_expr(p) : p <- params] & trailing_params, ", ")) & ");";
  
  String mk_gen_call(AnyVar var, String fn_name, [FnCallParam*] params, [String*] trailing_params) =
    to_c_var_name(var) & " = " & mk_gen_call(fn_name, params, trailing_params);
  
  [String*] mk_call(String fn_name, [FnCallParam*] params)             = [mk_gen_call(fn_name, params, [])];
  [String*] mk_call(AnyVar var, String fn_name, [FnCallParam*] params) = [mk_gen_call(var, fn_name, params, [])];
  
  //[String*] mk_fn_call(String fn_name, [FnCallParam*] params)             = [mk_gen_call(fn_name, params, ["env"])];
  [String*] mk_fn_call(AnyVar var, String fn_name, [FnCallParam*] params) = [mk_gen_call(var, fn_name, params, ["env"])];

  //## AnyVar IS WRONG HERE, SHOULD ONLY BE OBJ/BOOL/INT VARS
  [String*] mk_assignment(AnyVar var, AnyExpr value) = [to_c_var_name(var) & " = " & to_c_expr(value) & ";"];


  [String*] mk_cls_call(ObjVar var, Var cls_var, [ObjExpr*] params)
  {
    name         := to_str(length(params)) & "_" & _str_(untag(cls_var));
    return [mk_gen_call(var, "env.n" & name, params, ["env.C" & name, "env"])];
  }
}

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

using String typesymb2name(TypeSymbol)
{
  String to_c_expr(ObjExpr expr):
    object(Atom a)      = "S_" & _str_(a),
    object(Int n)       = "to_obj(" & to_str(n) & ")",
    :empty_set          = "empty_set",
    :empty_seq          = "empty_seq",
    :empty_map          = "empty_map",
    ObjVar              = to_c_var_name(expr),
    get_tag(e)          = "get_tag("        & to_c_expr(e)     & ")",
    get_inner_obj(e)    = "get_inner_obj("  & to_c_expr(e)     & ")",
    to_obj(e)           = "to_obj("         & to_c_expr(e)     & ")",
    to_str(e)           = "to_str("         & to_c_expr(e)     & ")",
    to_symb(e)          = "to_symb("        & to_c_expr(e)     & ")",
    get_curr_obj(v)     = "get_curr_obj("   & to_c_var_name(v) & ")",
    get_curr_key(v)     = "get_curr_key("   & to_c_var_name(v) & ")",
    get_curr_value(v)   = "get_curr_value(" & to_c_var_name(v) & ")";

  String to_c_expr(ObjExpr expr, Bool) = to_c_expr(expr);


  String to_c_expr(BoolExpr expr) = to_c_expr(expr, false);

  String to_c_expr(BoolExpr expr, Bool parentesised):
    :true                 = "true",
    :false                = "false",
    BoolVar               = to_c_var_name(expr),
    is_symb(e)            = "is_symb("    & to_c_expr(e) & ")",
    is_int(e)             = "is_int("     & to_c_expr(e) & ")",
    is_ne_set(e)          = "is_ne_set("  & to_c_expr(e) & ")",
    is_ne_seq(e)          = "is_ne_seq("  & to_c_expr(e) & ")",
    is_ne_map(e)          = "is_ne_map("  & to_c_expr(e) & ")",
    is_tagged_obj(e)      = "is_tag_obj(" & to_c_expr(e) & ")",
    
    is_eq_bool()          = to_nary_op(" == ", [expr.expr1, expr.expr2], parentesised), //## BAD
    is_eq_int()           = to_nary_op(" == ", [expr.expr1, expr.expr2], parentesised), //## BAD

    is_eq()               = "are_eq(" & to_c_expr(expr.expr1) & ", " & to_c_expr(expr.expr2) & ")",

    //## BUG BUG BUG HUGE BUG HERE, NOT CHECKING THAT THE OPERANDS ARE INTEGERS
    is_gt()               = to_nary_op(" > ",  [expr.expr1, expr.expr2], parentesised), //## BAD
    is_ge()               = to_nary_op(" >= ", [expr.expr1, expr.expr2], parentesised), //## BAD
    is_lt()               = to_nary_op(" < ",  [expr.expr1, expr.expr2], parentesised), //## BAD
    is_le()               = to_nary_op(" <= ", [expr.expr1, expr.expr2], parentesised), //## BAD

    is_out_of_range(v)    = "is_out_of_range(" & to_c_var_name(v) & ")",

    neg(e)                = { s := "!" & to_c_expr(e, true);
                              s := "(" & s & ")" if parentesised;
                              return s;
                            },
    
    and(es)               = to_nary_op(" & ",  es, parentesised),
    or(es)                = to_nary_op(" | ",  es, parentesised),
    and_then(es)          = to_nary_op(" && ", es, parentesised),
    or_else(es)           = to_nary_op(" || ", es, parentesised),
    
    eval_bool_fn()        = to_c_fn_name(expr.name) & "(" & to_nary_op(", ", expr.params, false) & ")";


  String to_c_expr(IntExpr expr) = to_c_expr(expr, false);

  String to_c_expr(IntExpr expr, Bool parentesised):
    Int             = to_str(expr),
    IntVar          = to_c_var_name(expr),
    get_int_val(e)  = "get_int_val("  & to_c_expr(e) & ")",
    get_set_size(e) = "get_set_size(" & to_c_expr(e) & ")",
    get_seq_len(e)  = "get_seq_len("  & to_c_expr(e) & ")",
    get_map_size(e) = "get_map_size(" & to_c_expr(e) & ")",
    minus(e)        = "-" & to_c_expr(e, true),
    add()           = to_nary_op(" + ", [expr.val1, expr.val2], parentesised),
    mult()          = to_nary_op(" * ", [expr.val1, expr.val2], parentesised),
    idiv()          = to_nary_op(" / ", [expr.val1, expr.val2], parentesised),
    :unique_int     = "unique_int()";


  String to_c_expr(<VecVar, ItVar, StreamVar> var) = to_c_var_name(var);
  
  
  String to_nary_op(String op, [AnyExpr+] exprs, Bool parentesised)
  {
    expr := append(intermix([to_c_expr(e, true) : e <- exprs], op));
    expr := "(" & expr & ")" if length(exprs) > 1 and parentesised;
    return expr;
  }

  String to_c_var_name(ObjVar v):
    var(Atom a)         = "v_"  & _str_(a),
    fn_par(Nat n)       = "p"   & to_str(n),
    named_par(Atom a)   = "env.n_"  & _str_(a),
    unique_var(Nat n)   = "u"   & to_str(n),
    cls_ext_par(Nat n)  = "C["  & to_str(n) & "]",
    lvar(Nat n)         = "l"   & to_str(n),
    evar()              = "V" & to_str(v.id) & "[" & to_c_expr(v.idx) & "]";

  //## USE AnyVar?
  String to_c_var_name(VecVar v)    = "V" & to_str(v.id);
  String to_c_var_name(BoolVar v)   = "b" & to_str(untag(v));
  String to_c_var_name(IntVar v)    = "i" & to_str(untag(v));
  String to_c_var_name(SetItVar v)  = "s" & to_str(untag(v));
  String to_c_var_name(SeqItVar v)  = "q" & to_str(untag(v));
  String to_c_var_name(MapItVar v)  = "m" & to_str(untag(v));
  String to_c_var_name(StreamVar v) = "t" & to_str(untag(v));

  ///////////////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////////////////////////////

  //String to_c_imp_var_name(FnSymbol fn_symb, Nat arity) = "imp_" & to_c_fn_name(fn_symb, arity);
  //String to_c_env_var_name(FnSymbol fn_symb, Nat arity) = "env_" & to_c_fn_name(fn_symb, arity);
  //String to_c_imp_var_name(FnSymbol fn_symb, Nat arity) = "imp_" & to_c_fn_name(fn_symb, arity);
  //String to_c_env_var_name(FnSymbol fn_symb, Nat arity) = "env_" & to_c_fn_name(fn_symb, arity);

  //String to_c_imp_bkp_var_name(FnSymbol fn_symb, Nat arity, Nat id) = "bkp_imp_" & to_c_fn_name(fn_symb, arity, id);
  //String to_c_env_bkp_var_name(FnSymbol fn_symb, Nat arity, Nat id) = "bkp_env_" & to_c_fn_name(fn_symb, arity, id);

  //String to_c_cls_name(FnSymbol fn_symb, Nat arity, Nat id) = "cls_" & to_c_fn_name(fn_symb, arity, id);

  String to_c_fn_name(FnSymbol fn_symb, Nat arity, Nat id) = to_c_fn_name(fn_symb, arity) & "__" & to_str(id);
  String to_c_fn_name(FnSymbol fn_symb, Nat arity)         = to_c_fn_name(fn_symb) & "__" & to_str(arity);

  //String to_c_fn_name(ObjFnName name) = to_c_fn_name(untag(name));
  String to_c_fn_name(FnSymbol fn_symb):
    fn_symbol(symb)     = capitalize(_str_(symb)),
    op_symbol(op)       = _str_(op),
    nested_fn_symbol()  = to_c_fn_name(fn_symb.outer) & "__" & to_c_fn_name(fn_symb.inner);

  String to_c_fn_name(BoolFnName): memb_test(ts) = "is_" & typesymb2name(ts);
}

///////////////////////////////////////////////////////////////////////////////

[String*] indent([String*] strs) = [indent_line(s) : s <- strs];

String indent_line(String str) = "  " & str;


String capitalize(String s)
{
  first := true;
  res := [];
  for (ch, i : untag(s))
    if (ch == 95)
      first := true;
    else
      ch  := ch - 32 if ch >= 97 and ch <= 122 and first;
      first := false;
    ;
    res := res & [ch];
  ;
  return string(res);
}