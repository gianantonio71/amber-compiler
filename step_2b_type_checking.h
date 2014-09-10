
FnType signature(FnDef fn_def, (TypeName => AnonType) typedefs) = fn_type(
                                   params:       [user_type_to_anon_type(p.type; typedefs=typedefs) : p <- fn_def.params],
                                   named_params: (n => user_type_to_anon_type(t; typedefs=typedefs) : n => t <- fn_def.named_params),
                                   ret_type:     user_type_to_anon_type(fn_def.res_type; typedefs=typedefs)
                                 );


Bool typechecks(Program prg)
{
  typedefs := prg.anon_tdefs;
  signatures := merge_values({(fd.name => signature(fd, typedefs)) : fd <- prg.fndefs});
  for (fd : rand_sort(prg.fndefs))
// if (to_c_fn_name(fd.name) /= "To_Text__Match_Idxs")
//## NON TYPECHECKING: Parse_Obj__Parse_Seq, Parse_Obj__Parse_Set, Parse_Obj__Parse_Map_Or_Tuple, Tokenize
// if (not in(to_c_fn_name(fd.name), {"To_Text__Match_Idxs"}))
// if (to_c_fn_name(fd.name) == "Parse_Obj__Parse_Obj")
    // print "Now doing function " & to_c_fn_name(fd.name);
    // print fd.params;
    if (not typechecks(fd, typedefs, signatures))
      // print "ERROR ERROR ERROR ERROR ERROR";
      // print "Function " & to_c_fn_name(fd.name) & " does not typecheck";
      // print fd.params;
      return false;
    // else
    //   print "Function " & to_c_fn_name(fd.name) & " typechecks";
    ;
// ;
  ;
  return true;
}


Bool typechecks(FnDef fn_def, (TypeName => AnonType) typedefs, (FnSymbol => FnType*) signatures)
{
  if (at_least_one([not p.type? : p <- fn_def.params]))
    print "Parameter type non provided";
    return true;
  ;

  if (not fn_def.res_type?)
    print "Return type not provided";
    return true;
  ;

  let (typedefs=typedefs, signatures=signatures, var_aliases=set([{fn_par(i), p.var} : p, i <- fn_def.params, p.var?]), halt_on_failure_to_typecheck=false)
    scalar_vars := (p.var => user_type_to_anon_type(p.type) : p <- set(fn_def.params) ; p.var?, p.type :: UserType) &
                   (fn_par(i) => user_type_to_anon_type(fn_def.params[i].type) : i <- index_set(fn_def.params) ; fn_def.params[i].type :: UserType) &
                   (v => user_type_to_anon_type(t) : v => UserType t <- fn_def.named_params);
    assert scalar_vars :: (Var => AnonType);

    cls_vars := (p.var => user_type_to_anon_type(p.type) : p <- set(fn_def.params) ; p.var?, p.type :: UserClsType) &
                (v => user_type_to_anon_type(t) : v => UserClsType t <- fn_def.named_params);
    assert cls_vars :: (Var => ClsType);

    // return typechecks(fn_def.expr, user_type_to_anon_type(fn_def.res_type); environment=scalar_vars, closures=cls_vars);
    //## THIS IS A TEMPORARY HACK TO WORK AROUND AN UNIMPLEMENTED FEATURE IN THE CODE GENERATION CODE
    res := typechecks(fn_def.expr, user_type_to_anon_type(fn_def.res_type); environment=scalar_vars, closures=cls_vars);
  ;
  return res;
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

using (TypeName => AnonType) typedefs
{
  ClsType user_type_to_anon_type(UserClsType type) = cls_type([user_type_to_anon_type(t) : t <- type.in_types], user_type_to_anon_type(type.out_type));


  AnonType user_type_to_anon_type(UserType type): //## BAD: SHOULD BE USING A REPLACE EXPRESSION HERE...
    LeafType        = type,
    TypeVar         = type,
    type_ref(ts)    = dereference_type_symbol(ts),
    ne_seq_type()   = ne_seq_type(user_type_to_anon_type(type.elem_type)),
    ne_set_type()   = ne_set_type(user_type_to_anon_type(type.elem_type)),
    ne_map_type()   = ne_map_type(user_type_to_anon_type(type.key_type), user_type_to_anon_type(type.value_type)),
    tuple_type(fs)  = tuple_type((l => (type: user_type_to_anon_type(f.type), optional: f.optional) : l => f <- fs)),
    tag_obj_type()  = tag_obj_type(type.tag_type, user_type_to_anon_type(type.obj_type)),
    union_type(ts)  = union_type({user_type_to_anon_type(t) : t <- ts});


  AnonType dereference_type_symbol(TypeSymbol type_symbol)
  {
    generic_type := typedefs[type_symb_to_name(type_symbol)];
    actual_params := [user_type_to_anon_type(tp) : tp <- params(type_symbol)];
    return instantiate_generic_params(generic_type, actual_params);
  }

  //## BAD: IS THIS THE SAME AS replace_type_vars()?
  AnonType instantiate_generic_params(AnonType generic_type, [AnonType*] actual_params): //## BAD: SHOULD BE USING A REPLACE EXPRESSION HERE...
    LeafType          = generic_type,
    SelfPretype       = generic_type,
    type_var(n)       = actual_params[n],
    ne_seq_type()     = ne_seq_type(instantiate_generic_params(generic_type.elem_type, actual_params)),
    ne_set_type()     = ne_set_type(instantiate_generic_params(generic_type.elem_type, actual_params)),
    ne_map_type()     = ne_map_type(instantiate_generic_params(generic_type.key_type, actual_params), instantiate_generic_params(generic_type.value_type, actual_params)),
    tuple_type(fs)    = tuple_type((l => (type: instantiate_generic_params(f.type, actual_params), optional: f.optional) : l => f <- fs)),
    tag_obj_type()    = tag_obj_type(instantiate_generic_params(generic_type.tag_type, actual_params), instantiate_generic_params(generic_type.obj_type, actual_params)),
    union_type(ts)    = union_type({instantiate_generic_params(t, actual_params) : t <- ts}),
    self_rec_type(t)  = self_rec_type(instantiate_generic_params(t, actual_params)),
    mut_rec_type()    = mut_rec_type(index: generic_type.index, types: [instantiate_generic_params(t, actual_params) : t <- generic_type.types]);
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

using
{
  Bool                    halt_on_failure_to_typecheck, //## THIS IS A TEMPORARY HACK
  (TypeName => AnonType)  typedefs,
  (FnSymbol => FnType*)   signatures,   //## MAYBE HERE I SHOULD INCLUDE THE ARITY IN THE KEY.
  (Var => AnonType)       environment,
  (Var => ClsType)        closures,
  Var**                   var_aliases;

  //////////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////

  Bool contains_empty_seq(AnonType type) = type_contains_obj(type, []);
  Bool contains_empty_set(AnonType type) = type_contains_obj(type, {});
  Bool contains_empty_map(AnonType type) = type_contains_obj(type, ());

  Bool is_seq_type(AnonType type) = is_subset(type, type_seq); //## IS THIS RIGHT?

  Bool is_typechecking_bool_expr(Expr expr) = typechecks(expr, type_bool);
  Bool is_typechecking_int_expr(Expr expr)  = typechecks(expr, integer);
  Bool is_typechecking_seq_expr(Expr expr)  = typechecks(expr, type_seq);
  Bool is_typechecking_set_expr(Expr expr)  = typechecks(expr, type_set);
  Bool is_typechecking_map_expr(Expr expr)  = typechecks(expr, type_map);

  Bool typechecks(Expr expr, AnonType* exp_types) = (? t <- exp_types : typechecks(expr, t)); //## IS THIS AT ALL USED?

  Bool typechecks(CondExpr expr, AnonType exp_type) = typechecks(expr.expr, exp_type) and is_typechecking_bool_expr(expr.cond);

  //## THIS FUNCTION SHOULD BE NEXT TO ITS ONLY CALLER
  Bool typechecks((key: Expr, value: Expr, cond: Expr?) entry, AnonType exp_key_type, AnonType exp_value_type) =
    typechecks(entry.key, exp_key_type) and typechecks(entry.value, exp_value_type) and (not entry.cond? or is_typechecking_bool_expr(entry.cond));

  Bool typechecks(Expr expr) = typechecks(expr, type_any);


  //////////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////

  Bool typechecks(Expr expr, AnonType exp_type)
  {
    res := typechecks_impl(expr, exp_type);
if (not res and halt_on_failure_to_typecheck)
  print "=============================================================";
  print expr;
  print exp_type;
  // print expr_type(expr);
  print environment[:var(:res)];
  // fail;
;
    return res;
  }

  Bool typechecks_impl(Expr expr, AnonType exp_type):
    SymbObj               = is_subset(symb_type(expr), exp_type),
    object(Int n)         = is_subset(int_range(min: n, size: 1), exp_type),

    set_expr(ses)         = {
      return contains_empty_set(exp_type) if ses == {};
      elem_type := set_elem_type(exp_type);
      return false if elem_type == void_type;
      return not (? se <- ses : not typechecks(se, elem_type));
    },

    // seq_expr(head: [SubExpr*], tail: Expr?), //## I DON'T LIKE THIS MUCH
    seq_expr()            = {
      return contains_empty_seq(exp_type) if expr.head == [] and not expr.tail?;
      return false if expr.tail? and not is_typechecking_seq_expr(expr.tail);
      elem_type := seq_elem_type(exp_type);
      return false if elem_type == void_type;
      for (e : expr.head)
        return false if not typechecks(e, elem_type);
      ;
      //## NOT SURE ABOUT THIS ONE. WHAT IF:
      //##   1) THE EXPECTED TYPE DOES NOT CONTAIN THE EMPTY SEQUENCE
      //##   2) THE HEAD IS NON-EMPTY
      //##   3) THE TAIL IS THE EMPTY SEQUENCE?
      return not expr.tail? or typechecks(expr.tail, exp_type);
    },

    //## TRY TO REWRITE THIS IN PROLOG-LIKE PSEUDOCODE
    map_expr(ses) = {
      // If it's the empty map, we just check that the empty map is included in the expected type
      return contains_empty_map(exp_type) if ses == {};
      // Inclusion conditions, if they exist, must typecheck as booleans
      return false if (? se <- ses : se.cond? and not is_typechecking_bool_expr(se.cond));
      // The expected type could contain either a map or a tuple type (or none at all).
      // Here we check to see if there's a map type
      exp_key_type := map_key_type(exp_type);
      exp_value_type := map_value_type(exp_type);
      assert (exp_key_type == void_type) == (exp_value_type == void_type);
      if (exp_key_type /= void_type and exp_value_type /= void_type) // A DOUBLE CHECK SHOULD HELP THE TYPE CHECKER
        // If the expected type includes a map type, we go for that
        return not (? se <- ses : not typechecks(se.key, exp_key_type) or not typechecks(se.value, exp_value_type));
      ;
      // There wasn't a map type. Now we check to see if there is a tuple type
      exp_tuple_type := tuple_type(exp_type);
      // If there is no tuple type we are done, the expression does not typecheck
      return false if exp_tuple_type == void_type;
      fields := untag(exp_tuple_type);
      exp_labels := keys(fields);
      // Making sure that the resulting tuple will always have all the required fields
      return false if not subset({l : l => f <- fields ; not f.optional}, {se.key : se <- ses ; not se.cond?});
      // Checking that the keys are symbols, that they are among the expected labels
      // and that the corresponding types all typecheck to the respective types.
      //## IN THEORY WE SHOULD CHECK THAT ALL EXPRESSIONS EVALUATE TO A SYMBOL, BUT WOULD THAT BE ANY USEFUL?
      return not (? se <- ses : not (se.key :: SymbObj and in(se.key, exp_labels) and typechecks(se.value, fields[se.key].type)));
    },

    // tag_obj_expr(tag: Expr, obj: Expr),
    tag_obj_expr()        = {
      tag_types := tagged_obj_types(exp_type);
      //## BUG: WHAT HAPPENS IF THE TAG EXPRESSION HAS TWO POSSIBLE VALUES
      //## AND THERE ARE TWO EXPECTED TYPES?
      return (? t <- tag_types : typechecks(expr.tag, t.tag_type), typechecks(expr.obj, t.obj_type));
    },

    Var                   = is_subset(environment[expr], exp_type),

    fn_call()             = (? s <- signatures[expr.name] : matches_signature(s, expr.params, expr.named_params),
                                                            is_subset(fn_call_type(s, expr.params, expr.named_params), exp_type)),

    cls_call()            = typechecks(expr.params, closures[expr.name], exp_type),

    builtin_call()        = matches_signature(builtin_signature(expr.name), expr.params, ()) and is_subset(expr_type(expr), exp_type),

    and_expr()            = is_subset(type_bool, exp_type) and is_typechecking_bool_expr(expr.left) and is_typechecking_bool_expr(expr.right),
    or_expr()             = is_subset(type_bool, exp_type) and is_typechecking_bool_expr(expr.left) and is_typechecking_bool_expr(expr.right),
    not_expr(e)           = is_subset(type_bool, exp_type) and is_typechecking_bool_expr(e),

    //## HERE I COULD ALSO CHECK THAT THE TYPES OF THE TWO EXPRESSIONS ARE NOT DISJOINT
    eq()                  = is_subset(type_bool, exp_type) and typechecks(expr.left) and typechecks(expr.right),

    membership()          = is_subset(type_bool, exp_type) and typechecks(expr.obj),

    cast_expr()           = typechecks(expr.expr), //## TODO: CHECK THAT THE TWO TYPES ARE NOT DISJOINT?

    accessor()            = {
      return false if not typechecks(expr.expr);
      types := split_type(expr_type(expr.expr));
      for (t : rand_sort(types)) //## UGLY UGLY
        if (t :: TupleType[AnonType])
          tuple_type := t;
        elif (t :: TagObjType[AnonType] and t.obj_type :: TupleType[AnonType])
          tuple_type := t.obj_type;
        else
          return false;
        ;
        field_type := mandatory_tuple_field_type(tuple_type, expr.field);
        return false if field_type == void_type or not is_subset(field_type, exp_type);
      ;
      return true;
    },

    accessor_test()       = {
      return false if not is_subset(type_bool, exp_type);
      type := expr_type(expr);
      return if type :: TupleType[AnonType] then tuple_has_field(type, expr.field),
                type :: MapType[AnonType]   then is_subset(symb_type(expr.field), type.key_type)
                                            else false
            end;
    },

    if_expr()             = {
      return false if not is_typechecking_bool_expr(expr.cond);
      new_envs := refine_environment(expr.cond);
      return typechecks(expr.then, exp_type; environment=new_envs.if_true) and
             typechecks(expr.else, exp_type; environment=new_envs.if_false);
    },

    //## HERE I SHOULD ALSO CHECK THAT THE PATTERNS WILL EVENTUALLY COVER ALL THE POSSIBILITIES...
    match_expr()          = {
      return false if not all([typechecks(e) : e <- expr.exprs]);
      ts := [expr_type(e) : e <- expr.exprs];
      for (c : expr.cases)
        ps := c.ptrns;
        e  := c.expr;
        //## A ZIP FUNCTION WOULD BE NICE HERE (OR, EVEN BETTER, LIST COMPREHENSION AND FOR LOOP THAT CAN WORK ON MULTIPLE LISTS)
        assert length(ps) == length(ts);
        for (i : indexes(ts))
          return false if not may_match(ps[i], ts[i]);
        ;
        new_env := update_environment(expr.exprs, ps);
        return false if not typechecks(e, exp_type; environment=new_env);
      ;
      return true;
    },

    do_expr(ss)           = typecheck(ss, exp_type),

    ex_qual()             = {
      return false if not typechecks(expr.source);
      new_env := update(environment, generated_environment(expr.source));
      return not expr.sel_expr? or is_typechecking_bool_expr(expr.sel_expr; environment=new_env);
    },

    set_comp()            = {
      return false if not typechecks(expr.source);
      new_env := refine_environment(expr.source);
      return false if expr.sel_expr? and not is_typechecking_bool_expr(expr.sel_expr; environment=new_env);
      exp_elem_type := set_elem_type(exp_type);
      return false if exp_elem_type == void_type;
      return typechecks(expr.expr, exp_elem_type; environment=new_env);
    },

    map_comp()            = {
      return false if not typechecks(expr.source);
      new_env := refine_environment(expr.source);
      return false if expr.sel_expr? and not is_typechecking_bool_expr(expr.sel_expr; environment=new_env);
      exp_key_type := map_key_type(exp_type);
      exp_value_type := map_value_type(exp_type);
      return false if exp_key_type == void_type or exp_value_type == void_type;
      return typechecks(expr.key_expr, exp_key_type; environment=new_env) and
             typechecks(expr.value_expr, exp_value_type; environment=new_env);
    },

    seq_comp()            = {
      return false if not is_typechecking_seq_expr(expr.src_expr);
      src_type := expr_type(expr.src_expr);
      return false if not is_seq_type(src_type);
      elem_type := seq_elem_type(src_type);
      assert elem_type /= void_type;
      // new_env := update(environment, (expr.var => elem_type, expr.idx_var => high_ints(min: 0) if expr.idx_var?));
      new_env := update(environment, (expr.var => elem_type) & if expr.idx_var? then (expr.idx_var => high_ints(min: 0)) else () end); //## BAD: RESTORE THE VERSION
      exp_elem_type := seq_elem_type(exp_type);
      return false if exp_elem_type == void_type;
      return false if expr.sel_expr? and is_typechecking_bool_expr(expr.sel_expr; environment=new_env);
      return typechecks(expr.expr, exp_elem_type; environment=new_env);
    },

    select_expr()         = {
      return false if not typechecks(expr.src_expr);
      new_env := update(environment, generated_environment(expr.ptrn));
      return false if expr.cond? and not is_typechecking_bool_expr(expr; environment=new_env);
      exp_elem_type := set_elem_type(exp_type);
      return false if exp_elem_type == void_type;
      return typechecks(expr.expr, exp_elem_type; environment=new_env);
    },

    replace_expr()        = is_type_any(exp_type);


  Bool typechecks(ClsExpr expr, UserClsType exp_type)
  {
    assert length(expr.params) == length(exp_type.in_types);

    idxs := set(indexes(expr.params));
    ps := expr.params;
    ts := exp_type.in_types;
    env_override := (fn_par(i) => ts[i] : i <- idxs) & (p => ts[i] : i <- idxs, p = ps[i] ; p /= nil);
    new_env := update(environment, env_override);

    return typechecks(expr.expr, exp_type.out_type);
  }


  Bool typechecks([Expr*] params, ClsType signature, AnonType exp_type)
  {
    assert length(params) == length(signature.in_types);

    for (i : indexes(params))
      e := params[i];
      t := signature.in_types[i];
      return false if not typechecks(e, replace_type_vars_with_type_any(t));
    ;

    return is_subset(cls_call_type(signature, [expr_type(p) : p <- params]), exp_type);
  }


  Bool typechecks(Clause clause, Expr sel_expr)
  {
    return false if not typechecks(clause);
    new_env := update(environment, generated_environment(clause));
    return typechecks(sel_expr, type_bool);
  }


  Bool typechecks(Clause clause):
    in_clause()           = is_typechecking_set_expr(clause.src),
    not_in_clause()       = is_typechecking_set_expr(clause.src),
    map_in_clause()       = is_typechecking_map_expr(clause.src),
    map_not_in_clause()   = is_typechecking_map_expr(clause.src),
    and_clause()          = typechecks(clause.left) and typechecks(clause.right; environment=update(environment, generated_environment(clause.left))),
    or_clause()           = typechecks(clause.left) and typechecks(clause.right);


  // We assume that the clause typechecks
  //## WOULD BE A GOOD IDEA TO ASSERT IT
  (Var => AnonType) generated_environment(Clause clause):
    in_clause()           = generated_environment(clause.ptrn, set_elem_type(expr_type(clause.src))),
    not_in_clause()       = (),
    map_in_clause()       = generated_environment(clause.key_ptrn, map_key_type(expr_type(clause.src))) &
                            generated_environment(clause.value_ptrn, map_value_type(expr_type(clause.src))),
    map_not_in_clause()   = (),
    and_clause()          = {
      left_env := generated_environment(clause.left);
      return left_env & generated_environment(clause.right; environment=environment & left_env);
    },
    or_clause()           = merge_envs(generated_environment(clause.left), generated_environment(clause.right));


  Bool may_match(Pattern ptrn, AnonType type):
    :ptrn_any         = true,
    obj_ptrn(obj)     = type_contains_obj(type, obj),
    type_ptrn(pt)     = intersection_superset(user_type_to_anon_type(pt), type) /= {},
    ext_var_ptrn(v)   = intersection_superset(environment[v], type) /= {},
    var_ptrn()        = not ptrn.ptrn? or may_match(ptrn.ptrn, type), //## REMEMBER TO UPDATE THIS WHEN MAKING THE ptrn FIELD NON-OPTIONAL
    tag_ptrn()        = {
      // tag := ptrn.tag;
      // if (tag :: <obj_ptrn(SymbObj)>)
      //   obj_type := tagged_obj_obj_type(type, untag(tag));
      //   return obj_type /= void_type and may_match(ptrn.obj, obj_type);
      // else
      //   tag_obj_types := tagged_obj_types(type);
      //   return (? t <- tag_obj_types : may_match(ptrn.obj, t.obj_type));
      // ;

      ts := tagged_obj_types(type);
      if (ptrn.tag :: <obj_ptrn(SymbObj)>)
        return (? t <- ts : may_match(ptrn.tag, t.tag_type) and may_match(ptrn.obj, t.obj_type));
      else
        return (? t <- ts : may_match(ptrn.obj, t.obj_type));
      ;
    };


  // Here I just assume that the pattern can match objects of the specified type
  // If it cannot, the function is free to fail or return garbage.
  //## WOULD BE GOOD TO ADD AN ASSERTION THAT CHECKS THAT THE PATTERN CAN ACTUALLY MATCH THE TYPE
  (Var => AnonType) generated_environment(Pattern ptrn, AnonType type)
  {
    res := generated_environment_impl(ptrn, type);
// print "#####################";
// print ptrn;
// print res;
// print "####";
    return res;
  }

  (Var => AnonType) generated_environment_impl(Pattern ptrn, AnonType type):
    :ptrn_any       = (),
    obj_ptrn(obj)   = (),
    type_ptrn()     = (),
    ext_var_ptrn(v) = (),
    var_ptrn()      = (ptrn.name => pattern_type_intersection(ptrn.ptrn, type)),
    tag_ptrn()      = {
      if (type :: TagObjType[AnonType])
        if (ptrn.tag :: <obj_ptrn(SymbObj)>)
          return () if not may_match(ptrn.tag, type.tag_type);
          env := ();
        else
          env := (ptrn.tag.name => type.tag_type);
        ;
        return env & generated_environment(ptrn.obj, type.obj_type);
      else
        return merge({generated_environment(ptrn, t) : t <- tagged_obj_types(type)});
      ;
    };


  Bool typecheck([Statement*] stmts, AnonType exp_type)
  {
    res := typecheck_impl(stmts, exp_type);
// if (not res and halt_on_failure_to_typecheck)
//   print "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@";
//   print stmts;
// ;
    return res;
  }

  Bool typecheck_impl([Statement*] stmts, AnonType exp_type)
  {
    env := environment;
    for (s : stmts)
      return false if not typechecks(s, exp_type; environment=env);
      env := update_environment(s; environment=env);
    ;
    return true;
  }

  Bool typechecks(Statement stmt, AnonType exp_type)
  {
    res := typechecks_impl(stmt, exp_type);

if (not res and halt_on_failure_to_typecheck)
  print "******************************";
  print stmt;
  fail;
;
    return res;
  }

  Bool typechecks_impl(Statement stmt, AnonType exp_type):
    assignment_stmt()   = typechecks(stmt.value),
    return_stmt(e)      = typechecks(e, exp_type),
    if_stmt()           = {
      return false if not is_typechecking_bool_expr(stmt.cond);
      envs := refine_environment(stmt.cond);
      return typecheck(stmt.body, exp_type; environment=envs.if_true) and typecheck(stmt.else, exp_type; environment=envs.if_false);
    },
    loop_stmt(ss)       = {
      return false if not typecheck(ss, exp_type);
      env_1 := update_environment(ss);
      return false if not typecheck(ss, exp_type; environment=env_1);
      env_2 := update_environment(ss; environment=env_1);
      return env_1 == env_2;
    },
    foreach_stmt()      = {
      return false if not is_typechecking_seq_expr(stmt.values);
      elem_type := seq_elem_type(expr_type(stmt.values));
      return false if elem_type == void_type;
      // env_0 := update(environment, (stmt.var => elem_type, stmt.idx_var => type_nat if stmt.idx_var));
      env_0 := update(environment, (stmt.var => elem_type) & if stmt.idx_var? then (stmt.idx_var => type_nat) else () end); //## BAD: RESTORE THE ABOVE VERSION
      return false if not typecheck(stmt.body, exp_type; environment=env_0);
      env_1 := update_environment(stmt.body; environment=env_0);
      return false if not typecheck(stmt.body, exp_type; environment=env_1);
      env_2 := update_environment(stmt.body; environment=env_1);
      return env_1 == env_2;
    },
    // for_stmt(var: Var, start_val: Expr, end_val: Expr, body: [Statement+]),
    //## BUG: THIS IS ALL WRONG
    for_stmt()          = is_typechecking_int_expr(stmt.start_val) and
                          is_typechecking_int_expr(stmt.end_val)   and
                          typecheck(stmt.body, exp_type; environment=environment & (stmt.var => integer)),
    let_stmt()          = {
      return false if (? v => e <- stmt.asgnms : not typechecks(e));
      env_delta := (v => expr_type(e) : v => e <- stmt.asgnms);
      new_env := update(environment, env_delta);
      return typecheck(stmt.body, exp_type; environment=new_env); //## BUG BUG BUG
    },
    :break_stmt         = true,
    :fail_stmt          = true,
    assert_stmt(e)      = is_typechecking_bool_expr(e),
    print_stmt(e)       = typechecks(e);

////////////////////////////////////////////////////////////////////////////////

  AnonType expr_type(CondExpr expr) = expr_type(expr.expr); //## HERE I SHOULD REFINE THE ENVIRONMENT BEFORE CALCULATING THE TYPE. SEE ALSO THE TYPECHECKING PART


  // I assume that the expression typechecks
  AnonType expr_type(Expr expr):
    SymbObj               = symb_type(expr),
    object(Int n)         = int_range(min: n, size: 1),

    set_expr(ses)         = {
      return empty_set_type if ses == {};
      type := ne_set_type(union_superset({expr_type(se) : se <- ses}));
      type := union_type({type, empty_set_type}) if (? se <- ses : se :: CondExpr);
      return type;
    },

    seq_expr()            = {
      if (expr.head == [])
        return if expr.tail? then expr_type(expr.tail) else empty_seq_type end;
      ;
      elem_type := union_superset({expr_type(se) : se <- set(expr.head)});
      may_be_empty := not (? se <- set(expr.head) : not se :: CondExpr);
      if (expr.tail?)
        tail_type := expr_type(expr.tail);
        may_be_empty := may_be_empty and contains_empty_seq(tail_type);
        tail_elem_type := seq_elem_type(tail_type);
        assert tail_type == empty_seq_type or tail_elem_type /= void_type;
        elem_type := union_superset({elem_type, tail_elem_type}) if tail_elem_type /= void_type;
      ;
      return if may_be_empty then type_seq(elem_type) else ne_seq_type(elem_type) end;
    },

    map_expr(ses) = {
      return empty_map_type if ses == {};
      if (not (? se <- ses : not se.key :: SymbObj))
        return tuple_type((se.key => (type: expr_type(se.value), optional: se.cond?) : se <- ses));
      else
        key_type := union_superset({expr_type(se.key) : se <- ses});
        value_type := union_superset({expr_type(se.value) : se <- ses});
        may_be_empty := not (? se <- ses : not se.cond?);
        return map_type(key_type, value_type, may_be_empty);
      ;
    },

    tag_obj_expr()        = {
      tag_type := expr_type(expr.tag);
      obj_type := expr_type(expr.obj);
      return tag_obj_type(tag_type, obj_type);
    },

    Var                   = environment[expr],

    fn_call()             = only_element({fn_call_type(s, expr.params, expr.named_params) : s <- signatures[expr.name] ; matches_signature(s, expr.params, expr.named_params)}),

    cls_call()            = cls_call_type(closures[expr.name], [expr_type(p) : p <- expr.params]),

    builtin_call()        = match (expr.name)
                              :obj  = union_superset({t.obj_type : t <- tagged_obj_types(expr_type(expr.params[0]))}),
                              :tag  = { tag_types := {t.tag_type : t <- tagged_obj_types(expr_type(expr.params[0]))};
                                        assert tag_types == {atom_type} or tag_types :: <SymbType+>;
                                        return union_type(tag_types); //## SHOULD I USE union_superset HERE?
                                      },
                              _     = fn_call_type(builtin_signature(expr.name), expr.params, ());
                            ,

    and_expr()            = type_bool,
    or_expr()             = type_bool,
    not(e)                = type_bool,

    eq()                  = type_bool,

    membership()          = type_bool,

    //## WOULD IT MAKE SENSE TO RETURN THE INTERSECTION OF THE TWO TYPES? OR WOULD IT JUST CONFUSE THE TYPE CHECKER?
    cast_expr()           = user_type_to_anon_type(expr.type),

    accessor()            = {
      types := for (t <- split_type(expr_type(expr.expr))) {
                 match (t)
                   tuple_type()    = t,
                   tag_obj_type()  = match (t.obj_type) tuple_type() ot = ot;
                 ;
               };
      assert types :: <TupleType[AnonType]+>;
      field_types := {mandatory_tuple_field_type(t, expr.field) : t <- types};
      //## MAYBE union_superset() SHOULD ACCEPT ALSO SETS OF JUST ONE TYPE. WHAT ABOUT THE EMPTY SET?
      return if size(field_types) == 1 then only_element(field_types) else union_superset(field_types) end;
    },

    accessor_test()       = type_bool,

    if_expr()             = {
      new_envs := refine_environment(expr.cond);
      return union_superset(expr_type(expr.then; environment=new_envs.if_true), expr_type(expr.else; environment=new_envs.if_false));
    },

    match_expr()          = {
      ts := [expr_type(e) : e <- expr.exprs];
      res_types := {};
      for (c : expr.cases)
        ps := c.ptrns;
        e  := c.expr;
        //## A ZIP FUNCTION WOULD BE NICE HERE (OR, EVEN BETTER, LIST COMPREHENSION AND FOR LOOP THAT CAN WORK ON MULTIPLE LISTS)
        assert length(ps) == length(ts);
        new_env := update_environment(expr.exprs, ps);
        res_types := res_types & {expr_type(e; environment=new_env)};
      ;
      return union_superset(res_types);
    },

    do_expr(ss)           = return_type(ss),

    ex_qual()             = type_bool,

    set_comp()            = ne_set_type(expr_type(expr.expr; environment=refine_environment(expr.source))),

    map_comp()            = {
      new_env := refine_environment(expr.source);
      key_type := expr_type(expr.key_expr; environment=new_env);
      value_type := expr_type(expr.value_expr; environment=new_env);
      return ne_map_type(key_type, value_type);
    },

    seq_comp()            = {
      src_type := expr_type(expr.src_expr);
      assert is_subset(src_type, type_seq);
      elem_type := seq_elem_type(src_type);
      // new_env := update(environment, (expr.var => elem_type, expr.idx_var => high_ints(min: 0) if expr.idx_var?));
      new_env := update(environment, (expr.var => elem_type) & if expr.idx_var? then (expr.idx_var => high_ints(min: 0)) else () end); //## BAD: RESTORE THE ABOVE VERSION
      return ne_seq_type(expr_type(expr.expr; environment=new_env));
    },

    select_expr()         = { //## THIS COULD BE REFINED, BUT IT ISN'T GOING TO BE EASY...
      new_env := update(environment, generated_environment(expr.ptrn));
      return ne_set_type(expr_type(expr.expr; environment=new_env));
    },

    replace_expr()        = type_any;

////////////////////////////////////////////////////////////////////////////////

  ClosedType return_type([Statement+] stmts)
  {
    env := environment;
    ret_types := {};
    for (s : stmts)
      ret_type := return_type(s; environment=env);
      ret_types := ret_types & {ret_type};
      env := update_environment(s; environment=env);
    ;
    return union_superset(ret_types);
  }


  ClosedType return_type(Statement stmt): //## IS THIS AT ALL USED?
    assignment_stmt()   = void_type,
    return_stmt(e)      = expr_type(e),
    if_stmt() = {
      envs := refine_environment(stmt.cond);
      true_ret_type := return_type(stmt.body; environment=envs.if_true);
      false_ret_type := return_type(stmt.body; environment=envs.if_false);
      return union_superset(true_ret_type, false_ret_type);
    },
    loop_stmt(ss) = {
      env_0 := environment;
      env_1 := update_environment(ss; environment=env_0);
      ret_type_0 := return_type(ss; environment=env_0);
      ret_type_1 := return_type(ss; environment=env_1);
      return union_superset(ret_type_0, ret_type_1);
    },
    foreach_stmt() = {
      elem_type := seq_elem_type(expr_type(stmt.values));
      assert elem_type /= void_type;
      // env_0 := update(environment, (stmt.var => elem_type, stmt.idx_var => type_nat if stmt.idx_var?));
      env_0 := environment & (stmt.var => elem_type) & if stmt.idx_var? then (stmt.idx_var => type_nat) else () end; //## TODO: RESTORE ABOVE VERSION
      env_1 := update_environment(stmt.body; environment=env_0);
      ret_type_0 := return_type(stmt.body; environment=env_0);
      ret_type_1 := return_type(stmt.body; environment=env_1);
      return union_superset(ret_type_0, ret_type_1);
    },
    for_stmt() = {
      env_0 := environment & (stmt.var => integer);
      env_1 := update_environment(stmt.body; environment=env_0);
      ret_type_0 := return_type(stmt.body; environment=env_0);
      ret_type_1 := return_type(stmt.body; environment=env_1);
      return union_superset(ret_type_0, ret_type_1);
    },
    let_stmt() = {
      env_delta := (v => expr_type(e) : v => e <- stmt.asgnms);
      new_env := update(environment, env_delta);
      return return_type(stmt.body; environment=new_env);
    },
    :break_stmt         = void_type,
    :fail_stmt          = void_type,
    assert_stmt()       = void_type,
    print_stmt()        = void_type;


    (Var => AnonType) update_environment([Statement*] stmts)
    {
      env := environment;
      for (s : stmts)
        env := update_environment(s; environment=env);
      ;
      assert may_fall_through(stmts) or env == ();
      return env;
    }


    (Var => AnonType) merge_envs((Var => AnonType) env1, (Var => AnonType) env2)
    {
      ks := intersection(keys(env1), keys(env2));
      return (k => union_superset({env1[k], env2[k]}) : k <- ks);
    }


    // Returns the empty map when the statement cannot fall through
    (Var => AnonType) update_environment(Statement stmt):
      assignment_stmt()   = update(environment, (stmt.var => expr_type(stmt.value))),

      return_stmt(e)      = (),

      if_stmt() = {
        start_envs := refine_environment(stmt.cond);
        res_env_true := update_environment(stmt.body; environment=start_envs.if_true);
        res_env_false := update_environment(stmt.else; environment=start_envs.if_false);

        if (may_fall_through(stmt.body))
          if (may_fall_through(stmt.else))
            return merge_envs(res_env_true, res_env_false);
          else
            return res_env_true;
          ;
        else
          if (may_fall_through(stmt.else))
            return res_env_false;
          else
            return ();
          ;
        ;
      },

      loop_stmt(ss) = {
        //## IS THIS CHECK NECESSARY? IF IT RETURNS OR FAILS (IT CANNOT BREAK) THEN THE RESULT IS MEANINGLESS
        //## ON THE OTHER HAND, RETURNING THE EMPTY MAP MAY BE MORE EFFECTIVE IN DETECTING ERRORS IN
        //## THE COMPILER CODE THAN RETURNING RANDOM GARBAGE...
        return () if not may_fall_through(ss);
        env_0 := environment;
        env_1 := update_environment(ss; environment=env_0);
        return merge_envs(env_0, env_1);
      },

      foreach_stmt() = {
        elem_type := seq_elem_type(expr_type(stmt.values));
        assert elem_type /= void_type;
        loop_vars := {stmt.var, stmt.idx_var if stmt.idx_var?};
        assert disjoint(keys(environment), loop_vars);
        // env_0 := environment & (stmt.var => elem_type, stmt.idx_var => type_nat if stmt.idx_var?));
        env_0 := environment & (stmt.var => elem_type) & if stmt.idx_var? then (stmt.idx_var => type_nat) else () end; //## TODO: RESTORE ABOVE VERSION
        env_1 := update_environment(stmt.body; environment=env_0);
        return merge_envs(environment, remove_keys(env_1, loop_vars));
      },

      for_stmt() = {
        loop_var := stmt.var;
        env_0 := environment & (loop_var => integer);
        env_1 := update_environment(stmt.body; environment=env_0);
        return merge_envs(environment, remove_keys(env_1, {loop_var}));      },

      let_stmt() = {
        return () if not may_fall_through(stmt.body); //## SEE COMMENT FOR loop_stmt() ABOVE
        env_delta := (v => expr_type(e) : v => e <- stmt.asgnms);
        new_env := update(environment, env_delta);
        return update_environment(stmt.body; environment=new_env);
      },

      :break_stmt         = (),

      :fail_stmt          = (),

      //## THIS IS AN INTERESTING CASE: IF I DECIDE TO MAKE ASSERTIONS REMOVABLE ONLY
      //## WHEN THEY ARE NOT NECESSARY TO MAKE THE CODE STATICALLY TYPE CHECKABLE,
      //## HOW CAN I DO IT? I WOULD NEED TO SOMEHOW STORE THE FACT THAT THE ASSERTION
      //## IS REMOVABLE OR NOT DURING STATIC TYPE CHECKING...
      assert_stmt(e)      = environment, // refine_environment(e).if_true, //## SHOULD I RELY ON THIS? WHAT HAPPENS IF THE ASSERTIONS ARE REMOVED? MAYBE I NEED A NON-REMOVABLE ASSERTION TYPE

      print_stmt()        = environment;


////////////////////////////////////////////////////////////////////////////////

  (if_true: (Var => AnonType), if_false: (Var => AnonType)) refine_environment(Expr cond) = (if_true: environment, if_false: environment); //## IMPLEMENT FOR REAL

  (Var => AnonType) update_environment([Expr+] exprs, [Pattern+] ptrns)
  {
// print "*--*--*--*--*--*--*--*--*--*--*--*--*--*--*--*--*--*--*";
    assert length(exprs) == length(ptrns);
    new_env := environment;
// print ptrns[0];
    for (i : indexes(exprs)) //## WOULD BE GOOD TO USE A ZIP FUNCTION HERE...
      expr := exprs[i];
      ptrn := ptrns[i];
      type := expr_type(expr);
      if (expr :: Var)
        refined_type := pattern_type_intersection(ptrn, type);
        assert refined_type /= void_type;
        var_group := only_element_or_def_if_empty({as : as <- var_aliases ; in(expr, as)}, {expr});
        new_env := update(new_env, (v => refined_type : v <- var_group));
      ;
      new_env := new_env & generated_environment(ptrn, type);
// print new_env[:var(:res)];
    ;
    return new_env;
  }

  //## IS IT CHECKED THAT VARIABLES IN CLAUSES CANNOT OVERRIDE EXISTING VARIABLES?
  //## WHAT ABOUT SOMETHING LIKE THIS: x <- xs, x => y <- xys?
  (Var => AnonType) refine_environment(Clause cls) = environment & generated_environment(cls);

////////////////////////////////////////////////////////////////////////////////

  FnType builtin_signature(BuiltIn):
    :neg            = fn_type([integer],                                            integer),
    :add            = fn_type([integer, integer],                                   integer),
    :str            = fn_type([atom_type],                                          type_string),
    :symb           = fn_type([type_string],                                        atom_type),
    :at             = fn_type([type_seq(type_var(:t)), integer],                    type_var(:t)),
    :len            = fn_type([type_seq],                                           high_ints(0)),
    :slice          = fn_type([type_seq(type_var(:t)), integer, integer],           type_seq(type_var(:t))),
    :cat            = fn_type([type_seq(type_var(:t)), type_seq(type_var(:t))],     type_seq(type_var(:t))),
    :rev            = fn_type([type_seq(type_var(:t))],                             type_seq(type_var(:t))),
    :set            = fn_type([type_seq(type_var(:t))],                             type_set(type_var(:t))),
    :mset           = fn_type([type_seq(type_var(:t))],                             type_mset(type_var(:t))),
    :isort          = fn_type([type_set(type_var(:t))],                             type_seq(type_var(:t))),
    // :list_to_seq    = fn_type([type_list(type_var(:t))],                            type_seq(type_var(:t))),
    :list_to_seq    = fn_type([type_any],                                           type_seq), //## BAD: IMPLEMENT ABOVE VERSION
    :tag            = fn_type([type_tagged_obj],                                    atom_type), // The return type is too loose, and it is ignore in the code
    :obj            = fn_type([type_tagged_obj],                                    type_any),  // Ditto
    :rand_nat       = fn_type([type_nat],                                           type_nat),
    :rand_elem      = fn_type([type_set(type_var(:t))],                             type_var(:t)),
    :counter        = fn_type([type_any],                                           integer);


  //## THIS IS ALL A TEMPORARY HACK TO WORK AROUND AN UNFINISHED FEATURE IN CODE GENERATION
  Bool matches_signature(FnType signature, [ExtExpr*] params, (<named_par(Atom)> => ExtExpr) named_params) =
    matches_signature_impl(signature, params, named_params; halt_on_failure_to_typecheck=false);

  Bool matches_signature_impl(FnType signature, [ExtExpr*] params, (<named_par(Atom)> => ExtExpr) named_params)
  {
    // let (halt_on_failure_to_typecheck=false)
      return false if length(params) /= length(signature.params);
      for (i : indexes(params)) //## WOULD BE GOOD TO USE A ZIP FUNCTION HERE
        e := params[i];
        t := signature.params[i];
        return false if not typechecks(e, replace_type_vars_with_type_any(t));
      ;

      for (p : keys(signature.named_params)) //## WOULD BE GOOD TO USE A ZIP (BY KEY) FUNCION HERE
        formal_type := signature.named_params[p];
        if (formal_type :: AnonType)
          formal_type := replace_type_vars_with_type_any(formal_type);
          if (has_key(named_params, p))
            expr := named_params[p];
            assert expr :: Expr;
            return false if not typechecks(expr, formal_type);
          else
            actual_type := environment[p];
            assert actual_type :: AnonType;
            return false if not is_subset(actual_type, formal_type);
          ;
        else
          assert formal_type :: ClsType;
          if (has_key(named_params, p))
            cls_expr := named_params[p];
            assert cls_expr :: ClsExpr;
            return false if not typechecks(cls_expr, formal_type);
          else
            actual_type := closures[p];
            assert actual_type :: ClsType;
            return false if not is_subset(actual_type, formal_type);
          ;
        ;
      ;
    // ;
    return true;
  }


  AnonType fn_call_type(FnType signature, [ExtExpr*] params, (<named_par(Atom)> => ExtExpr) named_params) //## DO I NEED THE THIRD PARAMETER?
  {
    cs  := [subset_conds(expr_type(params[i]), signature.params[i]) : i <- indexes(params)];
    mcs := merge_value_sets(set(cs));
    type_var_insts := (v => union_superset(ts) : v => ts <- mcs);
    return replace_type_vars(signature.ret_type, type_var_insts);
  }
}
