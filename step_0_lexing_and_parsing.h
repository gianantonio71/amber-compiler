
Result[[PrgDecl], <LexerError, PreParseError, ParserError>] lex_and_parse_src_file([Nat] chars)
{
  lex_res := lex_src_file(chars);
  return lex_res if is_failure(lex_res);
  tokens := get_result(lex_res);

  return success([]) if tokens == [];

  rec_rules := (
    type:         rule_type,
    pretype:      rule_pretype,
    expr:         rule_expr,
    stmt:         rule_stmt,
    ptrn:         rule_switch_ptrn,
    fndef:        rule_std_fndef(false),
    fndef_proc:   rule_proc_fndef(false),
    fndef_switch: rule_switch_fndef
  );

  pre_parse_res := pre_parse_file(tokens);
  return pre_parse_res if is_failure(pre_parse_res);
  pre_ast := get_result(pre_parse_res);

  parser_res := parse_all(rule_amber_file, pre_ast, rec_rules);
  return parser_res if is_failure(parser_res);
  parser_match := get_result(parser_res);

  post_parser_res := [reshuffle_local_fndefs(d) : d <- build_amber_file_ast(parser_match.rule_match)];

  return success(post_parser_res);
}


PrgDecl reshuffle_local_fndefs(PrgDecl decl)
{
  //## HUGE BUG: IF THE DO EXPRESSION ONLY CONTAINS FUNCTION DEFINITIONS,
  //## THE PURGED EXPRESSIONS WILL BE EMPTY, AND THIS WILL CRASH THE PROGRAM.
  //## IT ALSO DOESN'T REACH DOWN TO THE DO EXPRESSIONS THAT ARE NOT AT THE TOP LEVEL

  //## ALSO, THINK ABOUT HOW TO WRITE THIS FUNCTIONS WITHOUT APPENDING TO ARRAYS
  //## AND WITHOUT JUMPING THROUGH HOOP WITH PATTERN MATCHING

  return match (decl)
    syn_fn_def()  = reshuffle(decl),
    using_block() = syn_using_block(decl.signatures, [reshuffle(fd) : fd <- decl.fn_defs]),
    _             = decl;
  ;

  SynFnDef reshuffle(SynFnDef fd) =
    match (fd.expr)
      do_expr(ss?)  = reshuffle(fd, ss),
      _             = fd;
    ;

  SynFnDef reshuffle(SynFnDef fd, [SynStmt^] stmts)
  {
    lfds := [];
    rem_stmts := [];
    for (s : stmts)
      if (is_fn_def(s))
        lfds := lfds & [_obj_(s)];
      else
        rem_stmts := rem_stmts & [s];
      ;
    ;
    return syn_fn_def(
      name:       fd.name,
      params:     fd.params,
      res_type:   fd.res_type if fd.res_type?,
      expr:       syn_do_expr(rem_stmts),
      local_fns:  lfds
    );
  }

  Bool is_fn_def(SynStmt):
    fn_def_stmt() = true,
    _             = false;
}

////////////////////////////////////////////////////////////////////////////////

type PreParseError = parenthesis_not_closed(AnnotatedToken),
                     parenthesis_not_opened(AnnotatedToken),
                     mismatched_parenthesis(left: AnnotatedToken, right: AnnotatedToken);

type PreParseResult = Result[PreAst, PreParseError];

////////////////////////////////////////////////////////////////////////////////

PreParseError parenthesis_not_closed(AnnotatedToken p)                    = :parenthesis_not_closed(p);
PreParseError parenthesis_not_opened(AnnotatedToken p)                    = :parenthesis_not_opened(p);
PreParseError mismatched_parenthesis(AnnotatedToken l, AnnotatedToken r)  = mismatched_parenthesis(left: l, right: r);

////////////////////////////////////////////////////////////////////////////////

PreParseResult pre_parse_file([AnnotatedToken] tokens)
{
  par_stack := nil;
  pre_ast_stack := push(nil, []);
  for (at : tokens)
    t := at.token;
    new_node := at;
    if (t == left_parenthesis or t == left_bracket or t == left_brace)
      par_stack := push(par_stack, at);
      pre_ast_stack := push(pre_ast_stack, []);
    elif (t == right_parenthesis or t == right_bracket or t == right_brace)
      return failure(parenthesis_not_opened(at)) if par_stack == nil;
      last_par := peek(par_stack);
      //## SHOULD FIND A WAY TO MAKE THIS SYNTACTLY PALATABLE
      return failure(mismatched_parenthesis(last_par, at)) if match (last_par.token, t) left(pt1?), right(pt2?) = pt1 /= pt2;;
      par_stack := pop(par_stack);
      new_node := peek(pre_ast_stack) & [at];
      pre_ast_stack := pop(pre_ast_stack);
    ;
    pre_ast_stack := replace_top(pre_ast_stack, peek(pre_ast_stack) & [new_node]);
  ;
  return parenthesis_not_closed(peek(par_stack)) if par_stack /= nil;
  assert pop(pre_ast_stack) == nil;
  return success(peek(pre_ast_stack));
}

////////////////////////////////////////////////////////////////////////////////
