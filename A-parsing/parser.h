ParsingRule par_rule(ParsingRule rule)      = block_rule(parenthesis, rule);
ParsingRule bracket_rule(ParsingRule rule)  = block_rule(bracket, rule);
ParsingRule brace_rule(ParsingRule rule)    = block_rule(brace, rule);

ParsingRule empty_block_rule(ParType pt) = block_rule(pt, empty_rule);

ParsingRule comma_sep_seq(ParsingRule rule) = comma_sep_seq(rule, true);
ParsingRule opt_comma_sep_seq(ParsingRule rule) = comma_sep_seq(rule, false);
ParsingRule comma_sep_seq(ParsingRule rule, Bool nonempty) = rep_rule(rule, atomic_rule(comma), nonempty, false);
ParsingRule comma_sep_seq(ParsingRule rule, Nat min_count) = rep_rule(rule, min_count, atomic_rule(comma), false);

////////////////////////////////////////////////////////////////////////////////

type ParserError  = unexpected_end_of_file(ParsingRule),
                    unexpected_token(found: AnnotatedToken, expected: TokenMatchingRule?),
                    all_choices_failed(best_match: Atom, error: ParserError),
                    neg_rule_match(rule: ParsingRule, match: ParserMatch, offset: Nat);

type ParserMatch  = parser_match(rule_match: RuleMatch, nodes_consumed: Nat, failure: ParserError?);

type ParserResult = Result[ParserMatch, ParserError];

////////////////////////////////////////////////////////////////////////////////

ParserError unexpected_end_of_file(ParsingRule r)                     = :unexpected_end_of_file(r);
ParserError unexpected_token(AnnotatedToken t)                        = unexpected_token(found: t);
ParserError unexpected_token(AnnotatedToken t, TokenMatchingRule r)   = unexpected_token(found: t, expected: r);
ParserError all_choices_failed(Atom n, ParserError e)                 = all_choices_failed(best_match: n, error: e);
ParserError neg_rule_match(ParsingRule r, ParserMatch m, Nat o)       = neg_rule_match(rule: r, match: m, offset: o);

ParserMatch parser_match(RuleMatch rm, Nat nsc) = parser_match(rule_match: rm, nodes_consumed: nsc);
ParserMatch parser_match(RuleMatch rm, Nat nsc, ParserError pe) = parser_match(rule_match: rm, nodes_consumed: nsc, failure: pe);

////////////////////////////////////////////////////////////////////////////////

Int index_of_last_matched_token(ParserError error, PreAst pre_ast):
  //## BUG: THE -1 VALUE IS TOTALLY FAKE. I'M NOT SURE HOW TO FIX THIS.
  //## THIS IS ACTUALLY AN INTERESTING PROBLEM: THE LOSS OF INFORMATION
  //## MAKES IT IMPOSSIBLE TO DETERMINE THE CORRECT VALUE. HOW TO FIX THIS?
  unexpected_end_of_file()  = if pre_ast == [] then -1 else last_token(pre_ast).index end,
  unexpected_token()        = error.found.index - 1,
  all_choices_failed()      = index_of_last_matched_token(error.error, pre_ast),
  neg_rule_match()          = error.offset - 1; //## BUG: THIS IS WRONG TOO, AS THE INDEX THAT IS CONTAINED HERE IS RELATIVE THAT PARTICULAR NODE

////////////////////////////////////////////////////////////////////////////////

AnnotatedToken first_token(AnnotatedToken t)  = t;
AnnotatedToken first_token(PreAst a)          = first_token(a[0]);

AnnotatedToken last_token(AnnotatedToken t)   = t;
AnnotatedToken last_token(PreAst a)           = last_token(last(a));

////////////////////////////////////////////////////////////////////////////////

Bool matches(TokenMatchingRule rule, PlainToken token):
  AmberSymb,          AmberSymb           = rule == token,
  lowercase_id,       lowercase_id()      = true,
  mixedcase_id,       mixedcase_id()      = true,
  uppercase_id,       uppercase_id()      = true,
  qualified_symbol,   qualified_symbol()  = true,
  label,              label()             = true,
  integer,            Int                 = true,
  string,             String              = true,
  char,               Char                = true,
  operator,           operator()          = true,
  builtin,            builtin()           = true,
  qual_var,           qual_var()          = true,
  keyword(kw?),       lowercase_id(a?)    = kw == a,
  _,                  _                   = false;


ParserResult parse_all(ParsingRule rule, PreAst pre_ast, (Atom => ParsingRule) rec_rules)
{
  res = parse(rule, pre_ast, 0, rec_rules);
  return res if is_failure(res);
  mtc = get_result(res);
  nodes_consumed = mtc.nodes_consumed;
  assert nodes_consumed <= length(pre_ast);
  return res if nodes_consumed == length(pre_ast);
  if (mtc.failure?)
    err = mtc.failure;
  else
    err = unexpected_token(first_token(pre_ast[nodes_consumed]));
  ;
  return failure(err);
}


ParserResult parse(ParsingRule rule, PreAst pre_ast, Nat offset, (Atom => ParsingRule) rec_rules):
  empty_rule        = success(parser_match(null_match, 0)),

  atomic_rule(r?)   = {
    return failure(unexpected_end_of_file(rule)) if not is_valid_idx(pre_ast, offset);
    node = pre_ast[offset];
    return failure(unexpected_token(node[0], r)) if not node :: AnnotatedToken;
    return failure(unexpected_token(node, r)) if not matches(r, node.token);
    return success(parser_match(atomic_rule_match(node), 1));
  },

  optional_rule(r?) = {
    res = parse(r, pre_ast, offset, rec_rules);
    return if is_success(res) then res else success(parser_match(null_match, 0)) end;
  },

  rule_seq(rs?)     = {
    matches = [];
    maybe_prev_err = nil;
    delta = 0;
    for (r : rs)
      res = parse(r, pre_ast, offset+delta, rec_rules);
      if (is_failure(res))
        if (maybe_prev_err /= nil)
          err = get_error(res);
          prev_err = value(maybe_prev_err);
          err_idx = index_of_last_matched_token(err, pre_ast);
          prev_err_idx = index_of_last_matched_token(prev_err, pre_ast);
          return failure(prev_err) if prev_err_idx > err_idx;
        ;
        return res;
      ;
      res = get_result(res);
      matches = matches & [res.rule_match];
      maybe_prev_err = if res.failure? then just(res.failure) else nil end;
      delta = delta + res.nodes_consumed;
    ;
    return success(parser_match(rule_seq_match(matches), delta));
  },

  rep_rule()        = {
    matches = [];
    num_of_matches = 0;
    delta = 0;
    res = nil; //## BUG: THIS IS HERE ONLY BECAUSE THE COMPILER WOULD OTHERWISE COMPLAIN ABOUT THE VARIABLE res BEING UNDEFINED IN THE LAST LINE
    loop
      // Matching the separator, if this is not the first match
      sep_nodes = 0;
      if (matches /= [])
        res = parse(rule.separator, pre_ast, offset+delta, rec_rules);
        break if is_failure(res);
        res = get_result(res);
        matches = matches & [res.rule_match] if rule.save_sep;
        sep_nodes = res.nodes_consumed;
      ;
      // Matching the main rule
      res = parse(rule.rule, pre_ast, offset+delta+sep_nodes, rec_rules);
      break if is_failure(res);
      // if (is_failure(res))
      //   return res if num_of_matches < rule.min_count;
      //   break;
      // ;
      res = get_result(res);
      matches = matches & [res.rule_match];
      num_of_matches = num_of_matches + 1;
      delta = delta + sep_nodes + res.nodes_consumed;
    ;
    assert res /= nil;
    // assert num_of_matches >= rule.min_count;
    return res if num_of_matches < rule.min_count;
    return success(parser_match(rep_rule_match(matches), delta, get_error(res)));
  },

  rule_choice(cs?)  = {
    errs = [];
    for (c : cs)
      res = parse(c.rule, pre_ast, offset, rec_rules);
      if (is_success(res))
        res = get_result(res);
        mtc = if c.name? then rule_choice_match(c.name, res.rule_match) else res.rule_match end;
        return success(parser_match(mtc, res.nodes_consumed));
      else
        errs = errs & [get_error(res)];
      ;
    ;
    //## BAD: I WOULD NEED A max_by(xs, p) FUNCTION HERE
    idx = 0;
    for (e @ i : errs)
      idx = i if index_of_last_matched_token(e, pre_ast) > index_of_last_matched_token(errs[idx], pre_ast);
    ;
    //## BAD: LOSES ERROR INFORMATION HERE
    res_err = if cs[idx].name? then all_choices_failed(cs[idx].name, errs[idx]) else errs[idx] end;
    return failure(res_err);
  },

  rule_neg(r?)      = {
    res = parse(r, pre_ast, offset, rec_rules);
    if (is_failure(res))
      return success(parser_match(null_match, 0));
    else
      return failure(neg_rule_match(r, get_result(res), offset)); //## BUG: THE OFFSET HERE IS TOTALLY BOGUS, AS IT IS RELATIVE TO THE PRE-AST NODE THAT WE ARE VISITING NOW
    ;
  },

  block_rule()      = {
    par_token = left(rule.par_type);
    return failure(unexpected_end_of_file(atomic_rule(par_token))) if not is_valid_idx(pre_ast, offset);
    node = pre_ast[offset];
    return failure(unexpected_token(node, par_token)) if node :: AnnotatedToken;
    open_par = node[0];
    return failure(unexpected_token(open_par, par_token)) if open_par.token /= par_token;
    inner_pre_ast = subseq(node, 1, nil, 1);
    res = parse_all(rule.rule, inner_pre_ast, rec_rules);
    if (is_failure(res))
      return match (get_error(res))
        // unexpected_end_of_file(r?)  = failure(unexpected_token(last(node), r)),
        unexpected_end_of_file(r?)  = failure(unexpected_token(last(node))),
        _                           = res;
      ;
    ;
    return success(parser_match(get_result(res).rule_match, 1));
  },

  rule_ref(rn?)           = parse(rec_rules[rn], pre_ast, offset, rec_rules);
