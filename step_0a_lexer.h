
type TokenLineInfo  = token_line_info(token: PlainToken, offset: Nat, length: NzNat);

// type LexerError = lexer_error(line: NzNat, col: NzNat); //## BAD: ALREADY DEFINED IN THE PRELUDE

type LexerResult      = Result[[AnnotatedToken], LexerError];
type ParseLineResult  = Result[[TokenLineInfo], Nat];
type ParseTokenResult = Result[TokenLineInfo, Nat];

////////////////////////////////////////////////////////////////////////////////

TokenLineInfo token_line_info(PlainToken token, Nat offset, NzNat length) = token_line_info(token: token, offset: offset, length: length);

AnnotatedToken annotated_token(TokenLineInfo token_info, NzNat line, Nat idx) = annotated_token(token_info.token, line, token_info.offset+1, idx);

////////////////////////////////////////////////////////////////////////////////

Atom symb([Nat] bytes) = _symb_(string(bytes)); //## THIS DOESN'T BELONG HERE

////////////////////////////////////////////////////////////////////////////////

Bool is_lower([Nat] bytes, Int offset)           = is_lower(at(bytes, offset, 0));
Bool is_upper([Nat] bytes, Int offset)           = is_upper(at(bytes, offset, 0));
Bool is_digit([Nat] bytes, Int offset)           = is_digit(at(bytes, offset, 0));
Bool is_lower_or_digit([Nat] bytes, Int offset)  = is_lower_or_digit(at(bytes, offset, 0));
Bool is_char([Nat] bytes, Int offset, Nat ch)    = at(bytes, offset, nil) == ch;
Bool is_str([Nat] bytes, Int offset, String str) = subseq(bytes, offset, min(length(bytes)-offset, length(str))) == _obj_(str);

Bool is_alphanum([Nat] bytes, Int offset, <upper, lower, any> case)  = is_alpha(bytes, offset, case) or is_digit(bytes, offset);
Bool is_alpha([Nat] bytes, Int offset, <upper, lower, any> case)     = (case /= :lower and is_upper(bytes, offset)) or
                                                                        (case /= :upper and is_lower(bytes, offset));

//## THESE TWO FUNCTIONS DO NOT BELONG HERE
Bool is_alphanum(Nat ch, <upper, lower, any> case)  = is_alpha(ch, case) or is_digit(ch);
Bool is_alpha(Nat ch, <upper, lower, any> case)     = (case /= :lower and is_upper(ch)) or (case /= :upper and is_lower(ch));

////////////////////////////////////////////////////////////////////////////////

Bool looks_like_a_lowercase_id_or_label([Nat] bytes, Int offset)   = is_lower(bytes, offset) and not looks_like_an_operator_fn(bytes, offset); //## THE OPERATOR THING IS TEMPORARY, UNTIL WE CHANGE THE OPERATOR SYNTAX
Bool looks_like_an_operator_fn([Nat] bytes, Int offset)            = is_str(bytes, offset, "op_") and not is_alphanum(bytes, offset+3, :any);
Bool looks_like_a_mixed_or_upper_case_id([Nat] bytes, Int offset)  = is_upper(bytes, offset);
Bool looks_like_a_qualified_symbol([Nat] bytes, Int offset)        = is_char(bytes, offset, ascii_colon) and is_lower(bytes, offset+1);
Bool looks_like_an_integer([Nat] bytes, Int offset)                = is_digit(bytes, offset);
Bool looks_like_a_string([Nat] bytes, Int offset)                  = is_char(bytes, offset, ascii_double_quotes);
Bool looks_like_a_char([Nat] bytes, Int offset)                    = is_char(bytes, offset, ascii_single_quote);
Bool looks_like_a_builtin([Nat] bytes, Int offset)                 = is_char(bytes, offset, ascii_underscore) and is_lower(bytes, offset+1);

////////////////////////////////////////////////////////////////////////////////

LexerResult lex_src_file([Nat] chars)
{
  lines = [remove_line_comment(l) : l <- split_lines(chars)];
  tokens = [];
  for (l @ i : lines)
    res = split_line_into_tokens(l);
    if (is_success(res))
      start_idx = length(tokens);
      tokens = tokens & [annotated_token(ti, i+1, start_idx+j) : ti @ j <- get_result(res)];
    else
      return failure(lexer_error(i+1, get_error(res)));
    ;
  ;
  return success(tokens);

  [Nat] remove_line_comment([Nat] line) =
    match(left_search(line, 2 * [ascii_slash]))
      just(idx?)  = subseq(line, 0, idx),
      nil         = line;
    ;
}


ParseLineResult split_line_into_tokens([Nat] bytes)
{
  len = length(bytes);
  idx = 0;
  tokens = [];
  loop
    while (idx < len and is_space(bytes[idx]))
      idx = idx + 1;
    ;
    break if idx >= len;
    res = if looks_like_a_lowercase_id_or_label(bytes, idx)  then read_lowercase_id_or_label(bytes, idx),
              looks_like_an_operator_fn(bytes, idx)           then read_operator_fn(bytes, idx),
              looks_like_a_mixed_or_upper_case_id(bytes, idx) then read_mixed_or_upper_case_id(bytes, idx),
              looks_like_a_qualified_symbol(bytes, idx)       then read_qualified_symbol(bytes, idx),
              looks_like_an_integer(bytes, idx)               then read_integer(bytes, idx),
              looks_like_a_string(bytes, idx)                 then read_string(bytes, idx),
              //looks_like_a_char(bytes, idx)                   then read_char(bytes, idx),
              looks_like_a_builtin(bytes, idx)                then read_builtin(bytes, idx)
                                                              else read_symbolic_token(bytes, idx)
           end;
    return res if not is_success(res);
    info = get_result(res);
    tokens = tokens & [info];
    assert idx == info.offset;
    idx = idx + info.length;
  ;
  return success(tokens); //## SHOULD ALSO RETURN THE OFFSETS OF THE TOKENS
}

////////////////////////////////////////////////////////////////////////////////

ParseTokenResult read_lowercase_id_or_label([Nat] bytes, Int offset)
{
  len = identifier_length(bytes, offset, :lower);
  next_idx = offset + len;
  next_ch = at(bytes, next_idx, 0);
  return failure(next_idx) if is_upper(next_ch) or next_ch == ascii_underscore;
  id = symb(subseq(bytes, offset, len));
  res = read_symbolic_token(bytes, next_idx);
  if (is_success(res) and get_result(res).token == colon)
    info = token_line_info(label(id), offset, len+1);
  else
    info = token_line_info(lowercase_id(id), offset, len);
  ;
  return success(info);
}


ParseTokenResult read_operator_fn([Nat] bytes, Int offset)
{
  assert is_str(bytes, offset, "op_");
  map = string_to_operator;
  strs = keys(map);
  maybe_best_match = best_match(bytes, offset+3, strs);
  return failure(offset) if maybe_best_match == nil;
  str = value(maybe_best_match);
  //## WE SHOULD DO SOME CHECKING HERE, TO MAKE SURE WE DON'T GET A STRANGE SEQUENCE OF ADJACENT IDENTIFIERS
  //## OR MAYBE THERE'S JUST NO POINT, AS THE SYNTAX IS GOING TO CHANGE SOON FROM op_X TO (X)
  //## PROBABLY AT THAT POINT WE WON'T NEED THIS FUNCTION ANYMORE...
  return success(token_line_info(operator(map[str]), offset, length(str)+3));
}


ParseTokenResult read_mixed_or_upper_case_id([Nat] bytes, Int offset)
{
  mixed_case_res = read_mixedcase_id(bytes, offset);
  return mixed_case_res if is_success(mixed_case_res);
  uppercase_res = read_uppercase_id(bytes, offset);
  return uppercase_res if is_success(uppercase_res);
  return failure(max(get_error(mixed_case_res), get_error(uppercase_res)));
}

ParseTokenResult read_mixedcase_id([Nat] bytes, Int offset)
{
  assert is_upper(bytes, offset);
  len = alphanum_length(bytes, offset);
  return failure(offset+len) if is_char(bytes, offset+len, ascii_underscore);
  return failure(offset) if none([is_lower(bytes, offset+i) : i <- inc_seq(len)]);
  symbol = symb(to_lower_with_underscores(subseq(bytes, offset, len)));
  return success(token_line_info(mixedcase_id(symbol), offset, len));
}

ParseTokenResult read_uppercase_id([Nat] bytes, Int offset)
{
  assert is_upper(bytes, offset);
  len = identifier_length(bytes, offset, :upper);
  next_idx = offset + len;
  next_ch = at(bytes, next_idx, 0);
  return failure(next_idx) if is_lower(next_ch) or next_ch == ascii_underscore;
  symbol = symb([lower(ch) : ch <- subseq(bytes, offset, len)]);
  return success(token_line_info(uppercase_id(symbol), offset, len));
}

ParseTokenResult read_qualified_symbol([Nat] bytes, Int offset)
{
  assert is_char(bytes, offset, ascii_colon);
  len = identifier_length(bytes, offset+1, :lower);
  next_idx = offset + 1 + len;
  next_ch = at(bytes, next_idx, 0);
  return failure(next_idx) if is_upper(next_ch) or next_ch == ascii_underscore;
  symbol = symb(subseq(bytes, offset+1, len));
  return success(token_line_info(qualified_symbol(symbol), offset, len+1));
}


ParseTokenResult read_integer([Nat] bytes, Int offset)
{
  assert is_digit(bytes, offset);
  len = digit_length(bytes, offset);
  //## CHECK THAT THE INTEGER IS NOT TOO BIG
  next_idx = offset + len;
  return failure(next_idx) if is_alpha(bytes, next_idx, :any);
  value = to_int(string(subseq(bytes, offset, len)));
  return success(token_line_info(value, offset, len));
}


ParseTokenResult read_string([Nat] bytes, Int offset)
{
  assert is_char(bytes, offset, ascii_double_quotes);

  len = length(bytes);
  chs = [];
  i = 1;
  loop
    idx = offset + i;
    return failure(len) if idx >= len; //## WOULD BE GOOD TO ADD MORE INFORMATION ABOUT THE FAILURE HERE
    ch = bytes[idx];
    i = i + 1;
    return success(token_line_info(string(chs), offset, i)) if ch == ascii_double_quotes;
    if (ch == ascii_backslash)
      idx = offset + i;
      i = i + 1;
      return failure(len) if idx >= len; //## WOULD BE GOOD TO ADD MORE INFORMATION ABOUT THE FAILURE HERE
      ch = bytes[idx];
      if (ch == ascii_backslash or ch == ascii_double_quotes)
        chs = chs & [ch];
      elif (ch == ascii_lower_n)
        chs = chs & [ascii_newline];
      else
        return failure(offset+i); //## WOULD BE GOOD TO ADD MORE INFORMATION ABOUT THE FAILURE HERE
      ;
    else
      chs = chs & [ch];
    ;
  ;
}


ParseTokenResult read_char([Nat] bytes, Int offset)
{
  fail;
}


ParseTokenResult read_builtin([Nat] bytes, Int offset)
{
  assert is_char(bytes, offset, ascii_underscore);
  len = identifier_length(bytes, offset+1, :lower);
  next_idx = offset + 1 + len;
  return failure(next_idx) if not is_char(bytes, next_idx, ascii_underscore);
  symbol = symb(subseq(bytes, offset+1, len));
  return failure(offset) if not symbol :: BuiltIn; //## WOULD BE GOOD TO ADD MORE INFORMATION ABOUT THE FAILURE HERE
  return success(token_line_info(builtin(symbol), offset, len+2));
}


ParseTokenResult read_symbolic_token([Nat] bytes, Int offset)
{
  map = string_to_symbol;
  strs = keys(map);
  maybe_best_match = best_match(bytes, offset, strs);
  return failure(offset) if maybe_best_match == nil;
  best_match = value(maybe_best_match);
  return success(token_line_info(map[best_match], offset, length(best_match)));
}

////////////////////////////////////////////////////////////////////////////////

Int identifier_length([Nat] bytes, Int offset, <upper, lower> case)
{
  assert is_alpha(bytes, offset, case);
  return 0 if not is_alpha(bytes, offset, case);
  len = 1;
  loop
    idx = offset + len;
    ch = at(bytes, idx, 0);
    if (ch == ascii_underscore)
      return len if not is_alphanum(bytes, idx+1, case);
    elif (not is_alphanum(ch, case))
      return len;
    ;
    len = len + 1;
  ;
 }

Maybe[String] best_match([Nat] bytes, Int offset, String* strings)
{
  candidates = {s : s <- strings, is_str(bytes, offset, s)};
  return nil if candidates == {};
  //## THIS IS REALLY BAD
  max_len = max({length(s) : s <- candidates});
  return just(only_element({s : s <- candidates, length(s) == max_len}));
}

//## REENABLE THE COMMENTED OUT IMPLEMENTATION AS SOON AS POSSIBLE
// [Nat^] to_lower_with_underscores([Nat^] bytes) = join([[ascii_underscore if i > 0 and is_upper(b), lower(b)] : b @ i <- bytes]);
[Nat^] to_lower_with_underscores([Nat^] bytes) = join([if i > 0 and is_upper(b) then [ascii_underscore, lower(b)] else [lower(b)] end : b @ i <- bytes]);

//## THINK OF A BETTER WAY TO WRITE ALL THESE FUNCTIONS. THERE MUST BE ONE

Int alphanum_length([Nat] bytes, Int offset)
{
  len = 0;
  while (is_alphanum(bytes, offset+len, :any))
    len = len + 1;
  ;
  return len;
}

Int digit_length([Nat] bytes, Int offset)
{
  len = 0;
  while (is_digit(bytes, offset+len))
    len = len + 1;
  ;
  return len;
}

////////////////////////////////////////////////////////////////////////////////

(String => AmberSymb) string_to_symbol = (
  "("     =>  left_parenthesis,
  ")"     =>  right_parenthesis,
  "["     =>  left_bracket,
  "]"     =>  right_bracket,
  "{"     =>  left_brace,
  "}"     =>  right_brace,
  ","     =>  comma,
  ";"     =>  semicolon,

  "?"     =>  question_mark,
  "="     =>  equals,
  "|"     =>  pipe,
  ":"     =>  colon,
  "_"     =>  underscore,
  "^"     =>  circumflex,
  "."     =>  dot,
  "~"     =>  tilde,
  "@"     =>  at,
  "&"     =>  ampersand,
  "!"     =>  bang,
  "#"     =>  hash,
  "$"     =>  dollar,

  "<"     =>  lower,
  ">"     =>  greater,
  "+"     =>  plus,
  "-"     =>  minus,
  "*"     =>  asterisk,
  "/"     =>  slash,

  ".."    =>  double_dot,

  "=="    =>  double_equals,
  "/="    =>  not_equal,
  "<="    =>  lower_eq,
  ">="    =>  greater_eq,

  ":="    =>  assign,
  "::"    =>  double_colon,
  "->"    =>  right_arrow,
  "=>"    =>  double_right_arrow,
  "<-"    =>  left_arrow,
  //"<="    =>  double_left_arrow,
  "\\/"   =>  logical_or_operator,

  "..."   =>  triple_dot

  // "(+)"     =>  operator(:plus),
  // "(-)"     =>  operator(:minus),
  // "(*)"     =>  operator(:star),   //## RENAME
  // "(/)"     =>  operator(:slash),  //## RENAME
  // "(^)"     =>  operator(:exp),    //## RENAME
  // "(&)"     =>  operator(:amp),    //## RENAME
  // "(<)"     =>  operator(:lower),
  // "(>)"     =>  operator(:greater),
  // "(<=)"    =>  operator(:lower_eq),
  // "(>=)"    =>  operator(:greater_eq),
  // "([])"    =>  operator(:brackets)
);


(String => Operator) string_to_operator = (
  "+"     =>  :plus,
  "-"     =>  :minus,
  "*"     =>  :star,
  "/"     =>  :slash,
  "^"     =>  :exp,
  "&"     =>  :amp,
  "<"     =>  :lower,
  ">"     =>  :greater,
  "<="    =>  :lower_eq,
  ">="    =>  :greater_eq,
  "[]"    =>  :brackets
);
