
type_any_cheat_body = [ret_val(true)];

type_seq_cheat_body = [ret_val(or(is_empty_seq(fn_par(0)), is_ne_seq(fn_par(0))))];

type_set_cheat_body = [ret_val(or(is_empty_set(fn_par(0)), is_ne_set(fn_par(0))))];



ProcDef apply_cheats(ProcDef pd)
{
  if (pd.name == :memb_test(:type_symbol(:seq)))
    // print "Seq type cheat applied";
    return bool_proc_def(pd.name, pd.arity, type_seq_cheat_body);
  ;

  if (pd.name == :memb_test(:type_symbol(:set)))
    // print "Set type cheat applied";
    return bool_proc_def(pd.name, pd.arity, type_set_cheat_body);
  ;

  if (pd.name == :memb_test(:type_symbol(:any)))
    // print "Any type cheat applied";
    return bool_proc_def(pd.name, pd.arity, type_any_cheat_body);
  ;

  return pd;
}


Maybe[CCodeOutput] Compile((String => [Nat]) src_files, Bool print_intermediate, Bool print_times)
{
  t0 = _ticks_(nil);

  decls = [];
  for (fn : rand_sort(keys(src_files)))
    res = lex_and_parse_src_file(src_files[fn]);
    if (is_success(res))
      decls = decls & get_result(res);
    else
      print fn;
      print get_error(res);
      return nil;
    ;
  ;
  syn_prg = :prg(decls);

  t1 = _ticks_(nil);

  Print("Source files parsed\n");

  if (print_intermediate)
    FileWrite("dump_syn_prg.txt", false, _obj_(to_text(syn_prg, 100, 1)));
  ;

  errs = wf_errors(syn_prg);

  t2 = _ticks_(nil);

  if (errs == {})
    Print("Program is well-formed\n");
  else
    print errs;
    return nil;
  ;

  prg = rem_syntax(syn_prg);
  t3 = _ticks_(nil);
  Print("Syntax removed\n");

  if (print_intermediate)
    FileWrite("dump_prg.txt", false, _obj_(to_text(prg, 100, 1)));
  ;

  code = gen_prg_code(prg);
  t4 = _ticks_(nil);
  Print("Code generated\n");

  if (print_intermediate)
    FileWrite("dump_code.txt", false, _obj_(to_text(code, 100, 1)));
  ;

  code = {apply_cheats(d) : d <- code};

  c_code  = compile_to_c(code);
  t5 = _ticks_(nil);
  Print("C code generated\n");

  if (print_times)
    Print("\n");
    Print("Parsing:             " & to_str(t1-t0) & "ms\n");
    Print("Error checking:      " & to_str(t2-t1) & "ms\n");
    Print("Syntax removal:      " & to_str(t3-t2) & "ms\n");
    Print("Code generation:     " & to_str(t4-t3) & "ms\n");
    Print("C code generation:   " & to_str(t5-t4) & "ms\n");
    Print("Total time elapsed:  " & to_str(t5-t0) & "ms\n");
  ;

  return just(c_code);
}


[Nat] remove_comments([Nat] line)
{
  len = length(line);
  i = 0;
  while (i < len-1)
    return subseq(line, 0, i) if line[i] == ascii_slash and line[i+1] == ascii_slash;
    i = i + 1;
  ;
  return line;
}


[Nat] trim_spaces([Nat] line)
{
  len = length(line);
  skip_front = 0;
  while (skip_front < len and is_space(line[skip_front]))
    skip_front = skip_front + 1;
  ;
  return [] if skip_front == len;
  skip_back = 0;
  while (skip_back < len - skip_front and is_space(line[len-skip_back-1]))
    skip_back = skip_back + 1;
  ;
  assert skip_front + skip_back < len;
  return subseq(line, skip_front, nil, skip_back);
}


Main([String] args)
{
  argc = length(args);

  if (argc < 1)
    Print("Usage: amberc <project file>\n");
    return;
  ;

  fname = last(args);
  options = subseq(args, 0, argc-1);

  print_intermediate = false;
  print_times = false;
  wait_for_key = false;

  for (o : options)
    if (o == "-p")
      print_intermediate = true;
    elif (o == "-t")
      print_times = true;
    elif (o == "-w")
      wait_for_key = true;
    else
      Print("Unknown option: " & o & "\n");
      return;
    ;
  ;

  read_res = FileRead(fname);
  if (read_res == nil)
    Print("File not found: " & fname & "\n");
    return;
  ;
  prj_file = value(read_res);

  //## BAD. SHOULD BE: [s : l <- ls, s = ..., s /= ""]
  prj_file_lines = [string(trim_spaces(remove_comments(l))) : l <- split_lines(prj_file)];
  src_file_names = [l : l <- prj_file_lines, l /= ""];

  src_files = ();
  for (fn : src_file_names)
    fc = FileRead(fn);
    if (fc == nil)
      Print("Can't read file: " & fn & "\n");
      return;
    ;
    src_files = src_files & (fn => value(fc));
  ;

  output = Compile(src_files, print_intermediate, print_times);
  if (output /= nil)
    output = value(output);
    body = append(intermix(output.body, "\n"));
    header = append(intermix(output.header, "\n"));
    FileWrite("generated.cpp", false, _obj_(body));
    FileWrite("generated.h", false, _obj_(header));
  ;

  if (wait_for_key)
    GetChar();
  ;

  //## TODO: I SHOULD SET THE RETURN VALUE TO SOMETHING OTHER THAN 0 IF THE PROGRAM DOES NOT COMPILE
}
