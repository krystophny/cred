(* CLI entry point for ProbTT type checker *)

open Probtt_lib

let usage = "Usage: probtt <command> <file>\n\nCommands:\n  check <file>  Check a ProbTT/Agda file\n  infer <file>  Infer types in a ProbTT/Agda file\n"

let read_file path =
  try
    let ic = open_in path in
    let n = in_channel_length ic in
    let s = really_input_string ic n in
    close_in ic;
    Ok s
  with
  | Sys_error _ -> Error (Error.FileNotFound path)

(* Layout-aware lexer: inserts SEMI at start of lines at column 0 *)
let make_layout_lexer lexbuf =
  let pending_token = ref None in
  let last_line = ref 0 in
  let last_was_semi = ref false in
  fun () ->
    match !pending_token with
    | Some tok ->
        pending_token := None;
        last_was_semi := (tok = Parser.SEMI);
        tok
    | None ->
        let tok = Lexer.token lexbuf in
        (* Don't insert SEMI before EOF or if last token was SEMI *)
        if tok = Parser.EOF then tok
        else if tok = Parser.SEMI then begin
          last_was_semi := true;
          tok
        end else begin
          let pos = Lexing.lexeme_start_p lexbuf in
          let line = pos.Lexing.pos_lnum in
          let col = pos.Lexing.pos_cnum - pos.Lexing.pos_bol in
          (* Insert SEMI before tokens at column 0 on a new line, unless last was SEMI *)
          if line > !last_line && col = 0 && !last_line > 0 && not !last_was_semi then begin
            last_line := line;
            pending_token := Some tok;
            last_was_semi := false;
            Parser.SEMI
          end else begin
            last_line := line;
            last_was_semi := false;
            tok
          end
        end

let parse_string s =
  let lexbuf = Lexing.from_string s in
  let layout_token = make_layout_lexer lexbuf in
  try
    Ok (Parser.program (fun _ -> layout_token ()) lexbuf)
  with
  | Lexer.LexError msg -> Error (Error.ParseError msg)
  | Parser.Error ->
      let pos = lexbuf.Lexing.lex_curr_p in
      let msg = Printf.sprintf "Syntax error at line %d, column %d"
        pos.Lexing.pos_lnum
        (pos.Lexing.pos_cnum - pos.Lexing.pos_bol)
      in
      Error (Error.ParseError msg)

let check_decl _env (name, ty, term, weight) =
  if name = "" then Ok () else
  let open Format in
  printf "Checking %s : %a @ %a@." name Syntax.pp_ty ty Weight.pp weight;
  match Check.check Context.empty term ty with
  | Ok actual_weight ->
      let simplified = Weight.simplify actual_weight in
      if Weight.leq simplified weight then begin
        printf "  OK: %s has weight %a (declared %a)@.@."
          name Weight.pp simplified Weight.pp weight;
        Ok ()
      end else begin
        printf "  ERROR: weight %a not <= declared %a@.@."
          Weight.pp simplified Weight.pp weight;
        Error (Error.WeightNotLeq (weight, simplified))
      end
  | Error e ->
      printf "  ERROR: %a@.@." Error.pp e;
      Error e

let infer_decl _env (name, ty, term, _weight) =
  if name = "" then Ok () else
  let open Format in
  printf "Inferring %s@." name;
  match Check.infer Context.empty term with
  | Ok (inferred_ty, inferred_weight) ->
      printf "  %s : %a @ %a@.@."
        name Syntax.pp_ty inferred_ty Weight.pp (Weight.simplify inferred_weight);
      Ok ()
  | Error _ ->
      printf "  Checking against declared type: %a@." Syntax.pp_ty ty;
      match Check.check Context.empty term ty with
      | Ok w ->
          printf "  %s : %a @ %a@.@."
            name Syntax.pp_ty ty Weight.pp (Weight.simplify w);
          Ok ()
      | Error e' ->
          printf "  ERROR: %a@.@." Error.pp e';
          Error e'

let run_check path =
  let open Format in
  printf "ProbTT Type Checker (Agda-compatible syntax)@.";
  printf "Checking file: %s@.@." path;
  match read_file path with
  | Error e ->
      printf "ERROR: %a@." Error.pp e;
      exit 1
  | Ok content ->
      match parse_string content with
      | Error e ->
          printf "ERROR: %a@." Error.pp e;
          exit 1
      | Ok raw_decls ->
          let decls = Elaborate.elab_program raw_decls in
          let results = List.map (check_decl []) decls in
          let errors = List.filter Result.is_error results in
          if errors = [] then begin
            printf "All declarations checked successfully.@.";
            exit 0
          end else begin
            printf "%d error(s) found.@." (List.length errors);
            exit 1
          end

let run_infer path =
  let open Format in
  printf "ProbTT Type Checker (Agda-compatible syntax)@.";
  printf "Inferring types in: %s@.@." path;
  match read_file path with
  | Error e ->
      printf "ERROR: %a@." Error.pp e;
      exit 1
  | Ok content ->
      match parse_string content with
      | Error e ->
          printf "ERROR: %a@." Error.pp e;
          exit 1
      | Ok raw_decls ->
          let decls = Elaborate.elab_program raw_decls in
          let results = List.map (infer_decl []) decls in
          let errors = List.filter Result.is_error results in
          if errors = [] then begin
            printf "All declarations processed.@.";
            exit 0
          end else begin
            printf "%d error(s) found.@." (List.length errors);
            exit 1
          end

let () =
  match Array.to_list Sys.argv with
  | [_; "check"; path] -> run_check path
  | [_; "infer"; path] -> run_infer path
  | _ ->
      print_string usage;
      exit 1
