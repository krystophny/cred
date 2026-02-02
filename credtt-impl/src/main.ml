(* CLI entry point for CredTT type checker *)

open Credtt_lib

let usage = "Usage: credtt <command> [file]\n\nCommands:\n  check <file>  Check a CredTT/Agda file\n  infer <file>  Infer types in a CredTT/Agda file\n  proof sqrt2   Run the sqrt2 irrationality proof\n"

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

let check_decl _env (name, ty, term, credence) =
  if name = "" then Ok () else
  let open Format in
  printf "Checking %s : %a @ %a@." name Syntax.pp_ty ty Credence.pp credence;
  match Check.check Context.empty term ty with
  | Ok actual_credence ->
      let simplified = Credence.simplify actual_credence in
      (* Weakening rule (t-weaken): if we have t : A @ actual, we can use it
         at any declared credence where declared <= actual.
         Higher actual credence can be weakened to lower declared credence. *)
      if Credence.leq credence simplified then begin
        printf "  OK: %s has credence %a (declared %a)@.@."
          name Credence.pp simplified Credence.pp credence;
        Ok ()
      end else begin
        printf "  ERROR: declared credence %a not achievable from actual %a@.@."
          Credence.pp credence Credence.pp simplified;
        Error (Error.CredenceNotLeq (credence, simplified))
      end
  | Error e ->
      printf "  ERROR: %a@.@." Error.pp e;
      Error e

let infer_decl _env (name, ty, term, _credence) =
  if name = "" then Ok () else
  let open Format in
  printf "Inferring %s@." name;
  match Check.infer Context.empty term with
  | Ok (inferred_ty, inferred_credence) ->
      printf "  %s : %a @ %a@.@."
        name Syntax.pp_ty inferred_ty Credence.pp (Credence.simplify inferred_credence);
      Ok ()
  | Error _ ->
      printf "  Checking against declared type: %a@." Syntax.pp_ty ty;
      match Check.check Context.empty term ty with
      | Ok c ->
          printf "  %s : %a @ %a@.@."
            name Syntax.pp_ty ty Credence.pp (Credence.simplify c);
          Ok ()
      | Error e' ->
          printf "  ERROR: %a@.@." Error.pp e';
          Error e'

let run_check path =
  let open Format in
  printf "CredTT Type Checker (Agda-compatible syntax)@.";
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
          (* Check if this is a proof file *)
          if Elaborate.has_proof_decls raw_decls then begin
            printf "Detected proof declarations, running proof checker...@.@.";
            let proof_decls = Elaborate.extract_proof_decls raw_decls in
            match Proof.check_proof proof_decls with
            | Ok _ -> exit 0
            | Error _ -> exit 1
          end else begin
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
          end

let run_infer path =
  let open Format in
  printf "CredTT Type Checker (Agda-compatible syntax)@.";
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

let run_proof name =
  match name with
  | "sqrt2" ->
      (match Proof.run_sqrt2_proof () with
       | Ok _ -> exit 0
       | Error _ -> exit 1)
  | _ ->
      Printf.printf "Unknown proof: %s\n" name;
      Printf.printf "Available proofs: sqrt2\n";
      exit 1

let () =
  match Array.to_list Sys.argv with
  | [_; "check"; path] -> run_check path
  | [_; "infer"; path] -> run_infer path
  | [_; "proof"; name] -> run_proof name
  | _ ->
      print_string usage;
      exit 1
