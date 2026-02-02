(* CredTT Command-Line Interface

   Parses and checks .ctt files with credence tracking and stability analysis.

   Commands:
     credtt check <file>     Check a .ctt file for proof validity
     credtt infer <file>     Infer credences in a .ctt file
     credtt stability <file> Run stability analysis on a .ctt file
     credtt proof <name>     Run a built-in proof (sqrt2)
*)

open Credtt_lib

let usage = {|Usage: credtt <command> [file]

Commands:
  check <file>      Check a .ctt file for proof validity
  infer <file>      Infer credences in a .ctt file
  stability <file>  Run stability analysis on a .ctt file
  proof <name>      Run a built-in proof (sqrt2)

Options:
  --verbose, -v     Show detailed output
  --quiet, -q       Show only errors
  --help, -h        Show this help message

Examples:
  credtt check test/proofs/sqrt2.ptt
  credtt stability test/proofs/techniques/01_direct_proof.ctt
  credtt proof sqrt2
|}

type verbosity = Quiet | Normal | Verbose

let verbosity = ref Normal

let log level fmt =
  match level, !verbosity with
  | Verbose, Verbose -> Printf.ksprintf print_endline fmt
  | Normal, (Normal | Verbose) -> Printf.ksprintf print_endline fmt
  | Quiet, _ -> Printf.ksprintf print_endline fmt
  | _ -> Printf.ksprintf ignore fmt

let read_file path =
  try
    let ic = open_in path in
    let n = in_channel_length ic in
    let s = really_input_string ic n in
    close_in ic;
    Ok s
  with
  | Sys_error msg -> Error (Printf.sprintf "Cannot read file: %s" msg)

let make_layout_lexer lexbuf =
  let pending_token = ref None in
  let last_line = ref 0 in
  let last_was_semi = ref false in
  fun () ->
    match !pending_token with
    | Some tok ->
        pending_token := None;
        last_was_semi := (tok = Credtt_parser.Parser.SEMI);
        tok
    | None ->
        let tok = Credtt_parser.Lexer.token lexbuf in
        if tok = Credtt_parser.Parser.EOF then tok
        else if tok = Credtt_parser.Parser.SEMI then begin
          last_was_semi := true;
          tok
        end else begin
          let pos = Lexing.lexeme_start_p lexbuf in
          let line = pos.Lexing.pos_lnum in
          let col = pos.Lexing.pos_cnum - pos.Lexing.pos_bol in
          if line > !last_line && col = 0 && !last_line > 0 && not !last_was_semi then begin
            last_line := line;
            pending_token := Some tok;
            last_was_semi := false;
            Credtt_parser.Parser.SEMI
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
    Ok (Credtt_parser.Parser.program (fun _ -> layout_token ()) lexbuf)
  with
  | Credtt_parser.Lexer.LexError msg -> Error (Printf.sprintf "Lexer error: %s" msg)
  | Credtt_parser.Parser.Error ->
      let pos = lexbuf.Lexing.lex_curr_p in
      Error (Printf.sprintf "Parse error at line %d, column %d"
        pos.Lexing.pos_lnum
        (pos.Lexing.pos_cnum - pos.Lexing.pos_bol))

let check_decl _env (name, ty, term, credence) =
  if name = "" then Ok () else begin
  log Verbose "Checking %s : ... @ %s" name (Credence.to_string credence);
  match Check.check Context.empty term ty with
  | Ok actual_credence ->
      let simplified = Credence.simplify actual_credence in
      if Credence.leq credence simplified then begin
        log Verbose "  OK: %s has credence %s" name (Credence.to_string simplified);
        Ok ()
      end else begin
        log Quiet "  ERROR: declared credence %s not achievable from actual %s"
          (Credence.to_string credence) (Credence.to_string simplified);
        Error (Printf.sprintf "Credence mismatch for %s" name)
      end
  | Error e ->
      log Quiet "  ERROR: %s" (Error.to_string e);
      Error (Error.to_string e)
  end

let run_check path =
  log Normal "CredTT Type Checker";
  log Normal "Checking file: %s" path;
  log Normal "";
  match read_file path with
  | Error msg ->
      log Quiet "ERROR: %s" msg;
      1
  | Ok content ->
      match parse_string content with
      | Error msg ->
          log Quiet "ERROR: %s" msg;
          1
      | Ok raw_decls ->
          if Elaborate.has_proof_decls raw_decls then begin
            log Normal "Detected proof declarations, running proof checker...";
            log Normal "";
            let proof_decls = Elaborate.extract_proof_decls raw_decls in
            match Proof.check_proof proof_decls with
            | Ok _ ->
                log Normal "Proof checked successfully.";
                0
            | Error msg ->
                log Quiet "Proof check failed: %s" msg;
                1
          end else begin
            let decls = Elaborate.elab_program raw_decls in
            let results = List.map (check_decl []) decls in
            let errors = List.filter Result.is_error results in
            if errors = [] then begin
              log Normal "All declarations checked successfully.";
              0
            end else begin
              log Quiet "%d error(s) found." (List.length errors);
              1
            end
          end

let run_infer path =
  log Normal "CredTT Type Checker (inference mode)";
  log Normal "Inferring types in: %s" path;
  log Normal "";
  match read_file path with
  | Error msg ->
      log Quiet "ERROR: %s" msg;
      1
  | Ok content ->
      match parse_string content with
      | Error msg ->
          log Quiet "ERROR: %s" msg;
          1
      | Ok raw_decls ->
          let decls = Elaborate.elab_program raw_decls in
          let process (name, ty, term, _credence) =
            if name = "" then Ok () else begin
            log Normal "Inferring %s" name;
            match Check.infer Context.empty term with
            | Ok (_, inferred_credence) ->
                log Normal "  %s : ... @ %s" name
                  (Credence.to_string (Credence.simplify inferred_credence));
                Ok ()
            | Error _ ->
                match Check.check Context.empty term ty with
                | Ok c ->
                    log Normal "  %s : ... @ %s" name
                      (Credence.to_string (Credence.simplify c));
                    Ok ()
                | Error e ->
                    log Quiet "  ERROR: %s" (Error.to_string e);
                    Error (Error.to_string e)
            end
          in
          let results = List.map process decls in
          let errors = List.filter Result.is_error results in
          if errors = [] then begin
            log Normal "";
            log Normal "All declarations processed.";
            0
          end else begin
            log Quiet "%d error(s) found." (List.length errors);
            1
          end

let run_stability path =
  log Normal "CredTT Stability Analyzer";
  log Normal "Analyzing file: %s" path;
  log Normal "";
  match read_file path with
  | Error msg ->
      log Quiet "ERROR: %s" msg;
      1
  | Ok content ->
      match parse_string content with
      | Error msg ->
          log Quiet "ERROR: %s" msg;
          1
      | Ok raw_decls ->
          if Elaborate.has_proof_decls raw_decls then begin
            log Normal "Analyzing proof declarations for stability...";
            log Normal "";
            let proof_decls = Elaborate.extract_proof_decls raw_decls in
            match Proof.check_proof proof_decls with
            | Ok state ->
                log Normal "";
                log Normal "=== Stability Analysis ===";
                log Normal "";
                Hashtbl.iter (fun name j ->
                  let stability_str = Neighbourhood.stability_to_string j.Proof.stability in
                  let credence_str = Credence.to_string j.Proof.credence in
                  log Normal "  %s: %s @ %s" name stability_str credence_str
                ) state.Proof.judgments;
                log Normal "";
                if Hashtbl.length state.Proof.fixpoints > 0 then begin
                  log Normal "=== Fixpoints ===";
                  Hashtbl.iter (fun name value ->
                    log Normal "  %s = %s" name (Credence.rat_to_string value)
                  ) state.Proof.fixpoints;
                  log Normal ""
                end;
                log Normal "Stability analysis complete.";
                0
            | Error msg ->
                log Quiet "Analysis failed: %s" msg;
                1
          end else begin
            log Quiet "No proof declarations found. Use 'check' for type-theoretic files.";
            1
          end

let run_proof name =
  match name with
  | "sqrt2" ->
      log Normal "Running sqrt2 irrationality proof...";
      (match Proof.run_sqrt2_proof () with
       | Ok _ -> 0
       | Error _ -> 1)
  | _ ->
      log Quiet "Unknown proof: %s" name;
      log Quiet "Available proofs: sqrt2";
      1

let parse_args () =
  let args = Array.to_list Sys.argv |> List.tl in
  let rec go = function
    | [] -> None
    | "--verbose" :: rest | "-v" :: rest ->
        verbosity := Verbose;
        go rest
    | "--quiet" :: rest | "-q" :: rest ->
        verbosity := Quiet;
        go rest
    | "--help" :: _ | "-h" :: _ ->
        print_string usage;
        exit 0
    | "check" :: path :: _ -> Some (`Check path)
    | "infer" :: path :: _ -> Some (`Infer path)
    | "stability" :: path :: _ -> Some (`Stability path)
    | "proof" :: name :: _ -> Some (`Proof name)
    | _ -> None
  in
  go args

let () =
  match parse_args () with
  | Some (`Check path) -> exit (run_check path)
  | Some (`Infer path) -> exit (run_infer path)
  | Some (`Stability path) -> exit (run_stability path)
  | Some (`Proof name) -> exit (run_proof name)
  | None ->
      print_string usage;
      exit 1
