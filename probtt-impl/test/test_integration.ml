(* Integration tests: run CLI on .ptt files *)

let test name cond =
  if cond then
    Printf.printf "PASS: %s\n" name
  else begin
    Printf.printf "FAIL: %s\n" name;
    exit 1
  end

(* Find probtt-impl directory by looking for dune-project *)
let find_project_root () =
  let rec go dir =
    let candidate = Filename.concat dir "dune-project" in
    if Sys.file_exists candidate then dir
    else
      let parent = Filename.dirname dir in
      if parent = dir then failwith "Could not find project root"
      else go parent
  in
  go (Sys.getcwd ())

let project_root = find_project_root ()

let run_check path =
  let full_path = Filename.concat project_root path in
  (* Use the built executable directly *)
  let exe = Filename.concat project_root "_build/default/src/main.exe" in
  let cmd = Printf.sprintf "%s check %s 2>&1" exe full_path in
  let ic = Unix.open_process_in cmd in
  let buf = Buffer.create 256 in
  (try
    while true do
      Buffer.add_channel buf ic 1
    done
  with End_of_file -> ());
  let status = Unix.close_process_in ic in
  let output = Buffer.contents buf in
  (status, output)

let check_succeeds path =
  let (status, output) = run_check path in
  if status <> Unix.WEXITED 0 then
    Printf.eprintf "FAILED (expected success): %s\nOutput: %s\n" path output;
  status = Unix.WEXITED 0

let check_fails path =
  let (status, output) = run_check path in
  if status = Unix.WEXITED 0 then
    Printf.eprintf "FAILED (expected failure): %s\nOutput: %s\n" path output;
  status <> Unix.WEXITED 0

let check_contains path substr =
  let (_, output) = run_check path in
  try
    let _ = Str.search_forward (Str.regexp_string substr) output 0 in
    true
  with Not_found ->
    Printf.eprintf "MISSING '%s' in output:\n%s\n" substr output;
    false

let () =
  (* Example files should type check *)
  test "identity.ptt type checks" (check_succeeds "test/examples/identity.ptt");
  test "pair.ptt type checks" (check_succeeds "test/examples/pair.ptt");
  test "simple.ptt type checks" (check_succeeds "test/examples/simple.ptt");
  test "weights.ptt type checks" (check_succeeds "test/examples/weights.ptt");
  test "weakening.ptt type checks" (check_succeeds "test/examples/weakening.ptt");
  test "weight_mul.ptt type checks" (check_succeeds "test/examples/weight_mul.ptt");

  (* Proof files - sqrt2 *)
  test "sqrt2.ptt proof succeeds" (check_succeeds "test/proofs/sqrt2.ptt");
  test "sqrt2.ptt shows contradiction" (check_contains "test/proofs/sqrt2.ptt" "CONTRADICTION");
  test "sqrt2.ptt concludes weight 1" (check_contains "test/proofs/sqrt2.ptt" "1");

  (* Classical logic proofs *)
  test "modus_ponens.ptt succeeds" (check_succeeds "test/proofs/modus_ponens.ptt");
  test "modus_tollens.ptt succeeds" (check_succeeds "test/proofs/modus_tollens.ptt");
  test "modus_tollens.ptt shows contradiction" (check_contains "test/proofs/modus_tollens.ptt" "CONTRADICTION");
  test "contradiction.ptt succeeds" (check_succeeds "test/proofs/contradiction.ptt");
  test "double_negation.ptt succeeds" (check_succeeds "test/proofs/double_negation.ptt");
  test "double_negation.ptt forces w=0" (check_contains "test/proofs/double_negation.ptt" "w = 0");
  test "ex_falso.ptt succeeds" (check_succeeds "test/proofs/ex_falso.ptt");

  (* Invalid proofs - must be rejected *)
  test "invalid_unknown_ref.ptt fails" (check_fails "test/proofs/invalid_unknown_ref.ptt");
  test "invalid_contradict_unknown.ptt fails" (check_fails "test/proofs/invalid_contradict_unknown.ptt");
  test "invalid_conclude_unknown.ptt fails" (check_fails "test/proofs/invalid_conclude_unknown.ptt");

  (* Meta-theory proofs: Gödel, self-consistency, graded choice *)
  test "godel_fixpoint.ptt succeeds" (check_succeeds "test/proofs/godel_fixpoint.ptt");
  test "godel_fixpoint.ptt shows fixpoint" (check_contains "test/proofs/godel_fixpoint.ptt" "FIXPOINT");
  test "godel_fixpoint.ptt solves to 1/2" (check_contains "test/proofs/godel_fixpoint.ptt" "1/2");

  test "self_consistency.ptt succeeds" (check_succeeds "test/proofs/self_consistency.ptt");
  test "self_consistency.ptt has provable" (check_contains "test/proofs/self_consistency.ptt" "provable");

  test "graded_choice.ptt succeeds" (check_succeeds "test/proofs/graded_choice.ptt");
  test "graded_choice.ptt has finite choice" (check_contains "test/proofs/graded_choice.ptt" "Finite_Choice");

  (* Weight inference tests *)
  test "weight_infer.ptt succeeds" (check_succeeds "test/proofs/weight_infer.ptt");
  test "weight_infer.ptt preserves weight w" (check_contains "test/proofs/weight_infer.ptt" "w");

  test "infer_underscore.ptt succeeds" (check_succeeds "test/proofs/infer_underscore.ptt");
  test "infer_underscore.ptt shows inference variable" (check_contains "test/proofs/infer_underscore.ptt" "?0");

  test "infer_fixpoint.ptt succeeds" (check_succeeds "test/proofs/infer_fixpoint.ptt");
  test "infer_fixpoint.ptt solves to 1/2" (check_contains "test/proofs/infer_fixpoint.ptt" "1/2");

  Printf.printf "\nAll integration tests passed!\n"
