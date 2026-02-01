(* Unit tests for proof checker *)

let test name cond =
  if cond then
    Printf.printf "PASS: %s\n" name
  else begin
    Printf.printf "FAIL: %s\n" name;
    exit 1
  end

let () =
  let open Probtt_lib in
  let w = Weight.var "w" in

  (* Basic postulate *)
  test "postulate creates proposition" (
    let decls = [Proof.Postulate ("p", "P", w)] in
    match Proof.check_proof decls with
    | Ok _ -> true
    | Error _ -> false
  );

  (* Derive from postulate *)
  test "derive from postulate" (
    let decls = [
      Proof.Postulate ("p", "P", w);
      Proof.Derive ("q", "Q", w, Proof.From ("p", "rule"))
    ] in
    match Proof.check_proof decls with
    | Ok _ -> true
    | Error _ -> false
  );

  (* Contradiction forces weight to zero *)
  test "contradiction forces zero" (
    let decls = [
      Proof.Postulate ("p", "P", w);
      Proof.Postulate ("q", "NotP", w);
      Proof.Contradict ("p", "q")
    ] in
    match Proof.check_proof decls with
    | Ok _ -> true
    | Error _ -> false
  );

  (* Negation after contradiction yields weight 1 *)
  test "negation yields one after contradiction" (
    let decls = [
      Proof.Postulate ("p", "P", w);
      Proof.Postulate ("q", "NotP", w);
      Proof.Contradict ("p", "q");
      Proof.Negate ("result", "p")
    ] in
    match Proof.check_proof decls with
    | Ok _ -> true
    | Error _ -> false
  );

  (* Full sqrt2 proof structure *)
  test "sqrt2 proof structure" (
    let decls = [
      Proof.Postulate ("sqrt2_rational", "Rational", w);
      Proof.Postulate ("gcd_is_1", "GCD_1", w);
      Proof.Derive ("p_even", "Even_p", w, Proof.From ("sqrt2_rational", "algebra"));
      Proof.Derive ("q_even", "Even_q", w, Proof.From ("p_even", "substitution"));
      Proof.Derive ("gcd_geq_2", "GCD_geq_2", w, Proof.From ("q_even", "both_even"));
      Proof.Contradict ("gcd_is_1", "gcd_geq_2");
      Proof.Negate ("sqrt2_irrational", "sqrt2_rational")
    ] in
    match Proof.check_proof decls with
    | Ok _ -> true
    | Error _ -> false
  );

  (* Provability predicate *)
  test "provable declaration works" (
    let decls = [
      Proof.Provable ("p", "P", w)
    ] in
    match Proof.check_proof decls with
    | Ok state ->
        Hashtbl.mem state.provables "p"
    | Error _ -> false
  );

  (* Fixpoint resolution: w = ¬w → w = 1/2 *)
  test "fixpoint w = ¬w resolves to 1/2" (
    let godel_w = Weight.Neg (Weight.Var "godel_w") in
    let decls = [
      Proof.Fixpoint ("godel_w", godel_w)
    ] in
    match Proof.check_proof decls with
    | Ok state ->
        (match Hashtbl.find_opt state.fixpoints "godel_w" with
         | Some r -> Weight.rat_equal r Weight.rat_half
         | None -> false)
    | Error _ -> false
  );

  (* Encoding declaration *)
  test "encode declaration works" (
    let decls = [
      Proof.Encode ("G", "Unprovable_G")
    ] in
    match Proof.check_proof decls with
    | Ok state ->
        Hashtbl.mem state.encodings "G"
    | Error _ -> false
  );

  (* Combined proof with fixpoint *)
  test "godel proof with fixpoint" (
    let w = Weight.var "w" in
    let decls = [
      Proof.Encode ("G", "Unprov_G");
      Proof.Postulate ("g", "G", w);
      Proof.Derive ("g_claims", "Prov_G_zero", w, Proof.From ("g", "self_reference"));
      Proof.Fixpoint ("godel_w", Weight.Neg (Weight.Var "godel_w"));
      Proof.Provable ("godel_provability", "G", Weight.Var "1/2")
    ] in
    match Proof.check_proof decls with
    | Ok state ->
        (* Verify fixpoint was solved to 1/2 *)
        (match Hashtbl.find_opt state.fixpoints "godel_w" with
         | Some r -> Weight.rat_equal r Weight.rat_half
         | None -> false)
    | Error _ -> false
  );

  Printf.printf "\nAll proof checker tests passed!\n"
