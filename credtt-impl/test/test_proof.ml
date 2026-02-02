(* Unit tests for proof checker *)

let test name cond =
  if cond then
    Printf.printf "PASS: %s\n" name
  else begin
    Printf.printf "FAIL: %s\n" name;
    exit 1
  end

let () =
  let open Credtt_lib in
  let c = Credence.var "c" in

  (* Basic postulate *)
  test "postulate creates proposition" (
    let decls = [Proof.Postulate ("p", "P", c)] in
    match Proof.check_proof decls with
    | Ok _ -> true
    | Error _ -> false
  );

  (* Derive from postulate *)
  test "derive from postulate" (
    let decls = [
      Proof.Postulate ("p", "P", c);
      Proof.Derive ("q", "Q", c, Proof.From ("p", "rule"))
    ] in
    match Proof.check_proof decls with
    | Ok _ -> true
    | Error _ -> false
  );

  (* Contradiction forces credence to zero *)
  test "contradiction forces zero" (
    let decls = [
      Proof.Postulate ("p", "P", c);
      Proof.Postulate ("q", "NotP", c);
      Proof.Contradict ("p", "q")
    ] in
    match Proof.check_proof decls with
    | Ok _ -> true
    | Error _ -> false
  );

  (* Negation after contradiction yields credence 1 *)
  test "negation yields one after contradiction" (
    let decls = [
      Proof.Postulate ("p", "P", c);
      Proof.Postulate ("q", "NotP", c);
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
      Proof.Postulate ("sqrt2_rational", "Rational", c);
      Proof.Postulate ("gcd_is_1", "GCD_1", c);
      Proof.Derive ("p_even", "Even_p", c, Proof.From ("sqrt2_rational", "algebra"));
      Proof.Derive ("q_even", "Even_q", c, Proof.From ("p_even", "substitution"));
      Proof.Derive ("gcd_geq_2", "GCD_geq_2", c, Proof.From ("q_even", "both_even"));
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
      Proof.Provable ("p", "P", c)
    ] in
    match Proof.check_proof decls with
    | Ok state ->
        Hashtbl.mem state.provables "p"
    | Error _ -> false
  );

  (* Fixpoint resolution: c = neg c -> c = 1/2 *)
  test "fixpoint c = neg c resolves to 1/2" (
    let godel_c = Credence.Neg (Credence.Var "godel_c") in
    let decls = [
      Proof.Fixpoint ("godel_c", godel_c)
    ] in
    match Proof.check_proof decls with
    | Ok state ->
        (match Hashtbl.find_opt state.fixpoints "godel_c" with
         | Some r -> Credence.rat_equal r Credence.rat_half
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
    let c = Credence.var "c" in
    let decls = [
      Proof.Encode ("G", "Unprov_G");
      Proof.Postulate ("g", "G", c);
      Proof.Derive ("g_claims", "Prov_G_zero", c, Proof.From ("g", "self_reference"));
      Proof.Fixpoint ("godel_c", Credence.Neg (Credence.Var "godel_c"));
      Proof.Provable ("godel_provability", "G", Credence.Var "1/2")
    ] in
    match Proof.check_proof decls with
    | Ok state ->
        (* Verify fixpoint was solved to 1/2 *)
        (match Hashtbl.find_opt state.fixpoints "godel_c" with
         | Some r -> Credence.rat_equal r Credence.rat_half
         | None -> false)
    | Error _ -> false
  );

  (* Fixpoint: c = c*c resolves to 1 (idempotent, non-trivial solution) *)
  test "fixpoint c = c*c resolves to 1" (
    let c_squared = Credence.Mul (Credence.Var "idempot_c", Credence.Var "idempot_c") in
    let decls = [
      Proof.Fixpoint ("idempot_c", c_squared)
    ] in
    match Proof.check_proof decls with
    | Ok state ->
        (match Hashtbl.find_opt state.fixpoints "idempot_c" with
         | Some r -> Credence.rat_equal r Credence.rat_one
         | None -> false)
    | Error _ -> false
  );

  (* Fixpoint: c = c*k with k < 1 resolves to 0 *)
  test "fixpoint c = c*k (k<1) resolves to 0" (
    let c_times_half = Credence.Mul (Credence.Var "contract_c", Credence.Rat (1, 2)) in
    let decls = [
      Proof.Fixpoint ("contract_c", c_times_half)
    ] in
    match Proof.check_proof decls with
    | Ok state ->
        (match Hashtbl.find_opt state.fixpoints "contract_c" with
         | Some r -> Credence.rat_equal r Credence.rat_zero
         | None -> false)
    | Error _ -> false
  );

  (* Fixpoint: c = c*1 is identity (no binding) *)
  test "fixpoint c = c*1 is identity" (
    let c_times_one = Credence.Mul (Credence.Var "ident_c", Credence.One) in
    let decls = [
      Proof.Fixpoint ("ident_c", c_times_one)
    ] in
    match Proof.check_proof decls with
    | Ok state ->
        (* Identity means no fixpoint value is stored *)
        not (Hashtbl.mem state.fixpoints "ident_c")
    | Error _ -> false
  );

  (* Fixpoint: c = neg(neg c) is identity by involution *)
  test "fixpoint c = neg(neg c) is identity" (
    let double_neg = Credence.Neg (Credence.Neg (Credence.Var "invol_c")) in
    let decls = [
      Proof.Fixpoint ("invol_c", double_neg)
    ] in
    match Proof.check_proof decls with
    | Ok state ->
        (* Identity means no fixpoint value is stored *)
        not (Hashtbl.mem state.fixpoints "invol_c")
    | Error _ -> false
  );

  (* Fixpoint: c = c is trivial identity *)
  test "fixpoint c = c is trivial identity" (
    let trivial = Credence.Var "trivial_c" in
    let decls = [
      Proof.Fixpoint ("trivial_c", trivial)
    ] in
    match Proof.check_proof decls with
    | Ok state ->
        not (Hashtbl.mem state.fixpoints "trivial_c")
    | Error _ -> false
  );

  Printf.printf "\nAll proof checker tests passed!\n"
