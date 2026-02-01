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

  Printf.printf "\nAll proof checker tests passed!\n"
