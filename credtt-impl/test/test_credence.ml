(* Unit tests for credence algebra *)

let test name cond =
  if cond then
    Printf.printf "PASS: %s\n" name
  else begin
    Printf.printf "FAIL: %s\n" name;
    exit 1
  end

let () =
  let open Credtt_lib.Credence in

  test "zero is absorbing (left)" (equal (mul zero one) zero);
  test "zero is absorbing (right)" (equal (mul one zero) zero);
  test "one is identity (left)" (equal (mul one one) one);
  test "one is identity (right)" (equal (simplify (mul one (var "c"))) (var "c"));

  test "neg zero = one" (equal (neg zero) one);
  test "neg one = zero" (equal (neg one) zero);
  test "double negation" (equal (neg (neg one)) one);
  test "double negation var" (equal (simplify (neg (neg (var "c")))) (var "c"));

  test "zero <= anything" (leq zero one);
  test "zero <= var" (leq zero (var "c"));
  test "anything <= one" (leq (var "c") one);
  test "equal implies leq" (leq one one);

  test "mul simplifies to zero" (equal (simplify (mul (var "c") zero)) zero);
  test "mul simplifies identity" (equal (simplify (mul (var "c") one)) (var "c"));

  (* Rational credence tests *)
  test "rat_zero equals 0" (rat_equal rat_zero { num = 0; den = 1 });
  test "rat_one equals 1" (rat_equal rat_one { num = 1; den = 1 });
  test "rat_half equals 1/2" (rat_equal rat_half { num = 1; den = 2 });
  test "rat_mul 1/2 * 1/2 = 1/4" (
    rat_equal (rat_mul rat_half rat_half) { num = 1; den = 4 }
  );
  test "rat_neg 1/2 = 1/2" (rat_equal (rat_neg rat_half) rat_half);
  test "rat_neg 0 = 1" (rat_equal (rat_neg rat_zero) rat_one);
  test "rat_neg 1 = 0" (rat_equal (rat_neg rat_one) rat_zero);

  (* to_rational tests *)
  test "to_rational Zero = 0" (
    match to_rational Zero with
    | Some r -> rat_equal r rat_zero
    | None -> false
  );
  test "to_rational One = 1" (
    match to_rational One with
    | Some r -> rat_equal r rat_one
    | None -> false
  );
  test "to_rational (Neg Zero) = 1" (
    match to_rational (Neg Zero) with
    | Some r -> rat_equal r rat_one
    | None -> false
  );
  test "to_rational (Var x) = None" (
    match to_rational (Var "x") with
    | Some _ -> false
    | None -> true
  );

  (* Fixpoint solver tests *)
  test "solve_negation_fixpoint = 1/2" (
    rat_equal (solve_negation_fixpoint ()) rat_half
  );
  test "solve_fixpoint c = neg c gives 1/2" (
    match solve_fixpoint (fun c -> Neg c) "c" with
    | Some r -> rat_equal r rat_half
    | None -> false
  );
  test "solve_fixpoint c = c*c gives 1" (
    match solve_fixpoint (fun c -> Mul (c, c)) "c" with
    | Some r -> rat_equal r rat_one
    | None -> false
  );

  (* Constraint solver tests *)
  test "solve_constraints [c = 0]" (
    let constraints = [CEqual (Var "c", Zero)] in
    let solutions = solve_constraints constraints in
    match List.assoc_opt "c" solutions with
    | Some r -> rat_equal r rat_zero
    | None -> false
  );
  test "solve_constraints [fixpoint c = neg c]" (
    let constraints = [CFixpoint ("c", fun x -> Neg x)] in
    let solutions = solve_constraints constraints in
    match List.assoc_opt "c" solutions with
    | Some r -> rat_equal r rat_half
    | None -> false
  );

  (* Dependent credence tests *)
  test "dep_var creates DepVar" (
    match dep_var "x" 0 with
    | DepVar ("x", 0) -> true
    | _ -> false
  );

  test "sup creates Sup" (
    match sup "x" one with
    | Sup ("x", One) -> true
    | _ -> false
  );

  test "inf creates Inf" (
    match inf "x" one with
    | Inf ("x", One) -> true
    | _ -> false
  );

  test "sup with constant simplifies" (
    match simplify (sup "x" one) with
    | One -> true
    | _ -> false
  );

  test "inf with constant simplifies" (
    match simplify (inf "x" zero) with
    | Zero -> true
    | _ -> false
  );

  test "depends_on_var detects dependency" (
    depends_on_var "x" (dep_var "x" 0)
  );

  test "depends_on_var returns false for different var" (
    not (depends_on_var "y" (dep_var "x" 0))
  );

  test "dependent_pi_credence creates sup for dependent" (
    let body = dep_var "x" 0 in
    match dependent_pi_credence "x" body with
    | Sup ("x", DepVar ("x", 0)) -> true
    | _ -> false
  );

  test "dependent_pi_credence preserves constant" (
    match dependent_pi_credence "x" one with
    | One -> true
    | _ -> false
  );

  Printf.printf "\nAll credence tests passed!\n"
