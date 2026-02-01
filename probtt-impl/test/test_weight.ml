(* Unit tests for weight algebra *)

let test name cond =
  if cond then
    Printf.printf "PASS: %s\n" name
  else begin
    Printf.printf "FAIL: %s\n" name;
    exit 1
  end

let () =
  let open Probtt_lib.Weight in

  test "zero is absorbing (left)" (equal (mul zero one) zero);
  test "zero is absorbing (right)" (equal (mul one zero) zero);
  test "one is identity (left)" (equal (mul one one) one);
  test "one is identity (right)" (equal (simplify (mul one (var "w"))) (var "w"));

  test "neg zero = one" (equal (neg zero) one);
  test "neg one = zero" (equal (neg one) zero);
  test "double negation" (equal (neg (neg one)) one);
  test "double negation var" (equal (simplify (neg (neg (var "w")))) (var "w"));

  test "zero <= anything" (leq zero one);
  test "zero <= var" (leq zero (var "w"));
  test "anything <= one" (leq (var "w") one);
  test "equal implies leq" (leq one one);

  test "mul simplifies to zero" (equal (simplify (mul (var "w") zero)) zero);
  test "mul simplifies identity" (equal (simplify (mul (var "w") one)) (var "w"));

  (* Rational weight tests *)
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
  test "solve_fixpoint w = ¬w gives 1/2" (
    match solve_fixpoint (fun w -> Neg w) "w" with
    | Some r -> rat_equal r rat_half
    | None -> false
  );
  test "solve_fixpoint w = w·w gives 1" (
    match solve_fixpoint (fun w -> Mul (w, w)) "w" with
    | Some r -> rat_equal r rat_one
    | None -> false
  );

  (* Constraint solver tests *)
  test "solve_constraints [w = 0]" (
    let constraints = [CEqual (Var "w", Zero)] in
    let solutions = solve_constraints constraints in
    match List.assoc_opt "w" solutions with
    | Some r -> rat_equal r rat_zero
    | None -> false
  );
  test "solve_constraints [fixpoint w = ¬w]" (
    let constraints = [CFixpoint ("w", fun x -> Neg x)] in
    let solutions = solve_constraints constraints in
    match List.assoc_opt "w" solutions with
    | Some r -> rat_equal r rat_half
    | None -> false
  );

  Printf.printf "\nAll weight tests passed!\n"
