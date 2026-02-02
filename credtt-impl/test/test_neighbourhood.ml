(* Unit tests for neighbourhood semantics *)

let test name cond =
  if cond then
    Printf.printf "PASS: %s\n" name
  else begin
    Printf.printf "FAIL: %s\n" name;
    exit 1
  end

let () =
  let open Credtt_lib.Credence in
  let open Credtt_lib.Neighbourhood in

  (* Point neighbourhood tests *)
  test "of_credence Zero = Point 0" (
    match of_credence Zero with
    | Point r -> rat_equal r rat_zero
    | _ -> false
  );

  test "of_credence One = Point 1" (
    match of_credence One with
    | Point r -> rat_equal r rat_one
    | _ -> false
  );

  test "of_credence (Var x) = Full" (
    match of_credence (Var "x") with
    | Full -> true
    | _ -> false
  );

  (* Stability classification tests *)
  test "classify One = Robust" (
    match classify One with
    | Robust -> true
    | _ -> false
  );

  test "classify Zero = Vanishing" (
    match classify Zero with
    | Vanishing -> true
    | _ -> false
  );

  test "classify (Var x) = Unknown" (
    match classify (Var "x") with
    | Unknown -> true
    | _ -> false
  );

  test "classify (Neg Zero) = Robust" (
    match classify (Neg Zero) with
    | Robust -> true
    | _ -> false
  );

  test "classify (Neg One) = Vanishing" (
    match classify (Neg One) with
    | Vanishing -> true
    | _ -> false
  );

  (* Perturbation tests *)
  (* Note: perturb only works on credences that can be converted to rational.
     of_rational creates Var for non-trivial rationals, which can't be converted back.
     So we test with Zero and One which do have computable perturbations. *)
  test "perturb Zero creates interval [0, epsilon]" (
    let epsilon = { num = 1; den = 10 } in
    match perturb Zero ~epsilon with
    | Interval { lo; hi; _ } ->
        rat_equal lo rat_zero && rat_equal hi epsilon
    | _ -> false
  );

  test "perturb One creates interval [1-epsilon, 1]" (
    let epsilon = { num = 1; den = 10 } in
    let expected_lo = { num = 9; den = 10 } in
    match perturb One ~epsilon with
    | Interval { lo; hi; _ } ->
        rat_equal lo expected_lo && rat_equal hi rat_one
    | _ -> false
  );

  test "perturb Var returns Full" (
    let epsilon = { num = 1; den = 10 } in
    match perturb (Var "x") ~epsilon with
    | Full -> true
    | _ -> false
  );

  (* Intersection tests *)
  test "intersect Point Point same = Point" (
    let p = Point rat_half in
    match intersect p p with
    | Some (Point r) -> rat_equal r rat_half
    | _ -> false
  );

  test "intersect Point Point different = Empty" (
    let p1 = Point rat_zero in
    let p2 = Point rat_one in
    match intersect p1 p2 with
    | Some Empty -> true
    | _ -> false
  );

  test "intersect Full x = x" (
    let p = Point rat_half in
    match intersect Full p with
    | Some (Point r) -> rat_equal r rat_half
    | _ -> false
  );

  test "intersect Empty x = Empty" (
    let p = Point rat_half in
    match intersect Empty p with
    | Some Empty -> true
    | _ -> false
  );

  (* Union tests *)
  test "union Point Point same = Point" (
    let p = Point rat_half in
    match union p p with
    | Point r -> rat_equal r rat_half
    | _ -> false
  );

  test "union Empty x = x" (
    let p = Point rat_half in
    match union Empty p with
    | Point r -> rat_equal r rat_half
    | _ -> false
  );

  test "union Full x = Full" (
    let p = Point rat_half in
    match union Full p with
    | Full -> true
    | _ -> false
  );

  (* Stability propagation tests *)
  test "stability_of_app Robust Robust = Robust" (
    match stability_of_app Robust Robust with
    | Robust -> true
    | _ -> false
  );

  test "stability_of_app Vanishing Robust = Vanishing" (
    match stability_of_app Vanishing Robust with
    | Vanishing -> true
    | _ -> false
  );

  test "stability_of_app Robust Vanishing = Vanishing" (
    match stability_of_app Robust Vanishing with
    | Vanishing -> true
    | _ -> false
  );

  test "stability_of_neg Robust = Vanishing" (
    match stability_of_neg Robust with
    | Vanishing -> true
    | _ -> false
  );

  test "stability_of_neg Vanishing = Robust" (
    match stability_of_neg Vanishing with
    | Robust -> true
    | _ -> false
  );

  test "stability_of_compose preserves stability" (
    match stability_of_compose Robust Robust with
    | Robust -> true
    | _ -> false
  );

  (* is_stable / is_unstable tests *)
  test "is_stable Robust = true" (is_stable Robust);
  test "is_stable Vanishing = false" (not (is_stable Vanishing));
  test "is_stable Idempotent = false" (not (is_stable Idempotent));

  test "is_unstable Vanishing = true" (is_unstable Vanishing);
  test "is_unstable Robust = false" (not (is_unstable Robust));
  test "is_unstable Idempotent = false" (not (is_unstable Idempotent));

  (* Classify neighbourhood tests *)
  test "classify_neighbourhood Point 1 = Robust" (
    match classify_neighbourhood (Point rat_one) with
    | Robust -> true
    | _ -> false
  );

  test "classify_neighbourhood Point 0 = Vanishing" (
    match classify_neighbourhood (Point rat_zero) with
    | Vanishing -> true
    | _ -> false
  );

  test "classify_neighbourhood Full = Unknown" (
    match classify_neighbourhood Full with
    | Unknown -> true
    | _ -> false
  );

  test "classify_neighbourhood Empty = Vanishing" (
    match classify_neighbourhood Empty with
    | Vanishing -> true
    | _ -> false
  );

  (* Propagation through function tests *)
  (* Note: propagate converts to credence and back, so only works for 0 and 1 *)
  test "propagate Point 1 through identity" (
    let p = Point rat_one in
    let f c = c in
    match propagate p f with
    | Point r -> rat_equal r rat_one
    | _ -> false
  );

  test "propagate Point 0 through identity" (
    let p = Point rat_zero in
    let f c = c in
    match propagate p f with
    | Point r -> rat_equal r rat_zero
    | _ -> false
  );

  (* Credence stability predicates *)
  test "is_stable_near_one One = true" (is_stable_near_one One);
  test "is_stable_near_one Zero = false" (not (is_stable_near_one Zero));

  test "is_unstable_near_zero Zero = true" (is_unstable_near_zero Zero);
  test "is_unstable_near_zero One = false" (not (is_unstable_near_zero One));

  Printf.printf "\nAll neighbourhood tests passed!\n"
