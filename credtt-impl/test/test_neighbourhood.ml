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

  (* ============================================================
     ORDER-THEORETIC DYNAMICS TESTS
     ============================================================ *)

  (* Post-fixed point tests: c ≤ c · s *)
  test "is_post_fixed_point Zero s = true (0 ≤ 0·s)" (
    is_post_fixed_point Zero One
  );
  test "is_post_fixed_point c One = true (c ≤ c·1 = c)" (
    is_post_fixed_point One One && is_post_fixed_point (Var "c") One
  );
  test "is_post_fixed_point One Zero = false (1 ≤ 0 is false)" (
    not (is_post_fixed_point One Zero)
  );

  (* Idempotent tests: c · c = c *)
  test "is_idempotent One = true (1·1 = 1)" (is_idempotent One);
  test "is_idempotent Zero = true (0·0 = 0)" (is_idempotent Zero);
  test "is_idempotent (Var x) = false (cannot determine)" (
    not (is_idempotent (Var "x"))
  );

  (* Iteration behavior tests *)
  test "iteration_behavior One s = Preserves (1·s^n = 1·s = s-dependent)" (
    match iteration_behavior One One with
    | Preserves -> true
    | _ -> false
  );
  test "iteration_behavior Zero s = Preserves (0·s^n = 0)" (
    match iteration_behavior Zero (Var "s") with
    | Preserves -> true
    | _ -> false
  );
  test "iteration_behavior (Var x) s = Unknown_limit" (
    match iteration_behavior (Var "x") (Var "s") with
    | Unknown_limit -> true
    | _ -> false
  );

  (* Classify dynamics tests *)
  test "classify (Mul (One, Zero)) = Vanishing" (
    match classify (Mul (One, Zero)) with
    | Vanishing -> true
    | _ -> false
  );
  test "classify (Mul (One, One)) = Robust" (
    match classify (Mul (One, One)) with
    | Robust -> true
    | _ -> false
  );
  test "classify (Neg (Neg One)) = Robust" (
    match classify (Neg (Neg One)) with
    | Robust -> true
    | _ -> false
  );

  (* Stability propagation through application *)
  test "stability_of_app Robust Robust = Robust (1·1 = 1)" (
    match stability_of_app Robust Robust with
    | Robust -> true
    | _ -> false
  );
  test "stability_of_app Robust Vanishing = Vanishing (1·0 = 0)" (
    match stability_of_app Robust Vanishing with
    | Vanishing -> true
    | _ -> false
  );
  test "stability_of_app Idempotent Idempotent = Idempotent" (
    match stability_of_app Idempotent Idempotent with
    | Idempotent -> true
    | _ -> false
  );

  (* Stability of negation *)
  test "stability_of_neg Unknown = Unknown" (
    match stability_of_neg Unknown with
    | Unknown -> true
    | _ -> false
  );
  test "stability_of_neg Idempotent = Idempotent" (
    match stability_of_neg Idempotent with
    | Idempotent -> true
    | _ -> false
  );

  (* Stability of composition *)
  test "stability_of_compose Robust Unknown = Unknown" (
    match stability_of_compose Robust Unknown with
    | Unknown -> true
    | _ -> false
  );
  test "stability_of_compose Vanishing Robust = Vanishing" (
    match stability_of_compose Vanishing Robust with
    | Vanishing -> true
    | _ -> false
  );

  (* ============================================================
     INTERIOR POINT CLASSIFICATION TESTS (Issue #133)
     ============================================================
     Interior points 0 < c < 1 must be classified as Interior,
     NOT as Idempotent. Only 0 and 1 are idempotent under
     standard multiplication. *)

  test "classify_neighbourhood Point 1/2 = Interior (NOT Idempotent)" (
    match classify_neighbourhood (Point rat_half) with
    | Interior -> true
    | Idempotent -> false  (* This was the bug! *)
    | _ -> false
  );

  test "classify_neighbourhood Point 1/4 = Interior" (
    let quarter = { num = 1; den = 4 } in
    match classify_neighbourhood (Point quarter) with
    | Interior -> true
    | _ -> false
  );

  test "classify_neighbourhood Point 3/4 = Interior" (
    let three_quarters = { num = 3; den = 4 } in
    match classify_neighbourhood (Point three_quarters) with
    | Interior -> true
    | _ -> false
  );

  test "1/2 is NOT idempotent (1/2 * 1/2 = 1/4 != 1/2)" (
    let half_credence = of_rational rat_half in
    not (is_idempotent half_credence)
  );

  (* ============================================================
     ITERATION BEHAVIOR TESTS (Issue #104)
     ============================================================
     For concrete endpoint credences (0, 1), iteration_behavior
     should return concrete results. For symbolic credences
     (including Vars representing rationals), Unknown_limit is
     the correct conservative behavior. *)

  test "iteration_behavior 1 with 1 = Preserves" (
    match iteration_behavior One One with
    | Preserves -> true
    | _ -> false
  );

  test "iteration_behavior 0 with any = Preserves (0 * s^n = 0)" (
    match iteration_behavior Zero One with
    | Preserves -> true
    | _ -> false
  );

  test "iteration_behavior c with 0 = Degenerates for c = 1" (
    match iteration_behavior One Zero with
    | Degenerates -> true
    | _ -> false
  );

  test "iteration_behavior (Neg One) with 1 = Preserves (~1=0, 0*1^n=0)" (
    match iteration_behavior (Neg One) One with
    | Preserves -> true
    | _ -> false
  );

  test "iteration_behavior (Neg Zero) with 0 = Degenerates (~0=1, 1*0^n=0)" (
    match iteration_behavior (Neg Zero) Zero with
    | Degenerates -> true
    | _ -> false
  );

  test "iteration_behavior (Var c) with Zero = Degenerates (any c * 0^n = 0)" (
    match iteration_behavior (Var "c") Zero with
    | Degenerates -> true
    | _ -> false
  );

  test "iteration_behavior symbolic with symbolic = Unknown_limit (conservative)" (
    let symbolic = Var "c" in
    match iteration_behavior symbolic symbolic with
    | Unknown_limit -> true
    | _ -> false
  );

  (* ============================================================
     INTERIOR STABILITY PROPAGATION TESTS
     ============================================================ *)

  test "stability_of_app Interior Interior = Interior" (
    match stability_of_app Interior Interior with
    | Interior -> true
    | _ -> false
  );

  test "stability_of_app Robust Interior = Interior (1 * c = c)" (
    match stability_of_app Robust Interior with
    | Interior -> true
    | _ -> false
  );

  test "stability_of_app Interior Vanishing = Vanishing (c * 0 = 0)" (
    match stability_of_app Interior Vanishing with
    | Vanishing -> true
    | _ -> false
  );

  test "stability_of_neg Interior = Interior (~c for 0<c<1 gives 0<1-c<1)" (
    match stability_of_neg Interior with
    | Interior -> true
    | _ -> false
  );

  test "is_interior Interior = true" (is_interior Interior);
  test "is_interior Robust = false" (not (is_interior Robust));
  test "is_interior Vanishing = false" (not (is_interior Vanishing));

  (* ============================================================
     INTERVAL CLASSIFICATION TESTS
     ============================================================ *)

  test "classify_neighbourhood Interval (0.1, 0.9) = Interior" (
    let lo = { num = 1; den = 10 } in
    let hi = { num = 9; den = 10 } in
    match classify_neighbourhood (Interval { lo; hi; lo_closed = true; hi_closed = true }) with
    | Interior -> true
    | _ -> false
  );

  test "classify_neighbourhood Interval (0, 0.5) = Interior (contains interior)" (
    let lo = rat_zero in
    let hi = rat_half in
    match classify_neighbourhood (Interval { lo; hi; lo_closed = true; hi_closed = true }) with
    | Interior -> true
    | _ -> false
  );

  test "classify_neighbourhood Interval (0.5, 1) = Interior" (
    let lo = rat_half in
    let hi = rat_one in
    match classify_neighbourhood (Interval { lo; hi; lo_closed = true; hi_closed = true }) with
    | Interior -> true
    | _ -> false
  );

  Printf.printf "\nAll neighbourhood tests passed!\n"
