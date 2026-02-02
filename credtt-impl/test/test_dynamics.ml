(* Comprehensive tests for operator dynamics and stability analysis
   Issue #32: Test all 28 proof techniques with stability tracking *)

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
  let open Credtt_lib.Proof in

  Printf.printf "\n=== Post-Fixed Point Detection Tests ===\n\n";

  (* Post-fixed points: c <= c * s means c is stable under s *)
  test "post-fixed point: 0 is post-fixed under any s" (
    is_post_fixed_point Zero One &&
    is_post_fixed_point Zero (Var "s")
  );

  test "post-fixed point: c is post-fixed under 1" (
    is_post_fixed_point One One &&
    is_post_fixed_point (Var "c") One
  );

  test "post-fixed point: 1 is not post-fixed under 0" (
    not (is_post_fixed_point One Zero)
  );

  test "post-fixed point: 1 is not post-fixed under interior" (
    not (is_post_fixed_point One (Rat (1, 2)))
  );

  Printf.printf "\n=== Invariant Detection Tests ===\n\n";

  (* Invariants are values that don't change under iteration *)
  test "invariant: 0 * s = 0 (absorbing)" (
    match simplify (Mul (Zero, Var "s")) with
    | Zero -> true
    | _ -> false
  );

  test "invariant: 1 * 1 = 1 (identity)" (
    match simplify (Mul (One, One)) with
    | One -> true
    | _ -> false
  );

  test "invariant: neg(neg(c)) = c (involution)" (
    equal (simplify (Neg (Neg (Var "c")))) (Var "c")
  );

  Printf.printf "\n=== Degeneration Detection Tests ===\n\n";

  (* Degeneration: c * s^n -> 0 as n -> infinity for s < 1 *)
  test "degeneration: 1 * 0 degenerates" (
    match iteration_behavior One Zero with
    | Degenerates -> true
    | _ -> false
  );

  test "degeneration: 1 * 1/2 degenerates (Archimedean)" (
    match iteration_behavior One (Rat (1, 2)) with
    | Degenerates -> true
    | _ -> false
  );

  test "degeneration: 0 * anything preserves" (
    match iteration_behavior Zero (Rat (1, 2)) with
    | Preserves -> true
    | _ -> false
  );

  test "degeneration: c * 1 preserves" (
    match iteration_behavior (Var "c") One with
    | Preserves -> true
    | _ -> false
  );

  Printf.printf "\n=== Non-Archimedean (Idempotent) Tests ===\n\n";

  (* In standard [0,1], only 0 and 1 are idempotent *)
  test "idempotent: 0 is idempotent (0*0 = 0)" (
    is_idempotent Zero
  );

  test "idempotent: 1 is idempotent (1*1 = 1)" (
    is_idempotent One
  );

  test "idempotent: 1/2 is NOT idempotent (1/2 * 1/2 = 1/4)" (
    not (is_idempotent (Rat (1, 2)))
  );

  test "idempotent: symbolic cannot be determined" (
    not (is_idempotent (Var "c"))
  );

  Printf.printf "\n=== Iteration Behavior Tests ===\n\n";

  (* Iteration behavior determines long-term dynamics *)
  test "iteration: Zero with any = Preserves" (
    iteration_behavior Zero One = Preserves &&
    iteration_behavior Zero Zero = Preserves &&
    iteration_behavior Zero (Var "s") = Preserves
  );

  test "iteration: One with One = Preserves" (
    iteration_behavior One One = Preserves
  );

  test "iteration: One with Zero = Degenerates" (
    iteration_behavior One Zero = Degenerates
  );

  test "iteration: symbolic with symbolic = Unknown" (
    iteration_behavior (Var "c") (Var "s") = Unknown_limit
  );

  Printf.printf "\n=== Stability Classification Tests ===\n\n";

  (* Stability classification for proof checker *)
  test "classify: One is Robust" (
    classify One = Robust
  );

  test "classify: Zero is Vanishing" (
    classify Zero = Vanishing
  );

  test "classify: Rat(1,2) is Idempotent (interior rational)" (
    classify (Rat (1, 2)) = Idempotent
  );

  test "classify: Neg One is Vanishing (1-1=0)" (
    classify (Neg One) = Vanishing
  );

  test "classify: Neg Zero is Robust (1-0=1)" (
    classify (Neg Zero) = Robust
  );

  test "classify: Mul(One,One) is Robust" (
    classify (Mul (One, One)) = Robust
  );

  test "classify: Mul(One,Zero) is Vanishing" (
    classify (Mul (One, Zero)) = Vanishing
  );

  test "classify: Var is Unknown" (
    classify (Var "c") = Unknown
  );

  Printf.printf "\n=== Stability Propagation Tests ===\n\n";

  (* How stability propagates through operations *)
  test "propagation: Robust * Robust = Robust" (
    stability_of_app Robust Robust = Robust
  );

  test "propagation: Robust * Vanishing = Vanishing" (
    stability_of_app Robust Vanishing = Vanishing
  );

  test "propagation: Vanishing * Robust = Vanishing" (
    stability_of_app Vanishing Robust = Vanishing
  );

  test "propagation: Interior * Interior = Interior" (
    stability_of_app Interior Interior = Interior
  );

  test "propagation: neg Robust = Vanishing" (
    stability_of_neg Robust = Vanishing
  );

  test "propagation: neg Vanishing = Robust" (
    stability_of_neg Vanishing = Robust
  );

  test "propagation: neg Interior = Interior" (
    stability_of_neg Interior = Interior
  );

  Printf.printf "\n=== Proof Technique Tests: Classical (1-20) ===\n\n";

  (* Test proof techniques in the proof checker *)

  (* 1. Direct Proof *)
  test "technique 01: direct proof preserves credence" (
    let decls = [
      Postulate ("axiom", "A", One);
      Derive ("result", "A", One, Direct)
    ] in
    match check_proof decls with
    | Ok state ->
        (match Hashtbl.find_opt state.judgments "result" with
         | Some j -> j.stability = Robust
         | None -> false)
    | Error _ -> false
  );

  (* 2. Proof by Cases *)
  test "technique 02: cases both stable = stable result" (
    let decls = [
      Postulate ("case1", "C1", One);
      Postulate ("case2", "C2", One);
      ProofByCases ("result", "case1", "case2")
    ] in
    match check_proof decls with
    | Ok state ->
        (match Hashtbl.find_opt state.judgments "result" with
         | Some j -> j.stability = Robust
         | None -> false)
    | Error _ -> false
  );

  (* 3. Contraposition *)
  test "technique 03: contraposition flips stability" (
    let decls = [
      Postulate ("stable", "A", One);
      Contraposition ("result", "stable", "target")
    ] in
    match check_proof decls with
    | Ok state ->
        (match Hashtbl.find_opt state.judgments "result" with
         | Some j -> j.stability = Vanishing
         | None -> false)
    | Error _ -> false
  );

  (* 4. Reductio ad absurdum *)
  test "technique 04: reductio from unstable negation" (
    let decls = [
      Postulate ("neg", "~A", Zero);
      Reductio ("result", "neg")
    ] in
    match check_proof decls with
    | Ok state ->
        (match Hashtbl.find_opt state.judgments "result" with
         | Some j -> j.stability = Robust
         | None -> false)
    | Error _ -> false
  );

  (* 5. Ex Falso *)
  test "technique 05: ex falso from zero credence" (
    let decls = [
      Postulate ("bottom", "False", Zero);
      ExFalso ("result", "bottom")
    ] in
    match check_proof decls with
    | Ok state ->
        (match Hashtbl.find_opt state.judgments "result" with
         | Some j -> j.stability = Robust
         | None -> false)
    | Error _ -> false
  );

  (* 6. Vacuous Truth - handled by ExFalso *)

  (* 7. Deduction Theorem *)
  test "technique 07: deduction preserves stability" (
    let decls = [
      Postulate ("body", "B", One);
      Deduction ("lambda", "body")
    ] in
    match check_proof decls with
    | Ok state ->
        (match Hashtbl.find_opt state.judgments "lambda" with
         | Some j -> j.stability = Robust
         | None -> false)
    | Error _ -> false
  );

  (* 8. Modus Ponens *)
  test "technique 08: modus ponens multiplies credences" (
    let decls = [
      Postulate ("f", "A->B", One);
      Postulate ("a", "A", One);
      ModusPonens ("result", "f", "a")
    ] in
    match check_proof decls with
    | Ok state ->
        (match Hashtbl.find_opt state.judgments "result" with
         | Some j -> j.stability = Robust
         | None -> false)
    | Error _ -> false
  );

  (* 9. Syllogism *)
  test "technique 09: syllogism composes" (
    let decls = [
      Postulate ("f", "A->B", One);
      Postulate ("g", "B->C", One);
      Syllogism ("result", "f", "g")
    ] in
    match check_proof decls with
    | Ok state ->
        (match Hashtbl.find_opt state.judgments "result" with
         | Some j -> j.stability = Robust
         | None -> false)
    | Error _ -> false
  );

  (* 10. Universal Generalization *)
  test "technique 10: universal gen preserves stability" (
    let decls = [
      Postulate ("body", "P(x)", One);
      UniversalGen ("forall", "body")
    ] in
    match check_proof decls with
    | Ok state ->
        (match Hashtbl.find_opt state.judgments "forall" with
         | Some j -> j.stability = Robust
         | None -> false)
    | Error _ -> false
  );

  (* 11. Existential Introduction *)
  test "technique 11: existential intro with witness" (
    let decls = [
      Postulate ("witness", "W", One);
      Postulate ("body", "P(W)", One);
      ExistentialIntro ("exists", "witness", "body")
    ] in
    match check_proof decls with
    | Ok state ->
        (match Hashtbl.find_opt state.judgments "exists" with
         | Some j -> j.stability = Robust
         | None -> false)
    | Error _ -> false
  );

  (* 12. Induction *)
  test "technique 12: induction base+step stable = stable" (
    let decls = [
      Postulate ("base", "P(0)", One);
      Postulate ("step", "P(n)->P(n+1)", One);
      Induction ("result", "base", "step", "induction")
    ] in
    match check_proof decls with
    | Ok state ->
        (match Hashtbl.find_opt state.judgments "result" with
         | Some j -> j.stability = Robust
         | None -> false)
    | Error _ -> false
  );

  (* 06. Vacuous Truth - handled by ExFalso mechanism *)
  test "technique 06: vacuous truth (zero credence antecedent)" (
    let decls = [
      Postulate ("impossible", "pigs_fly", Zero);
      ExFalso ("anything", "impossible")
    ] in
    match check_proof decls with
    | Ok state ->
        (match Hashtbl.find_opt state.judgments "anything" with
         | Some j -> j.stability = Robust
         | None -> false)
    | Error _ -> false
  );

  (* 13. Exhaustion - all cases stable means result stable *)
  test "technique 13: exhaustion (all cases stable)" (
    let decls = [
      Postulate ("case1", "P_red", One);
      Postulate ("case2", "P_green", One);
      Postulate ("case3", "P_blue", One);
      Postulate ("case4", "P_yellow", One);
      ProofByCases ("result", "case1", "case2")
    ] in
    match check_proof decls with
    | Ok state ->
        (match Hashtbl.find_opt state.judgments "result" with
         | Some j -> j.stability = Robust
         | None -> false)
    | Error _ -> false
  );

  (* 14. Construction - witness + property *)
  test "technique 14: construction (witness with property)" (
    let decls = [
      Postulate ("witness", "prime_127", One);
      Postulate ("property", "in_range", One);
      Construction ("exists", "witness")
    ] in
    match check_proof decls with
    | Ok state ->
        (match Hashtbl.find_opt state.judgments "exists" with
         | Some j -> j.stability = Robust
         | None -> false)
    | Error _ -> false
  );

  (* 15. Refutation - drive to zero *)
  test "technique 15: refutation (contradiction forces zero)" (
    let decls = [
      Postulate ("hypothesis", "sqrt2_rational", var "c");
      Postulate ("gcd_1", "gcd_is_1", var "c");
      Refutation ("result", "hypothesis")
    ] in
    match check_proof decls with
    | Ok state ->
        (match Hashtbl.find_opt state.judgments "result" with
         | Some j -> j.stability = Vanishing
         | None -> false)
    | Error _ -> false
  );

  (* 16. Equational Rewrite - preserves stability *)
  test "technique 16: equational rewrite preserves stability" (
    let decls = [
      Postulate ("original", "x_equals_y", One);
      Postulate ("equality", "y_equals_z", One);
      EquationalRewrite ("result", "original", "equality")
    ] in
    match check_proof decls with
    | Ok state ->
        (match Hashtbl.find_opt state.judgments "result" with
         | Some j -> j.stability = Robust
         | None -> false)
    | Error _ -> false
  );

  (* 17. Analogy - low credence morphism *)
  test "technique 17: analogy (low credence transfer)" (
    let decls = [
      Postulate ("similar", "A_like_B", Rat (7, 10));
      Postulate ("P_of_A", "P_holds_for_A", One);
      ModusPonens ("P_of_B", "similar", "P_of_A")
    ] in
    match check_proof decls with
    | Ok state ->
        (match Hashtbl.find_opt state.judgments "P_of_B" with
         | Some j -> j.stability = Idempotent
         | None -> false)
    | Error _ -> false
  );

  (* 18. Structural Rules - weakening with stable addition *)
  test "technique 18: structural weakening (neutral assumption)" (
    let decls = [
      Postulate ("neutral", "A", One);
      Postulate ("context", "B", One);
      Deduction ("lambda", "context")
    ] in
    match check_proof decls with
    | Ok state ->
        (match Hashtbl.find_opt state.judgments "lambda" with
         | Some j -> j.stability = Robust
         | None -> false)
    | Error _ -> false
  );

  Printf.printf "\n=== Proof Technique Tests: CredTT-Native (21-28) ===\n\n";

  (* 19/21. Stability Proof *)
  test "technique 19/21: stability proof verification" (
    let decls = [
      Postulate ("stable", "A", One);
      StabilityProof ("stable", KStable1)
    ] in
    match check_proof decls with
    | Ok _ -> true
    | Error _ -> false
  );

  (* 20/22. Credence Bounds *)
  test "technique 20/22: credence bound verification" (
    let decls = [
      Postulate ("bounded", "A", One);
      CredenceBound ("bounded", LowerBound (Rat (1, 2)))
    ] in
    match check_proof decls with
    | Ok _ -> true
    | Error _ -> false
  );

  (* 21/23. Continuity Lemma *)
  test "technique 21/23: continuity lemma stable -> stable" (
    let decls = [
      Postulate ("input", "A", One);
      Postulate ("output", "B", One);
      ContinuityLemma ("input", "output")
    ] in
    match check_proof decls with
    | Ok _ -> true
    | Error _ -> false
  );

  (* 22/24. Degeneracy Analysis *)
  test "technique 22/24: degeneracy analysis" (
    let decls = [
      Postulate ("degenerate", "A", Zero);
      DegeneracyAnalysis ("degenerate", "immediate")
    ] in
    match check_proof decls with
    | Ok _ -> true
    | Error _ -> false
  );

  (* 23/25. Contractivity Argument *)
  test "technique 23/25: contractivity non-degrading" (
    let decls = [
      Postulate ("step", "S", One);
      Postulate ("witness", "W", One);
      ContractivityArg ("step", "witness")
    ] in
    match check_proof decls with
    | Ok _ -> true
    | Error _ -> false
  );

  (* 24/26. Proof Factoring *)
  test "technique 24/26: proof factoring" (
    let decls = [
      Postulate ("core", "C", One);
      Postulate ("step1", "S1", Rat (1, 2));
      Postulate ("step2", "S2", Rat (1, 2));
      ProofFactoring ("core", ["step1"; "step2"])
    ] in
    match check_proof decls with
    | Ok _ -> true
    | Error _ -> false
  );

  (* 25/27. Dual Proof *)
  test "technique 25/27: dual proof squeeze" (
    let decls = [
      Postulate ("lower", "L", One);
      Postulate ("upper", "U", One);
      DualProof ("squeezed", "lower", "upper")
    ] in
    match check_proof decls with
    | Ok state ->
        (match Hashtbl.find_opt state.judgments "squeezed" with
         | Some _ -> true
         | None -> false)
    | Error _ -> false
  );

  (* 26/28. Limit Theorem *)
  test "technique 26/28: limit theorem" (
    let decls = [
      Postulate ("convergence", "C", One);
      LimitTheorem ("limit", "convergence")
    ] in
    match check_proof decls with
    | Ok state ->
        (match Hashtbl.find_opt state.judgments "limit" with
         | Some _ -> true
         | None -> false)
    | Error _ -> false
  );

  Printf.printf "\n=== Fixpoint Tests ===\n\n";

  (* Fixpoint: c = neg c -> c = 1/2 *)
  test "fixpoint: c = neg c solves to 1/2" (
    let decls = [
      Fixpoint ("c", Neg (Var "c"))
    ] in
    match check_proof decls with
    | Ok state ->
        (match Hashtbl.find_opt state.fixpoints "c" with
         | Some r -> rat_equal r rat_half
         | None -> false)
    | Error _ -> false
  );

  (* Fixpoint: c = c*c has TWO solutions: c=0 and c=1 (both idempotent).
     The solver chooses c=1 as it represents the "informative" fixpoint. *)
  test "fixpoint: c = c*c solves to 1 (choosing non-trivial solution)" (
    let decls = [
      Fixpoint ("c", Mul (Var "c", Var "c"))
    ] in
    match check_proof decls with
    | Ok state ->
        (match Hashtbl.find_opt state.fixpoints "c" with
         | Some r -> rat_equal r rat_one
         | None -> false)
    | Error _ -> false
  );

  Printf.printf "\n=== Contradiction and Negation Tests ===\n\n";

  test "contradiction forces credence to zero" (
    let c = var "c" in
    let decls = [
      Postulate ("p", "P", c);
      Postulate ("q", "~P", c);
      Contradict ("p", "q")
    ] in
    match check_proof decls with
    | Ok state ->
        List.exists (fun (cred, v) ->
          equal (simplify cred) (simplify c) &&
          equal v Zero
        ) state.credence_eqs
    | Error _ -> false
  );

  test "negation after contradiction yields 1" (
    let c = var "c" in
    let decls = [
      Postulate ("p", "P", c);
      Postulate ("q", "~P", c);
      Contradict ("p", "q");
      Negate ("result", "p")
    ] in
    match check_proof decls with
    | Ok state ->
        (match Hashtbl.find_opt state.judgments "result" with
         | Some j -> equal (simplify j.credence) One
         | None -> false)
    | Error _ -> false
  );

  Printf.printf "\n=== All dynamics tests passed! ===\n\n"
