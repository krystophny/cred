(* Unit tests for credence inference *)

let test name cond =
  if cond then
    Printf.printf "PASS: %s\n" name
  else begin
    Printf.printf "FAIL: %s\n" name;
    exit 1
  end

let () =
  let open Credtt_lib.Credence in

  (* Test fresh inference variable generation *)
  reset_infer ();
  let i1 = fresh_infer () in
  let i2 = fresh_infer () in
  test "fresh_infer generates unique variables" (
    match i1, i2 with
    | Infer 0, Infer 1 -> true
    | _ -> false
  );

  (* Test simplification preserves Infer *)
  test "simplify preserves Infer" (
    match simplify (Infer 42) with
    | Infer 42 -> true
    | _ -> false
  );

  (* Test multiplication with Infer *)
  test "mul with Infer simplifies correctly" (
    let c = simplify (mul (Infer 0) one) in
    match c with
    | Infer 0 -> true
    | _ -> false
  );
  test "mul Infer with zero = zero" (
    equal (simplify (mul (Infer 0) zero)) zero
  );

  (* Test unification *)
  reset_infer ();
  test "unify Infer with Zero" (
    match unify [] (Infer 0) Zero with
    | Unified s ->
        (match List.assoc_opt 0 s with
         | Some Zero -> true
         | _ -> false)
    | _ -> false
  );

  test "unify Infer with One" (
    match unify [] (Infer 1) One with
    | Unified s ->
        (match List.assoc_opt 1 s with
         | Some One -> true
         | _ -> false)
    | _ -> false
  );

  test "unify Infer with Var" (
    match unify [] (Infer 2) (Var "c") with
    | Unified s ->
        (match List.assoc_opt 2 s with
         | Some (Var "c") -> true
         | _ -> false)
    | _ -> false
  );

  test "unify two Infers" (
    match unify [] (Infer 3) (Infer 4) with
    | Unified s ->
        (match List.assoc_opt 3 s with
         | Some (Infer 4) -> true
         | _ -> false)
    | _ -> false
  );

  (* Test fixpoint detection in unification *)
  test "unify detects fixpoint ?n = neg ?n" (
    match unify [] (Infer 5) (Neg (Infer 5)) with
    | Fixpoint (5, _) -> true
    | _ -> false
  );

  (* Test apply_subst *)
  test "apply_subst replaces Infer" (
    let s = [(0, Zero); (1, One)] in
    equal (apply_subst s (Infer 0)) Zero &&
    equal (apply_subst s (Infer 1)) One
  );

  test "apply_subst leaves unbound Infer" (
    let s = [(0, Zero)] in
    match apply_subst s (Infer 99) with
    | Infer 99 -> true
    | _ -> false
  );

  test "apply_subst through Mul" (
    let s = [(0, One)] in
    let c = apply_subst s (Mul (Infer 0, Var "c")) in
    equal c (Var "c")
  );

  test "apply_subst through Neg" (
    let s = [(0, Zero)] in
    let c = apply_subst s (Neg (Infer 0)) in
    equal c One
  );

  (* Test inference context *)
  reset_infer ();
  let ctx = create_infer_ctx () in
  add_constraint ctx (Infer 0) Zero;
  test "solve_inference with single constraint" (
    match solve_inference ctx with
    | Ok s ->
        (match List.assoc_opt 0 s with
         | Some Zero -> true
         | _ -> false)
    | Error _ -> false
  );

  (* Test multiple constraints *)
  reset_infer ();
  let ctx2 = create_infer_ctx () in
  add_constraint ctx2 (Infer 0) (Var "c");
  add_constraint ctx2 (Infer 1) One;
  test "solve_inference with multiple constraints" (
    match solve_inference ctx2 with
    | Ok s ->
        let v0 = List.assoc_opt 0 s in
        let v1 = List.assoc_opt 1 s in
        (match v0, v1 with
         | Some (Var "c"), Some One -> true
         | _ -> false)
    | Error _ -> false
  );

  (* Test finalize_credence *)
  reset_infer ();
  let ctx3 = create_infer_ctx () in
  add_constraint ctx3 (Infer 0) Zero;
  (match solve_inference ctx3 with
   | Ok _ ->
       test "finalize_credence resolves Infer to value" (
         let c = finalize_credence ctx3 (Mul (Infer 0, Var "x")) in
         equal c Zero
       )
   | Error _ -> test "finalize_credence resolves Infer to value" false);

  (* Test has_infer *)
  test "has_infer detects Infer in term" (
    has_infer (Mul (Infer 0, One)) &&
    has_infer (Neg (Infer 1)) &&
    not (has_infer Zero) &&
    not (has_infer (Var "c"))
  );

  (* Test collect_infers *)
  test "collect_infers finds all Infer vars" (
    let vars = collect_infers [] (Mul (Infer 0, Neg (Infer 1))) in
    List.mem 0 vars && List.mem 1 vars && List.length vars = 2
  );

  (* Test infer_derivation_credence *)
  test "infer_derivation_credence preserves credence for known steps" (
    let c = Var "c" in
    equal (infer_derivation_credence ~from_credence:c ~step:"algebra") c &&
    equal (infer_derivation_credence ~from_credence:c ~step:"substitution") c &&
    equal (infer_derivation_credence ~from_credence:c ~step:"self_reference") c
  );

  Printf.printf "\nAll credence inference tests passed!\n"
