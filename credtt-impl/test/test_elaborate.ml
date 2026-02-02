(* Unit tests for elaboration *)

let test name cond =
  if cond then
    Printf.printf "PASS: %s\n" name
  else begin
    Printf.printf "FAIL: %s\n" name;
    exit 1
  end

let () =
  let open Credtt_lib in

  (* Test THole raises ElaborationError (Issue #56) *)
  test "THole raises ElaborationError" (
    try
      let _ = Elaborate.elab_term Elaborate.empty_env Raw.THole in
      false
    with
    | Elaborate.ElaborationError Error.UnsupportedHole -> true
    | _ -> false
  );

  (* Test basic term elaboration works *)
  test "TVar elaborates to Var" (
    let env = Elaborate.extend_var Elaborate.empty_env "x" in
    match Elaborate.elab_term env (Raw.TVar "x") with
    | Syntax.Var 0 -> true
    | _ -> false
  );

  (* Test lambda elaboration *)
  test "TLam elaborates to Lam" (
    match Elaborate.elab_term Elaborate.empty_env (Raw.TLam ("x", Raw.TVar "x")) with
    | Syntax.Lam (_, Syntax.Var 0) -> true
    | _ -> false
  );

  (* Test pair elaboration *)
  test "TPair elaborates to Pair" (
    let env = Elaborate.extend_var Elaborate.empty_env "x" in
    match Elaborate.elab_term env (Raw.TPair (Raw.TVar "x", Raw.TVar "x")) with
    | Syntax.Pair (Syntax.Var 0, Syntax.Var 0) -> true
    | _ -> false
  );

  (* Test fst elaboration via app *)
  test "TApp fst elaborates to Fst" (
    let env = Elaborate.extend_var Elaborate.empty_env "p" in
    match Elaborate.elab_term env (Raw.TApp (Raw.TVar "fst", Raw.TVar "p")) with
    | Syntax.Fst (Syntax.Var 0) -> true
    | _ -> false
  );

  (* Test snd elaboration via app *)
  test "TApp snd elaborates to Snd" (
    let env = Elaborate.extend_var Elaborate.empty_env "p" in
    match Elaborate.elab_term env (Raw.TApp (Raw.TVar "snd", Raw.TVar "p")) with
    | Syntax.Snd (Syntax.Var 0) -> true
    | _ -> false
  );

  (* Test inl elaboration *)
  test "TInl elaborates to Inl" (
    let env = Elaborate.extend_var Elaborate.empty_env "x" in
    match Elaborate.elab_term env (Raw.TInl (Raw.TVar "x")) with
    | Syntax.Inl (Syntax.Var 0) -> true
    | _ -> false
  );

  (* Test inr elaboration *)
  test "TInr elaborates to Inr" (
    let env = Elaborate.extend_var Elaborate.empty_env "x" in
    match Elaborate.elab_term env (Raw.TInr (Raw.TVar "x")) with
    | Syntax.Inr (Syntax.Var 0) -> true
    | _ -> false
  );

  (* Test refl elaboration *)
  test "TRefl elaborates to Refl" (
    match Elaborate.elab_term Elaborate.empty_env Raw.TRefl with
    | Syntax.Refl -> true
    | _ -> false
  );

  (* Test type elaboration: arrow type with known types *)
  test "TyArrow elaborates to TPi" (
    match Elaborate.elab_ty Elaborate.empty_env (Raw.TyArrow (Raw.TyVar "Nat", Raw.TyVar "Bool")) with
    | Syntax.TPi (_, _) -> true
    | _ -> false
  );

  (* Test type elaboration: sum type with known types *)
  test "TySum elaborates to TSum" (
    match Elaborate.elab_ty Elaborate.empty_env (Raw.TySum (Raw.TyVar "Nat", Raw.TyVar "Nat")) with
    | Syntax.TSum (_, _) -> true
    | _ -> false
  );

  (* Issue #79: Test unbound type name raises error *)
  test "Unbound type name raises ElaborationError" (
    try
      let _ = Elaborate.elab_ty Elaborate.empty_env (Raw.TyVar "UnknownType") in
      false
    with
    | Elaborate.ElaborationError (Error.UnboundTypeName "UnknownType") -> true
    | _ -> false
  );

  (* Issue #79: Test type application raises error *)
  test "TyApp raises ElaborationError" (
    try
      let _ = Elaborate.elab_ty Elaborate.empty_env (Raw.TyApp (Raw.TyVar "List", Raw.TyVar "Nat")) in
      false
    with
    | Elaborate.ElaborationError (Error.UnsupportedConstruct _) -> true
    | _ -> false
  );

  (* Issue #81: Test unbound variable raises error *)
  test "Unbound variable raises ElaborationError" (
    try
      let _ = Elaborate.elab_term Elaborate.empty_env (Raw.TVar "unbound_var") in
      false
    with
    | Elaborate.ElaborationError (Error.UnboundName "unbound_var") -> true
    | _ -> false
  );

  (* Test credence elaboration *)
  test "CZero elaborates to zero" (
    Credence.equal (Elaborate.elab_credence Raw.CZero) Credence.zero
  );

  test "COne elaborates to one" (
    Credence.equal (Elaborate.elab_credence Raw.COne) Credence.one
  );

  test "CMul elaborates to mul" (
    let c = Elaborate.elab_credence (Raw.CMul (Raw.COne, Raw.COne)) in
    Credence.equal c Credence.one
  );

  (* Test nested THole still raises error *)
  test "THole in application raises ElaborationError" (
    try
      let _ = Elaborate.elab_term Elaborate.empty_env (Raw.TApp (Raw.TVar "f", Raw.THole)) in
      false
    with
    | Elaborate.ElaborationError Error.UnsupportedHole -> true
    | _ -> false
  );

  test "THole in pair raises ElaborationError" (
    try
      let env = Elaborate.extend_var Elaborate.empty_env "x" in
      let _ = Elaborate.elab_term env (Raw.TPair (Raw.TVar "x", Raw.THole)) in
      false
    with
    | Elaborate.ElaborationError Error.UnsupportedHole -> true
    | _ -> false
  );

  Printf.printf "\nAll elaboration tests passed!\n"
