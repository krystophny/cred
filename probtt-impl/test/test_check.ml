(* Unit tests for type checker *)

let test name cond =
  if cond then
    Printf.printf "PASS: %s\n" name
  else begin
    Printf.printf "FAIL: %s\n" name;
    exit 1
  end

let () =
  let open Probtt_lib in
  let open Syntax in

  let a_ty = TBase 0 in

  test "star : Unit @ 1" (
    match Check.check Context.empty Star TUnit with
    | Ok w -> Weight.equal w Weight.one
    | Error _ -> false
  );

  test "var 0 in context" (
    let ctx = Context.extend Context.empty a_ty in
    match Check.infer ctx (Var 0) with
    | Ok (_, w) -> Weight.equal w Weight.one
    | Error _ -> false
  );

  test "lambda : A -> A @ 1" (
    let lam = Lam (a_ty, Var 0) in
    let ty = TPi (a_ty, Subst.wk_ty a_ty) in
    match Check.check Context.empty lam ty with
    | Ok w -> Weight.equal w Weight.one
    | Error _ -> false
  );

  test "pair : A * A @ 1" (
    let ctx = Context.extend Context.empty a_ty in
    let pair = Pair (Var 0, Var 0) in
    let ty = TSigma (a_ty, Subst.wk_ty a_ty) in
    match Check.check ctx pair ty with
    | Ok w -> Weight.equal w Weight.one
    | Error _ -> false
  );

  test "inl : A + B" (
    let ctx = Context.extend Context.empty a_ty in
    let inl = Inl (Var 0) in
    let ty = TSum (a_ty, a_ty) in
    match Check.check ctx inl ty with
    | Ok w -> Weight.equal w Weight.one
    | Error _ -> false
  );

  Printf.printf "\nAll type checking tests passed!\n"
