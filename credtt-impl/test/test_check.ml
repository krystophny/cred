(* Unit tests for type checker *)

let test name cond =
  if cond then
    Printf.printf "PASS: %s\n" name
  else begin
    Printf.printf "FAIL: %s\n" name;
    exit 1
  end

let () =
  let open Credtt_lib in
  let open Syntax in

  let a_ty = TBase 0 in

  test "var 0 in context" (
    let ctx = Context.extend Context.empty a_ty in
    match Check.infer ctx (Var 0) with
    | Ok (_, c) -> Credence.equal c Credence.one
    | Error _ -> false
  );

  test "lambda : A -> A @ 1" (
    let lam = Lam (a_ty, Var 0) in
    let ty = TPi (a_ty, Subst.wk_ty a_ty) in
    match Check.check Context.empty lam ty with
    | Ok c -> Credence.equal c Credence.one
    | Error _ -> false
  );

  test "pair : A * A @ 1" (
    let ctx = Context.extend Context.empty a_ty in
    let pair = Pair (Var 0, Var 0) in
    let ty = TSigma (a_ty, Subst.wk_ty a_ty) in
    match Check.check ctx pair ty with
    | Ok c -> Credence.equal c Credence.one
    | Error _ -> false
  );

  test "inl : A + B" (
    let ctx = Context.extend Context.empty a_ty in
    let inl = Inl (Var 0) in
    let ty = TSum (a_ty, a_ty) in
    match Check.check ctx inl ty with
    | Ok c -> Credence.equal c Credence.one
    | Error _ -> false
  );

  (* Per Agda spec (Judgment.agda:81-83), variables ALWAYS have credence 1.
     Credences multiply at ELIMINATION (app, projection), not at variable lookup.
     This is the chain rule: P(A,B) = P(A|B) * P(B) - multiplication happens
     when we USE a term, not when we INTRODUCE it. *)

  test "var always returns credence 1 (t-var rule)" (
    let ctx = Context.extend Context.empty a_ty in
    match Check.infer ctx (Var 0) with
    | Ok (_, c) -> Credence.equal c Credence.one
    | Error _ -> false
  );

  test "nested var returns credence 1" (
    let ctx = Context.extend Context.empty a_ty in
    let ctx2 = Context.extend ctx a_ty in
    match Check.infer ctx2 (Var 0) with
    | Ok (_, c) -> Credence.equal c Credence.one
    | Error _ -> false
  );

  test "lookup outer var returns credence 1" (
    let ctx = Context.extend Context.empty a_ty in
    let ctx2 = Context.extend ctx a_ty in
    match Check.infer ctx2 (Var 1) with
    | Ok (_, c) -> Credence.equal c Credence.one
    | Error _ -> false
  );

  test "app multiplies credences (chain rule): 1 * 1 = 1" (
    let f_ty = TPi (a_ty, Subst.wk_ty a_ty) in
    let ctx = Context.extend Context.empty a_ty in
    let ctx2 = Context.extend ctx f_ty in
    match Check.infer ctx2 (App (Var 0, Var 1)) with
    | Ok (_, c) -> Credence.equal c Credence.one
    | Error _ -> false
  );

  Printf.printf "\nAll type checking tests passed!\n"
