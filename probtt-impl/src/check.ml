(* Bidirectional type checker with weight multiplication
   Key rules from agda/ProbTT/Judgment.agda:
   - t-var: Variables at weight 1 (line 61-62)
   - t-app: Weights multiply (line 77-80)
   - t-pair: Weights multiply (line 84-87)
   - t-case: Scrutinee weight multiplies branch weight (line 111-115)
   - t-J: Identity elim multiplies weights (line 135-139)
   - t-weaken: Can lower weight if v <= w (line 65-68) *)

open Syntax
open Subst
open Context
open Eval

type result = (ty * Weight.t, Error.t) Result.t
type check_result = (Weight.t, Error.t) Result.t

let ( let* ) = Result.bind

let infer (ctx : Context.t) (t : term) : result =
  let rec go ctx = function
    | Var i ->
        (match lookup ctx i with
         | Some ty -> Ok (ty, Weight.one)
         | None -> Error (Error.UnboundVariable i))

    | App (f, a) ->
        let* (f_ty, w_f) = go ctx f in
        (match f_ty with
         | TPi (a_ty, b_ty) ->
             let* w_a = check ctx a a_ty in
             let result_ty = subst_single_ty b_ty a in
             Ok (result_ty, Weight.mul w_f w_a)
         | ty -> Error (Error.NotAFunction ty))

    | Fst t ->
        let* (t_ty, w) = go ctx t in
        (match t_ty with
         | TSigma (a_ty, _) -> Ok (a_ty, w)
         | ty -> Error (Error.NotAPair ty))

    | Snd t ->
        let* (t_ty, w) = go ctx t in
        (match t_ty with
         | TSigma (_, b_ty) ->
             let result_ty = subst_single_ty b_ty (Fst t) in
             Ok (result_ty, w)
         | ty -> Error (Error.NotAPair ty))

    | Star -> Ok (TUnit, Weight.one)

    | Refl -> Error (Error.CannotInfer Refl)

    | Lam _ -> Error (Error.CannotInfer t)
    | Pair _ -> Error (Error.CannotInfer t)
    | Inl _ -> Error (Error.CannotInfer t)
    | Inr _ -> Error (Error.CannotInfer t)
    | Case _ -> Error (Error.CannotInfer t)
    | Abort _ -> Error (Error.CannotInfer t)
    | J _ -> Error (Error.CannotInfer t)

  and check ctx t expected : check_result =
    match t, expected with
    | Lam (a_ty, body), TPi (a_ty', b_ty) ->
        if not (equal_ty a_ty a_ty') then
          Error (Error.TypeMismatch { expected = a_ty'; actual = a_ty })
        else
          let ctx' = extend ctx a_ty in
          check ctx' body b_ty

    | Pair (a, b), TSigma (a_ty, b_ty) ->
        let* w_a = check ctx a a_ty in
        let b_ty' = subst_single_ty b_ty a in
        let* w_b = check ctx b b_ty' in
        Ok (Weight.mul w_a w_b)

    | Inl a, TSum (a_ty, _) ->
        check ctx a a_ty

    | Inr b, TSum (_, b_ty) ->
        check ctx b b_ty

    (* Case elimination: both branches must have equal weight v, result is w·v
       Reference: Judgment.agda:111-115 (t-case rule) *)
    | Case (e, l, r), result_ty ->
        let* (e_ty, w_e) = go ctx e in
        (match e_ty with
         | TSum (a_ty, b_ty) ->
             let ctx_l = extend ctx a_ty in
             let ctx_r = extend ctx b_ty in
             let result_ty_wk = wk_ty result_ty in
             let* w_l = check ctx_l l result_ty_wk in
             let* w_r = check ctx_r r result_ty_wk in
             if Weight.equal (Weight.simplify w_l) (Weight.simplify w_r) then
               Ok (Weight.mul w_e w_l)
             else
               Error (Error.BranchWeightMismatch (w_l, w_r))
         | ty -> Error (Error.NotASum ty))

    | Star, TUnit -> Ok Weight.one

    | Abort (_, e), _ ->
        let* w = check ctx e TEmpty in
        Ok w

    | Refl, TId (ty, a, b) ->
        if not (equal_tm a b) then
          Error (Error.IdEndpointsNotEqual (a, b))
        else
          check ctx a ty

    | J (m, d, p), expected_ty ->
        let* (p_ty, w_p) = go ctx p in
        (match p_ty with
         | TId (_, a, b) ->
             let d_ty = subst_single_ty (subst_single_ty m a) Refl in
             let* w_d = check ctx d d_ty in
             let result_ty = subst_single_ty (subst_single_ty m b) p in
             if not (equal_ty result_ty expected_ty) then
               Error (Error.TypeMismatch { expected = expected_ty; actual = result_ty })
             else
               Ok (Weight.mul w_p w_d)
         | ty -> Error (Error.NotAnIdentity ty))

    | _, _ ->
        let* (inferred, w) = go ctx t in
        if equal_ty inferred expected then Ok w
        else Error (Error.TypeMismatch { expected; actual = inferred })
  in
  go ctx t

let check ctx t expected =
  let rec go ctx = function
    | Var i ->
        (match lookup ctx i with
         | Some ty -> Ok (ty, Weight.one)
         | None -> Error (Error.UnboundVariable i))

    | App (f, a) ->
        let* (f_ty, w_f) = go ctx f in
        (match f_ty with
         | TPi (a_ty, b_ty) ->
             let* w_a = check_impl ctx a a_ty in
             let result_ty = subst_single_ty b_ty a in
             Ok (result_ty, Weight.mul w_f w_a)
         | ty -> Error (Error.NotAFunction ty))

    | Fst t ->
        let* (t_ty, w) = go ctx t in
        (match t_ty with
         | TSigma (a_ty, _) -> Ok (a_ty, w)
         | ty -> Error (Error.NotAPair ty))

    | Snd t ->
        let* (t_ty, w) = go ctx t in
        (match t_ty with
         | TSigma (_, b_ty) ->
             let result_ty = subst_single_ty b_ty (Fst t) in
             Ok (result_ty, w)
         | ty -> Error (Error.NotAPair ty))

    | Star -> Ok (TUnit, Weight.one)

    | Refl -> Error (Error.CannotInfer Refl)
    | Lam _ -> Error (Error.CannotInfer t)
    | Pair _ -> Error (Error.CannotInfer t)
    | Inl _ -> Error (Error.CannotInfer t)
    | Inr _ -> Error (Error.CannotInfer t)
    | Case _ -> Error (Error.CannotInfer t)
    | Abort _ -> Error (Error.CannotInfer t)
    | J _ -> Error (Error.CannotInfer t)

  and check_impl ctx t expected : check_result =
    match t, expected with
    | Lam (a_ty, body), TPi (a_ty', b_ty) ->
        if not (equal_ty a_ty a_ty') then
          Error (Error.TypeMismatch { expected = a_ty'; actual = a_ty })
        else
          let ctx' = extend ctx a_ty in
          check_impl ctx' body b_ty

    | Pair (a, b), TSigma (a_ty, b_ty) ->
        let* w_a = check_impl ctx a a_ty in
        let b_ty' = subst_single_ty b_ty a in
        let* w_b = check_impl ctx b b_ty' in
        Ok (Weight.mul w_a w_b)

    | Inl a, TSum (a_ty, _) ->
        check_impl ctx a a_ty

    | Inr b, TSum (_, b_ty) ->
        check_impl ctx b b_ty

    (* Case elimination: both branches must have equal weight v, result is w·v
       Reference: Judgment.agda:111-115 (t-case rule) *)
    | Case (e, l, r), result_ty ->
        let* (e_ty, w_e) = go ctx e in
        (match e_ty with
         | TSum (a_ty, b_ty) ->
             let ctx_l = extend ctx a_ty in
             let ctx_r = extend ctx b_ty in
             let result_ty_wk = wk_ty result_ty in
             let* w_l = check_impl ctx_l l result_ty_wk in
             let* w_r = check_impl ctx_r r result_ty_wk in
             if Weight.equal (Weight.simplify w_l) (Weight.simplify w_r) then
               Ok (Weight.mul w_e w_l)
             else
               Error (Error.BranchWeightMismatch (w_l, w_r))
         | ty -> Error (Error.NotASum ty))

    | Star, TUnit -> Ok Weight.one

    | Abort (_, e), _ ->
        check_impl ctx e TEmpty

    | Refl, TId (ty, a, b) ->
        if not (equal_tm a b) then
          Error (Error.IdEndpointsNotEqual (a, b))
        else
          check_impl ctx a ty

    | J (m, d, p), expected_ty ->
        let* (p_ty, w_p) = go ctx p in
        (match p_ty with
         | TId (_, a, b) ->
             let d_ty = subst_single_ty (subst_single_ty m a) Refl in
             let* w_d = check_impl ctx d d_ty in
             let result_ty = subst_single_ty (subst_single_ty m b) p in
             if not (equal_ty result_ty expected_ty) then
               Error (Error.TypeMismatch { expected = expected_ty; actual = result_ty })
             else
               Ok (Weight.mul w_p w_d)
         | ty -> Error (Error.NotAnIdentity ty))

    | _, _ ->
        let* (inferred, w) = go ctx t in
        if equal_ty inferred expected then Ok w
        else Error (Error.TypeMismatch { expected; actual = inferred })
  in
  check_impl ctx t expected

(* Check with weight constraint.
   Weakening rule (t-weaken): if we prove t : A @ actual, we can use it
   at any expected_weight where expected_weight ≤ actual.
   Higher actual weight can be weakened to lower expected weight. *)
let check_with_weight ctx t expected expected_weight =
  let* actual_weight = check ctx t expected in
  if Weight.leq expected_weight actual_weight then
    Ok actual_weight
  else
    Error (Error.WeightNotLeq (expected_weight, actual_weight))
