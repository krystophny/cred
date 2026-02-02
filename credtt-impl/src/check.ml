(* Bidirectional type checker with credence multiplication and stability tracking
   Key rules from agda/CredTT/Judgment.agda:
   - t-var: Variables at credence 1 (line 61-62)
   - t-app: Credences multiply (line 77-80)
   - t-pair: Credences multiply (line 84-87)
   - t-case: Scrutinee credence multiplies branch credence (line 111-115)
   - t-J: Identity elim multiplies credences (line 135-139)
   - t-weaken: Can lower credence if v <= c (line 65-68)

   Stability tracking (neighbourhood semantics):
   - Stable1: credence robustly near 1, inhabitation persists under degradation
   - Unstable0: credence fragile near 0, inhabitation collapses easily
   - Interior: credence strictly between extremes
   - Classical proof techniques become stability theorems *)

open Syntax
open Subst
open Context
open Eval

(* Extended result with stability tracking *)
type infer_result = {
  ty : ty;
  credence : Credence.t;
  stability : Neighbourhood.stability;
}

type result = (ty * Credence.t, Error.t) Result.t
type check_result = (Credence.t, Error.t) Result.t
type full_result = (infer_result, Error.t) Result.t

let ( let* ) = Result.bind

let infer (ctx : Context.t) (t : term) : result =
  let rec go ctx = function
    | Var i ->
        (match lookup ctx i with
         | Some ty -> Ok (ty, Credence.one)
         | None -> Error (Error.UnboundVariable i))

    | App (f, a) ->
        let* (f_ty, c_f) = go ctx f in
        (match f_ty with
         | TPi (a_ty, b_ty) ->
             let* c_a = check ctx a a_ty in
             let result_ty = subst_single_ty b_ty a in
             Ok (result_ty, Credence.mul c_f c_a)
         | ty -> Error (Error.NotAFunction ty))

    | Fst t ->
        let* (t_ty, c) = go ctx t in
        (match t_ty with
         | TSigma (a_ty, _) -> Ok (a_ty, c)
         | ty -> Error (Error.NotAPair ty))

    | Snd t ->
        let* (t_ty, c) = go ctx t in
        (match t_ty with
         | TSigma (_, b_ty) ->
             let result_ty = subst_single_ty b_ty (Fst t) in
             Ok (result_ty, c)
         | ty -> Error (Error.NotAPair ty))

    | Refl -> Error (Error.CannotInfer Refl)

    | Lam _ -> Error (Error.CannotInfer t)
    | Pair _ -> Error (Error.CannotInfer t)
    | Inl _ -> Error (Error.CannotInfer t)
    | Inr _ -> Error (Error.CannotInfer t)
    | Case _ -> Error (Error.CannotInfer t)
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
        let* c_a = check ctx a a_ty in
        let b_ty' = subst_single_ty b_ty a in
        let* c_b = check ctx b b_ty' in
        Ok (Credence.mul c_a c_b)

    | Inl a, TSum (a_ty, _) ->
        check ctx a a_ty

    | Inr b, TSum (_, b_ty) ->
        check ctx b b_ty

    (* Case elimination: both branches must have equal credence v, result is c*v
       Reference: Judgment.agda:111-115 (t-case rule) *)
    | Case (e, l, r), result_ty ->
        let* (e_ty, c_e) = go ctx e in
        (match e_ty with
         | TSum (a_ty, b_ty) ->
             let ctx_l = extend ctx a_ty in
             let ctx_r = extend ctx b_ty in
             let result_ty_wk = wk_ty result_ty in
             let* c_l = check ctx_l l result_ty_wk in
             let* c_r = check ctx_r r result_ty_wk in
             if Credence.equal (Credence.simplify c_l) (Credence.simplify c_r) then
               Ok (Credence.mul c_e c_l)
             else
               Error (Error.BranchCredenceMismatch (c_l, c_r))
         | ty -> Error (Error.NotASum ty))

    | Refl, TId (ty, a, b) ->
        if not (equal_tm a b) then
          Error (Error.IdEndpointsNotEqual (a, b))
        else
          check ctx a ty

    | J (m, d, p), expected_ty ->
        let* (p_ty, c_p) = go ctx p in
        (match p_ty with
         | TId (_, a, b) ->
             let d_ty = subst_single_ty (subst_single_ty m a) Refl in
             let* c_d = check ctx d d_ty in
             let result_ty = subst_single_ty (subst_single_ty m b) p in
             if not (equal_ty result_ty expected_ty) then
               Error (Error.TypeMismatch { expected = expected_ty; actual = result_ty })
             else
               Ok (Credence.mul c_p c_d)
         | ty -> Error (Error.NotAnIdentity ty))

    | _, _ ->
        let* (inferred, c) = go ctx t in
        if equal_ty inferred expected then Ok c
        else Error (Error.TypeMismatch { expected; actual = inferred })
  in
  go ctx t

let check ctx t expected =
  let rec go ctx = function
    | Var i ->
        (match lookup ctx i with
         | Some ty -> Ok (ty, Credence.one)
         | None -> Error (Error.UnboundVariable i))

    | App (f, a) ->
        let* (f_ty, c_f) = go ctx f in
        (match f_ty with
         | TPi (a_ty, b_ty) ->
             let* c_a = check_impl ctx a a_ty in
             let result_ty = subst_single_ty b_ty a in
             Ok (result_ty, Credence.mul c_f c_a)
         | ty -> Error (Error.NotAFunction ty))

    | Fst t ->
        let* (t_ty, c) = go ctx t in
        (match t_ty with
         | TSigma (a_ty, _) -> Ok (a_ty, c)
         | ty -> Error (Error.NotAPair ty))

    | Snd t ->
        let* (t_ty, c) = go ctx t in
        (match t_ty with
         | TSigma (_, b_ty) ->
             let result_ty = subst_single_ty b_ty (Fst t) in
             Ok (result_ty, c)
         | ty -> Error (Error.NotAPair ty))

    | Refl -> Error (Error.CannotInfer Refl)
    | Lam _ -> Error (Error.CannotInfer t)
    | Pair _ -> Error (Error.CannotInfer t)
    | Inl _ -> Error (Error.CannotInfer t)
    | Inr _ -> Error (Error.CannotInfer t)
    | Case _ -> Error (Error.CannotInfer t)
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
        let* c_a = check_impl ctx a a_ty in
        let b_ty' = subst_single_ty b_ty a in
        let* c_b = check_impl ctx b b_ty' in
        Ok (Credence.mul c_a c_b)

    | Inl a, TSum (a_ty, _) ->
        check_impl ctx a a_ty

    | Inr b, TSum (_, b_ty) ->
        check_impl ctx b b_ty

    (* Case elimination: both branches must have equal credence v, result is c*v
       Reference: Judgment.agda:111-115 (t-case rule) *)
    | Case (e, l, r), result_ty ->
        let* (e_ty, c_e) = go ctx e in
        (match e_ty with
         | TSum (a_ty, b_ty) ->
             let ctx_l = extend ctx a_ty in
             let ctx_r = extend ctx b_ty in
             let result_ty_wk = wk_ty result_ty in
             let* c_l = check_impl ctx_l l result_ty_wk in
             let* c_r = check_impl ctx_r r result_ty_wk in
             if Credence.equal (Credence.simplify c_l) (Credence.simplify c_r) then
               Ok (Credence.mul c_e c_l)
             else
               Error (Error.BranchCredenceMismatch (c_l, c_r))
         | ty -> Error (Error.NotASum ty))

    | Refl, TId (ty, a, b) ->
        if not (equal_tm a b) then
          Error (Error.IdEndpointsNotEqual (a, b))
        else
          check_impl ctx a ty

    | J (m, d, p), expected_ty ->
        let* (p_ty, c_p) = go ctx p in
        (match p_ty with
         | TId (_, a, b) ->
             let d_ty = subst_single_ty (subst_single_ty m a) Refl in
             let* c_d = check_impl ctx d d_ty in
             let result_ty = subst_single_ty (subst_single_ty m b) p in
             if not (equal_ty result_ty expected_ty) then
               Error (Error.TypeMismatch { expected = expected_ty; actual = result_ty })
             else
               Ok (Credence.mul c_p c_d)
         | ty -> Error (Error.NotAnIdentity ty))

    | _, _ ->
        let* (inferred, c) = go ctx t in
        if equal_ty inferred expected then Ok c
        else Error (Error.TypeMismatch { expected; actual = inferred })
  in
  check_impl ctx t expected

(* Check with credence constraint.
   Weakening rule (t-weaken): if we prove t : A @ actual, we can use it
   at any expected_credence where expected_credence <= actual.
   Higher actual credence can be weakened to lower expected credence. *)
let check_with_credence ctx t expected expected_credence =
  let* actual_credence = check ctx t expected in
  if Credence.leq expected_credence actual_credence then
    Ok actual_credence
  else
    Error (Error.CredenceNotLeq (expected_credence, actual_credence))

(* ============================================================
   STABILITY-AWARE INFERENCE
   ============================================================
   This is the core differentiator of CredTT over MLTT.
   Every judgment tracks not just credence, but stability class.
   ============================================================ *)

(* Infer type, credence, and stability *)
let infer_with_stability (ctx : Context.t) (t : term) : full_result =
  let rec go ctx = function
    | Var i ->
        (match lookup ctx i with
         | Some ty ->
             (* Variables have credence 1, which is Stable1 *)
             Ok { ty; credence = Credence.one; stability = Neighbourhood.Stable1 }
         | None -> Error (Error.UnboundVariable i))

    | App (f, a) ->
        let* f_res = go ctx f in
        (match f_res.ty with
         | TPi (a_ty, b_ty) ->
             let* c_a = check_impl ctx a a_ty in
             let result_ty = subst_single_ty b_ty a in
             let result_credence = Credence.mul f_res.credence c_a in
             (* Stability of application: stable * stable = stable *)
             let a_stability = Neighbourhood.classify c_a in
             let result_stability = Neighbourhood.stability_of_app f_res.stability a_stability in
             Ok { ty = result_ty; credence = result_credence; stability = result_stability }
         | ty -> Error (Error.NotAFunction ty))

    | Fst t ->
        let* t_res = go ctx t in
        (match t_res.ty with
         | TSigma (a_ty, _) ->
             (* Projection preserves stability *)
             Ok { ty = a_ty; credence = t_res.credence;
                  stability = Neighbourhood.stability_of_sigma_elim t_res.stability }
         | ty -> Error (Error.NotAPair ty))

    | Snd t ->
        let* t_res = go ctx t in
        (match t_res.ty with
         | TSigma (_, b_ty) ->
             let result_ty = subst_single_ty b_ty (Fst t) in
             (* Projection preserves stability *)
             Ok { ty = result_ty; credence = t_res.credence;
                  stability = Neighbourhood.stability_of_sigma_elim t_res.stability }
         | ty -> Error (Error.NotAPair ty))

    | Refl -> Error (Error.CannotInfer Refl)
    | Lam _ -> Error (Error.CannotInfer t)
    | Pair _ -> Error (Error.CannotInfer t)
    | Inl _ -> Error (Error.CannotInfer t)
    | Inr _ -> Error (Error.CannotInfer t)
    | Case _ -> Error (Error.CannotInfer t)
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
        let* c_a = check_impl ctx a a_ty in
        let b_ty' = subst_single_ty b_ty a in
        let* c_b = check_impl ctx b b_ty' in
        Ok (Credence.mul c_a c_b)

    | Inl a, TSum (a_ty, _) ->
        check_impl ctx a a_ty

    | Inr b, TSum (_, b_ty) ->
        check_impl ctx b b_ty

    | Case (e, l, r), result_ty ->
        let* e_res = go ctx e in
        (match e_res.ty with
         | TSum (a_ty, b_ty) ->
             let ctx_l = extend ctx a_ty in
             let ctx_r = extend ctx b_ty in
             let result_ty_wk = wk_ty result_ty in
             let* c_l = check_impl ctx_l l result_ty_wk in
             let* c_r = check_impl ctx_r r result_ty_wk in
             if Credence.equal (Credence.simplify c_l) (Credence.simplify c_r) then
               Ok (Credence.mul e_res.credence c_l)
             else
               Error (Error.BranchCredenceMismatch (c_l, c_r))
         | ty -> Error (Error.NotASum ty))

    | Refl, TId (ty, a, b) ->
        if not (equal_tm a b) then
          Error (Error.IdEndpointsNotEqual (a, b))
        else
          check_impl ctx a ty

    | J (m, d, p), expected_ty ->
        let* p_res = go ctx p in
        (match p_res.ty with
         | TId (_, a, b) ->
             let d_ty = subst_single_ty (subst_single_ty m a) Refl in
             let* c_d = check_impl ctx d d_ty in
             let result_ty = subst_single_ty (subst_single_ty m b) p in
             if not (equal_ty result_ty expected_ty) then
               Error (Error.TypeMismatch { expected = expected_ty; actual = result_ty })
             else
               Ok (Credence.mul p_res.credence c_d)
         | ty -> Error (Error.NotAnIdentity ty))

    | _, _ ->
        let* res = go ctx t in
        if equal_ty res.ty expected then Ok res.credence
        else Error (Error.TypeMismatch { expected; actual = res.ty })
  in
  go ctx t

(* Check stability assertion: verify term has expected stability *)
let check_stability ctx t expected_stability =
  let* res = infer_with_stability ctx t in
  if res.stability = expected_stability then
    Ok res
  else
    Error (Error.StabilityMismatch {
      expected = Neighbourhood.stability_to_string expected_stability;
      actual = Neighbourhood.stability_to_string res.stability
    })

(* Assert term is Stable1 (robust near credence 1) *)
let assert_stable ctx t =
  check_stability ctx t Neighbourhood.Stable1

(* Assert term is Unstable0 (fragile near credence 0) *)
let assert_unstable ctx t =
  check_stability ctx t Neighbourhood.Unstable0
