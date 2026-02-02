(* Weak head normalization for type equality *)

open Syntax
open Subst

let rec whnf = function
  | App (f, a) ->
      (match whnf f with
       | Lam (_, body) -> whnf (subst_single_tm body a)
       | f' -> App (f', a))
  | Fst t ->
      (match whnf t with
       | Pair (a, _) -> whnf a
       | t' -> Fst t')
  | Snd t ->
      (match whnf t with
       | Pair (_, b) -> whnf b
       | t' -> Snd t')
  | Case (e, l, r) ->
      (match whnf e with
       | Inl a -> whnf (subst_single_tm l a)
       | Inr b -> whnf (subst_single_tm r b)
       | e' -> Case (e', l, r))
  | J (m, d, p) ->
      (match whnf p with
       | Refl -> whnf d
       | p' -> J (m, d, p'))
  | t -> t

let rec equal_tm t1 t2 =
  match whnf t1, whnf t2 with
  | Var i, Var j -> i = j
  | Lam (ty1, b1), Lam (ty2, b2) -> equal_ty ty1 ty2 && equal_tm b1 b2
  | App (f1, a1), App (f2, a2) -> equal_tm f1 f2 && equal_tm a1 a2
  | Pair (a1, b1), Pair (a2, b2) -> equal_tm a1 a2 && equal_tm b1 b2
  | Fst t1', Fst t2' -> equal_tm t1' t2'
  | Snd t1', Snd t2' -> equal_tm t1' t2'
  | Inl t1', Inl t2' -> equal_tm t1' t2'
  | Inr t1', Inr t2' -> equal_tm t1' t2'
  | Case (e1, l1, r1), Case (e2, l2, r2) ->
      equal_tm e1 e2 && equal_tm l1 l2 && equal_tm r1 r2
  | Refl, Refl -> true
  | J (m1, d1, p1), J (m2, d2, p2) ->
      equal_ty m1 m2 && equal_tm d1 d2 && equal_tm p1 p2
  | _, _ -> false

and equal_ty ty1 ty2 =
  match ty1, ty2 with
  | TBase i, TBase j -> i = j
  | TPi (a1, b1), TPi (a2, b2) -> equal_ty a1 a2 && equal_ty b1 b2
  | TSigma (a1, b1), TSigma (a2, b2) -> equal_ty a1 a2 && equal_ty b1 b2
  | TSum (a1, b1), TSum (a2, b2) -> equal_ty a1 a2 && equal_ty b1 b2
  | TId (a1, t1, u1), TId (a2, t2, u2) ->
      equal_ty a1 a2 && equal_tm t1 t2 && equal_tm u1 u2
  | _, _ -> false
