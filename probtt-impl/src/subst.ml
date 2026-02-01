(* De Bruijn substitution following agda/ProbTT/Substitution.agda *)

open Syntax

let rec rename_ty (r : int -> int) = function
  | TBase i -> TBase i
  | TPi (a, b) -> TPi (rename_ty r a, rename_ty (lift_ren r) b)
  | TSigma (a, b) -> TSigma (rename_ty r a, rename_ty (lift_ren r) b)
  | TSum (a, b) -> TSum (rename_ty r a, rename_ty r b)
  | TUnit -> TUnit
  | TId (a, t1, t2) -> TId (rename_ty r a, rename_tm r t1, rename_tm r t2)

and rename_tm (r : int -> int) = function
  | Var i -> Var (r i)
  | Lam (ty, body) -> Lam (rename_ty r ty, rename_tm (lift_ren r) body)
  | App (f, a) -> App (rename_tm r f, rename_tm r a)
  | Pair (a, b) -> Pair (rename_tm r a, rename_tm r b)
  | Fst t -> Fst (rename_tm r t)
  | Snd t -> Snd (rename_tm r t)
  | Inl t -> Inl (rename_tm r t)
  | Inr t -> Inr (rename_tm r t)
  | Case (e, l, r') -> Case (rename_tm r e, rename_tm (lift_ren r) l, rename_tm (lift_ren r) r')
  | Star -> Star
  | Refl -> Refl
  | J (m, d, p) -> J (rename_ty (lift_ren (lift_ren r)) m, rename_tm r d, rename_tm r p)

and lift_ren (r : int -> int) (i : int) : int =
  if i = 0 then 0 else r (i - 1) + 1

let wk_tm t = rename_tm (fun i -> i + 1) t
let wk_ty ty = rename_ty (fun i -> i + 1) ty

type sub = int -> term

let lift_sub (s : sub) (i : int) : term =
  if i = 0 then Var 0 else wk_tm (s (i - 1))

let rec subst_ty (s : sub) = function
  | TBase i -> TBase i
  | TPi (a, b) -> TPi (subst_ty s a, subst_ty (lift_sub s) b)
  | TSigma (a, b) -> TSigma (subst_ty s a, subst_ty (lift_sub s) b)
  | TSum (a, b) -> TSum (subst_ty s a, subst_ty s b)
  | TUnit -> TUnit
  | TId (a, t1, t2) -> TId (subst_ty s a, subst_tm s t1, subst_tm s t2)

and subst_tm (s : sub) = function
  | Var i -> s i
  | Lam (ty, body) -> Lam (subst_ty s ty, subst_tm (lift_sub s) body)
  | App (f, a) -> App (subst_tm s f, subst_tm s a)
  | Pair (a, b) -> Pair (subst_tm s a, subst_tm s b)
  | Fst t -> Fst (subst_tm s t)
  | Snd t -> Snd (subst_tm s t)
  | Inl t -> Inl (subst_tm s t)
  | Inr t -> Inr (subst_tm s t)
  | Case (e, l, r) -> Case (subst_tm s e, subst_tm (lift_sub s) l, subst_tm (lift_sub s) r)
  | Star -> Star
  | Refl -> Refl
  | J (m, d, p) -> J (subst_ty (lift_sub (lift_sub s)) m, subst_tm s d, subst_tm s p)

let single_sub (t : term) (i : int) : term =
  if i = 0 then t else Var (i - 1)

let subst_single_tm body t = subst_tm (single_sub t) body
let subst_single_ty ty t = subst_ty (single_sub t) ty
