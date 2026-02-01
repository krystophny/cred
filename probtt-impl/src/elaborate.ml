(* Elaboration from Agda-style surface syntax to core AST *)

open Raw

module StringMap = Map.Make(String)

type env = {
  vars : int StringMap.t;
  depth : int;
  sigs : (ty * weight option) StringMap.t;
}

let empty_env = {
  vars = StringMap.empty;
  depth = 0;
  sigs = StringMap.empty;
}

let extend_var env name =
  let vars = StringMap.map (fun i -> i + 1) env.vars in
  let vars = StringMap.add name 0 vars in
  { env with vars; depth = env.depth + 1 }

let lookup_var env name =
  try Some (StringMap.find name env.vars)
  with Not_found -> None

let add_sig env name ty weight =
  { env with sigs = StringMap.add name (ty, weight) env.sigs }

let lookup_sig env name =
  try Some (StringMap.find name env.sigs)
  with Not_found -> None

(* Convert raw weight to core Weight.t *)
let rec elab_weight = function
  | WZero -> Weight.zero
  | WOne -> Weight.one
  | WMul (a, b) -> Weight.mul (elab_weight a) (elab_weight b)
  | WNeg w -> Weight.neg (elab_weight w)
  | WVar x -> Weight.var x
  | WRat (n, d) -> Weight.of_rational { Weight.num = n; Weight.den = d }


let rec elab_ty env = function
  | TyVar "_" -> Syntax.TBase 0
  | TyVar name ->
      (match lookup_var env name with
       | Some _ -> Syntax.TBase 0
       | None -> Syntax.TBase 0)
  | TyApp (f, a) ->
      let _ = elab_ty env f in
      let _ = elab_ty env a in
      Syntax.TBase 0
  | TyArrow (a, b) ->
      let a' = elab_ty env a in
      let env' = extend_var env "_" in
      let b' = elab_ty env' b in
      Syntax.TPi (a', b')
  | TyPi (name, _implicit, a, b) ->
      let a' = elab_ty env a in
      let env' = extend_var env name in
      let b' = elab_ty env' b in
      Syntax.TPi (a', b')
  | TySigma (name, a, b) ->
      let a' = elab_ty env a in
      let env' = extend_var env name in
      let b' = elab_ty env' b in
      Syntax.TSigma (a', b')
  | TySum (a, b) ->
      Syntax.TSum (elab_ty env a, elab_ty env b)
  | TyId (a, t1, t2) ->
      Syntax.TId (elab_ty env a, elab_term env t1, elab_term env t2)
  | TySet _ -> Syntax.TBase 0

and elab_term env = function
  | TVar name ->
      (match lookup_var env name with
       | Some i -> Syntax.Var i
       | None -> Syntax.Var 0)
  | TApp (TVar "fst", a) ->
      Syntax.Fst (elab_term env a)
  | TApp (TVar "snd", a) ->
      Syntax.Snd (elab_term env a)
  | TApp (TVar "inl", a) ->
      Syntax.Inl (elab_term env a)
  | TApp (TVar "inr", a) ->
      Syntax.Inr (elab_term env a)
  | TApp (f, a) ->
      Syntax.App (elab_term env f, elab_term env a)
  | TLam (name, body) ->
      let env' = extend_var env name in
      Syntax.Lam (Syntax.TBase 0, elab_term env' body)
  | TLamTy (name, ty, body) ->
      let ty' = elab_ty env ty in
      let env' = extend_var env name in
      Syntax.Lam (ty', elab_term env' body)
  | TPair (a, b) ->
      Syntax.Pair (elab_term env a, elab_term env b)
  | TFst t -> Syntax.Fst (elab_term env t)
  | TSnd t -> Syntax.Snd (elab_term env t)
  | TInl t -> Syntax.Inl (elab_term env t)
  | TInr t -> Syntax.Inr (elab_term env t)
  | TCase (e, (x, l), (y, r)) ->
      let e' = elab_term env e in
      let env_l = extend_var env x in
      let env_r = extend_var env y in
      Syntax.Case (e', elab_term env_l l, elab_term env_r r)
  | TRefl -> Syntax.Refl
  | TJ (m, d, p) ->
      Syntax.J (elab_ty env m, elab_term env d, elab_term env p)
  | TAnn (t, _ty) -> elab_term env t
  | THole -> Syntax.Var 0  (* placeholder - holes are not properly supported *)
  | TLet (name, _ty, t, body) ->
      let t' = elab_term env t in
      let env' = extend_var env name in
      Syntax.App (Syntax.Lam (Syntax.TBase 0, elab_term env' body), t')
  | TWhere (body, _decls) ->
      elab_term env body

(* Extract argument types with implicit/explicit info *)
type arg_info = { arg_ty: ty; arg_name: name; is_implicit: bool }

let rec extract_arg_info = function
  | TyArrow (a, b) ->
      { arg_ty = a; arg_name = "_"; is_implicit = false } :: extract_arg_info b
  | TyPi (name, impl, a, b) ->
      let is_implicit = (impl = Implicit) in
      { arg_ty = a; arg_name = name; is_implicit } :: extract_arg_info b
  | _ -> []

(* For backwards compatibility *)
let extract_arg_types ty =
  List.map (fun info -> info.arg_ty) (extract_arg_info ty)

let wrap_lambdas_with_types env pats arg_infos body =
  let rec go env pats infos =
    match pats, infos with
    | [], [] -> elab_term env body
    (* No more patterns but still have implicit args - insert lambdas *)
    | [], { arg_ty; arg_name; is_implicit = true } :: rest_infos ->
        let ty' = elab_ty env arg_ty in
        let env' = extend_var env arg_name in
        Syntax.Lam (ty', go env' [] rest_infos)
    (* No more patterns but explicit args remain - error case, insert anyway *)
    | [], { arg_ty; arg_name; is_implicit = false } :: rest_infos ->
        let ty' = elab_ty env arg_ty in
        let env' = extend_var env arg_name in
        Syntax.Lam (ty', go env' [] rest_infos)
    (* Implicit arg without pattern - insert lambda and continue *)
    | pats, { arg_ty; arg_name; is_implicit = true } :: rest_infos ->
        let ty' = elab_ty env arg_ty in
        let env' = extend_var env arg_name in
        Syntax.Lam (ty', go env' pats rest_infos)
    (* Explicit pattern with type info *)
    | PVar name :: rest_pats, { arg_ty; is_implicit = false; _ } :: rest_infos ->
        let ty' = elab_ty env arg_ty in
        let env' = extend_var env name in
        Syntax.Lam (ty', go env' rest_pats rest_infos)
    | PWild :: rest_pats, { arg_ty; is_implicit = false; _ } :: rest_infos ->
        let ty' = elab_ty env arg_ty in
        let env' = extend_var env "_" in
        Syntax.Lam (ty', go env' rest_pats rest_infos)
    | _ :: rest_pats, { arg_ty; is_implicit = false; _ } :: rest_infos ->
        let ty' = elab_ty env arg_ty in
        let env' = extend_var env "_" in
        Syntax.Lam (ty', go env' rest_pats rest_infos)
    (* Pattern without type info - use placeholder type *)
    | pat :: rest_pats, [] ->
        let env' = match pat with
          | PVar name -> extend_var env name
          | _ -> extend_var env "_"
        in
        Syntax.Lam (Syntax.TBase 0, go env' rest_pats [])
  in
  go env pats arg_infos

type elab_decl = {
  name : string;
  ty : Syntax.ty;
  term : Syntax.term;
  weight : Weight.t;
}

let process_decls env decls =
  let rec collect_sigs env = function
    | [] -> env
    | DSig (name, ty, w) :: rest ->
        collect_sigs (add_sig env name ty w) rest
    | _ :: rest -> collect_sigs env rest
  in
  let env = collect_sigs env decls in

  let rec process env acc = function
    | [] -> List.rev acc
    | DSig _ :: rest -> process env acc rest
    | DDef (name, pats, body) :: rest ->
        let (ty, arg_infos, weight) = match lookup_sig env name with
          | Some (t, w) ->
              let weight = match w with
                | Some raw_w -> elab_weight raw_w
                | None -> Weight.one
              in
              (elab_ty env t, extract_arg_info t, weight)
          | None -> (Syntax.TBase 0, [], Weight.one)
        in
        let term = wrap_lambdas_with_types env pats arg_infos body in
        let decl = { name; ty; term; weight } in
        process env (decl :: acc) rest
    | DModule (_, inner) :: rest ->
        let inner_decls = process env [] inner in
        process env (inner_decls @ acc) rest
    | DData _ :: rest -> process env acc rest
    | DRecord _ :: rest -> process env acc rest
    | DOpen _ :: rest -> process env acc rest
    | DImport _ :: rest -> process env acc rest
    | DInfix _ :: rest -> process env acc rest
    | DComment _ :: rest -> process env acc rest
    (* Skip proof declarations in normal elaboration *)
    | DPostulate _ :: rest -> process env acc rest
    | DDerive _ :: rest -> process env acc rest
    | DContradict _ :: rest -> process env acc rest
    | DConclude _ :: rest -> process env acc rest
    | DProvable _ :: rest -> process env acc rest
    | DFixpoint _ :: rest -> process env acc rest
    | DEncode _ :: rest -> process env acc rest
  in
  process env [] decls

let elab_program decls =
  let results = process_decls empty_env decls in
  List.map (fun d -> (d.name, d.ty, d.term, d.weight)) results

let elab_decl _env decl =
  match decl with
  | DSig (name, ty, w) ->
      let ty' = elab_ty empty_env ty in
      let weight = match w with
        | Some raw_w -> elab_weight raw_w
        | None -> Weight.one
      in
      (name, ty', Syntax.Refl, weight)  (* placeholder term *)
  | DDef (name, pats, body) ->
      let term = wrap_lambdas_with_types empty_env pats [] body in
      (name, Syntax.TBase 0, term, Weight.one)
  | _ -> ("", Syntax.TBase 0, Syntax.Refl, Weight.one)  (* placeholder term *)

(* Extract proof declarations from a program *)
let extract_proof_decls decls =
  let rec go acc = function
    | [] -> List.rev acc
    | DPostulate (name, prop, w) :: rest ->
        let proof_decl = Proof.Postulate (name, prop, elab_weight w) in
        go (proof_decl :: acc) rest
    | DDerive (name, prop, w, from_name, by_name) :: rest ->
        let proof_decl = Proof.Derive (name, prop, elab_weight w,
                                       Proof.From (from_name, by_name)) in
        go (proof_decl :: acc) rest
    | DContradict (p, q) :: rest ->
        go (Proof.Contradict (p, q) :: acc) rest
    | DConclude (name, from_name) :: rest ->
        go (Proof.Negate (name, from_name) :: acc) rest
    | DProvable (name, prop, w) :: rest ->
        let proof_decl = Proof.Provable (name, prop, elab_weight w) in
        go (proof_decl :: acc) rest
    | DFixpoint (name, w) :: rest ->
        let proof_decl = Proof.Fixpoint (name, elab_weight w) in
        go (proof_decl :: acc) rest
    | DEncode (name, prop) :: rest ->
        let proof_decl = Proof.Encode (name, prop) in
        go (proof_decl :: acc) rest
    | _ :: rest -> go acc rest
  in
  go [] decls

(* Check if a program contains proof declarations *)
let has_proof_decls decls =
  List.exists (function
    | DPostulate _ | DDerive _ | DContradict _ | DConclude _
    | DProvable _ | DFixpoint _ | DEncode _ -> true
    | _ -> false
  ) decls
