(* CredTT Proof Checker

   Parses and checks proof files with credence tracking.
   Syntax is Agda-compatible.
*)

(* Proof constructs *)
type proof_decl =
  | Postulate of string * string * Credence.t    (* name, prop, credence *)
  | Derive of string * string * Credence.t * derivation
  | Contradict of string * string              (* two contradictory props *)
  | Negate of string * string                  (* conclusion from negated assumption *)
  (* Meta-theory constructs *)
  | Provable of string * string * Credence.t     (* Prov_c(phi) *)
  | Fixpoint of string * Credence.t              (* x where x = f(x) *)
  | Encode of string * string                  (* Goedel encoding *)

and derivation =
  | From of string * string   (* from prop, by justification *)
  | Direct                    (* direct/axiom *)

(* Proof state *)
type judgment = {
  name : string;
  prop : string;
  credence : Credence.t;
  status : status;
}

and status =
  | Assumed
  | Derived of string   (* from which judgment *)
  | Forced of Credence.t  (* forced to this credence by contradiction *)

type proof_state = {
  judgments : (string, judgment) Hashtbl.t;
  credence_eqs : (Credence.t * Credence.t) list;  (* c = v constraints *)
  provables : (string, string * Credence.t) Hashtbl.t;  (* name -> (prop, credence) *)
  fixpoints : (string, Credence.rational) Hashtbl.t;    (* variable -> solved value *)
  encodings : (string, string) Hashtbl.t;  (* name -> encoded prop *)
  infer_ctx : Credence.infer_ctx;  (* inference context for credence solving *)
}

let create () = {
  judgments = Hashtbl.create 16;
  credence_eqs = [];
  provables = Hashtbl.create 16;
  fixpoints = Hashtbl.create 16;
  encodings = Hashtbl.create 16;
  infer_ctx = Credence.create_infer_ctx ();
}

(* Check if credence needs inference (is an Infer variable) *)
let needs_inference = function
  | Credence.Infer _ -> true
  | _ -> false

(* Add a postulate *)
let add_postulate state name prop credence =
  (* If credence needs inference, generate fresh variable *)
  let actual_credence =
    if needs_inference credence then credence
    else credence
  in
  let j = { name; prop; credence = actual_credence; status = Assumed } in
  Hashtbl.replace state.judgments name j;
  Printf.printf "  postulate %s : %s [ %s ]\n" name prop (Credence.to_string actual_credence);
  Ok state

(* Add a derivation *)
let add_derivation state name prop credence deriv =
  match deriv with
  | From (from_name, justification) ->
    (match Hashtbl.find_opt state.judgments from_name with
     | None ->
       Error (Printf.sprintf "Unknown judgment: %s" from_name)
     | Some from_j ->
       (* Use inference to derive credence from source *)
       let derived_credence = Credence.infer_derivation_credence
         ~from_credence:from_j.credence ~step:justification in
       (* If declared credence differs, add constraint for inference *)
       let final_credence =
         if needs_inference credence then begin
           (* Infer from derivation *)
           Credence.add_constraint state.infer_ctx credence derived_credence;
           derived_credence
         end else if not (Credence.equal (Credence.simplify credence) (Credence.simplify derived_credence)) then begin
           Printf.printf "  WARNING: declared credence %s differs from derived %s\n"
             (Credence.to_string credence) (Credence.to_string derived_credence);
           (* Add constraint: declared = derived *)
           Credence.add_constraint state.infer_ctx credence derived_credence;
           derived_credence
         end else
           derived_credence
       in
       let j = { name; prop; credence = final_credence; status = Derived from_name } in
       Hashtbl.replace state.judgments name j;
       Printf.printf "  %s : %s [ %s ]  (from %s by %s)\n"
         name prop (Credence.to_string final_credence) from_name justification;
       Ok state)
  | Direct ->
    let j = { name; prop; credence; status = Assumed } in
    Hashtbl.replace state.judgments name j;
    Printf.printf "  %s : %s [ %s ]  (direct)\n" name prop (Credence.to_string credence);
    Ok state

(* Process a contradiction *)
let add_contradiction state p q =
  match Hashtbl.find_opt state.judgments p,
        Hashtbl.find_opt state.judgments q with
  | Some jp, Some jq ->
    Printf.printf "\n  CONTRADICTION: %s and %s\n" p q;
    Printf.printf "     %s [ %s ]\n" p (Credence.to_string jp.credence);
    Printf.printf "     %s [ %s ]\n" q (Credence.to_string jq.credence);
    (* Find the credence variable(s) to force to 0 *)
    (* If both have same credence -> that credence = 0 *)
    (* If one is constant 1 and other is variable c -> c = 0 *)
    let cp = Credence.simplify jp.credence in
    let cq = Credence.simplify jq.credence in
    let (forced_credence, forced_str) =
      if Credence.equal cp cq then
        (cp, Credence.to_string cp)
      else if Credence.equal cp Credence.one then
        (cq, Credence.to_string cq)
      else if Credence.equal cq Credence.one then
        (cp, Credence.to_string cp)
      else
        (* Both are different variables - force both via product *)
        (Credence.mul cp cq, Printf.sprintf "%s * %s" (Credence.to_string cp) (Credence.to_string cq))
    in
    Printf.printf "     -> %s = 0\n" forced_str;
    (* Add constraint to inference context *)
    Credence.add_zero_constraint state.infer_ctx forced_credence;
    let state = { state with credence_eqs = (forced_credence, Credence.zero) :: state.credence_eqs } in
    (* Update judgments to show forced credence *)
    Hashtbl.iter (fun name j ->
      let jc = Credence.simplify j.credence in
      if Credence.equal jc (Credence.simplify forced_credence) ||
         Credence.equal jc (Credence.simplify cp) ||
         Credence.equal jc (Credence.simplify cq) then
        Hashtbl.replace state.judgments name { j with status = Forced Credence.zero }
    ) state.judgments;
    Ok state
  | None, _ -> Error (Printf.sprintf "Unknown judgment: %s" p)
  | _, None -> Error (Printf.sprintf "Unknown judgment: %s" q)

(* Compute negated credence *)
let negate_credence state c =
  let dominated_by_zero = List.exists (fun (c', v) ->
    Credence.equal (Credence.simplify c') (Credence.simplify c) &&
    Credence.equal v Credence.zero
  ) state.credence_eqs in
  if dominated_by_zero then Credence.one
  else Credence.neg c

(* Add a negation/conclusion *)
let add_negation state name from_name =
  match Hashtbl.find_opt state.judgments from_name with
  | None -> Error (Printf.sprintf "Unknown judgment: %s" from_name)
  | Some from_j ->
    let neg_credence = negate_credence state from_j.credence in
    let j = { name; prop = "not " ^ from_j.prop; credence = neg_credence; status = Derived from_name } in
    Hashtbl.replace state.judgments name j;
    Printf.printf "\n  THEREFORE %s : not %s [ %s ]\n" name from_j.prop (Credence.to_string neg_credence);
    Ok state

(* Add a provability assertion: Prov_c(phi) *)
let add_provable state name prop credence =
  Hashtbl.replace state.provables name (prop, credence);
  Printf.printf "  provable %s : Prov(%s) [ %s ]\n" name prop (Credence.to_string credence);
  Ok state

(* Add and solve a fixpoint: x = f(x)
   Currently handles c = neg c -> c = 1/2 *)
let add_fixpoint state name credence_expr =
  let simplified = Credence.simplify credence_expr in
  let result = match simplified with
    | Credence.Neg (Credence.Var v) when v = name ->
        (* c = neg c -> c = 1/2 (negation fixpoint) *)
        let half = Credence.solve_negation_fixpoint () in
        Hashtbl.replace state.fixpoints name half;
        Printf.printf "\n  FIXPOINT: %s = neg %s\n" name name;
        Printf.printf "     Solved: %s = %s\n" name (Credence.rat_to_string half);
        Some half
    | Credence.Neg (Credence.Infer n) ->
        (* Inference variable fixpoint: ?n = neg ?n -> ?n = 1/2 *)
        let half = Credence.solve_negation_fixpoint () in
        Hashtbl.replace state.fixpoints name half;
        Printf.printf "\n  FIXPOINT: %s = neg ?%d\n" name n;
        Printf.printf "     Solved: %s = %s\n" name (Credence.rat_to_string half);
        (* Add to inference context *)
        state.infer_ctx.fixpoints <- (n, fun x -> Credence.Neg x) :: state.infer_ctx.fixpoints;
        Some half
    | Credence.Mul (Credence.Var v1, Credence.Var v2) when v1 = name && v2 = name ->
        (* c = c*c -> c = 0 or c = 1 (idempotent) *)
        Printf.printf "\n  FIXPOINT: %s = %s * %s\n" name name name;
        Printf.printf "     Solutions: 0 or 1 (choosing 1)\n";
        let one = Credence.rat_one in
        Hashtbl.replace state.fixpoints name one;
        Some one
    | Credence.Var v when v = name ->
        (* c = c (trivial, any value works) *)
        Printf.printf "\n  FIXPOINT: %s = %s (trivial)\n" name name;
        None
    | _ ->
        Printf.printf "\n  FIXPOINT: %s = %s (unknown form)\n" name (Credence.to_string simplified);
        None
  in
  match result with
  | Some _ -> Ok state
  | None -> Ok state

(* Add an encoding *)
let add_encoding state name prop =
  Hashtbl.replace state.encodings name prop;
  Printf.printf "  encode %s = [%s]\n" name prop;
  Ok state

(* Get the solved credence for a variable if available *)
let get_solved_credence state var_name =
  Hashtbl.find_opt state.fixpoints var_name

(* Process a single declaration *)
let process_decl state = function
  | Postulate (name, prop, credence) -> add_postulate state name prop credence
  | Derive (name, prop, credence, deriv) -> add_derivation state name prop credence deriv
  | Contradict (p, q) -> add_contradiction state p q
  | Negate (name, from_name) -> add_negation state name from_name
  | Provable (name, prop, credence) -> add_provable state name prop credence
  | Fixpoint (name, credence) -> add_fixpoint state name credence
  | Encode (name, prop) -> add_encoding state name prop

(* Run a proof *)
let check_proof decls =
  Printf.printf "\n==============================================================\n";
  Printf.printf "  CredTT Proof Checker\n";
  Printf.printf "==============================================================\n\n";

  Credence.reset_infer ();  (* Reset inference counter for fresh run *)
  let state = create () in
  let rec go state = function
    | [] -> Ok state
    | d :: ds ->
      match process_decl state d with
      | Ok state' -> go state' ds
      | Error e -> Error e
  in
  match go state decls with
  | Ok final_state ->
    (* Solve accumulated inference constraints *)
    (match Credence.solve_inference final_state.infer_ctx with
     | Ok subst ->
       Printf.printf "\n==============================================================\n";
       Printf.printf "  Proof checked successfully\n";
       (* Print inferred credences if any *)
       if subst <> [] then begin
         Printf.printf "\n  Inferred credences:\n";
         List.iter (fun (n, c) ->
           Printf.printf "    ?%d = %s\n" n (Credence.to_string c)
         ) subst
       end;
       (* Print solved fixpoints *)
       if Hashtbl.length final_state.fixpoints > 0 then begin
         Printf.printf "\n  Solved fixpoints:\n";
         Hashtbl.iter (fun name value ->
           Printf.printf "    %s = %s\n" name (Credence.rat_to_string value)
         ) final_state.fixpoints
       end;
       Printf.printf "==============================================================\n\n";
       Ok final_state
     | Error msg ->
       Printf.printf "\n  Inference error: %s\n\n" msg;
       Error msg)
  | Error e ->
    Printf.printf "\n  Error: %s\n\n" e;
    Error e

(* === sqrt2 proof as data === *)
let sqrt2_proof_decls =
  let c = Credence.var "c" in
  [
    Postulate ("sqrt2_rational", "sqrt2_is_rational", c);
    Postulate ("gcd_is_1", "gcd(p,q)=1", c);
    Derive ("p_even", "p_is_even", c, From ("sqrt2_rational", "algebra"));
    Derive ("q_even", "q_is_even", c, From ("p_even", "substitution"));
    Derive ("gcd_geq_2", "gcd(p,q)>=2", c, From ("q_even", "both_even"));
    Contradict ("gcd_is_1", "gcd_geq_2");
    Negate ("sqrt2_irrational", "sqrt2_rational");
  ]

let run_sqrt2_proof () =
  Printf.printf "
+==============================================================+
|  sqrt2 Irrationality Proof                                   |
|                                                              |
|  Structure:                                                  |
|  1. Assume sqrt2 = p/q in lowest terms, at credence c        |
|  2. Derive p even, q even (credence preserved)               |
|  3. Contradiction: gcd=1 AND gcd>=2                          |
|  4. Therefore c = 0, so not(sqrt2 rational) has credence 1   |
+==============================================================+
";
  check_proof sqrt2_proof_decls
