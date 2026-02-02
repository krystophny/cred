(* ProbTT Proof Checker

   Parses and checks proof files with weight tracking.
   Syntax is Agda-compatible.
*)

(* Proof constructs *)
type proof_decl =
  | Postulate of string * string * Weight.t    (* name, prop, weight *)
  | Derive of string * string * Weight.t * derivation
  | Contradict of string * string              (* two contradictory props *)
  | Negate of string * string                  (* conclusion from negated assumption *)
  (* Meta-theory constructs *)
  | Provable of string * string * Weight.t     (* Prov_w(φ) *)
  | Fixpoint of string * Weight.t              (* x where x = f(x) *)
  | Encode of string * string                  (* ⌈φ⌉ encoding *)

and derivation =
  | From of string * string   (* from prop, by justification *)
  | Direct                    (* direct/axiom *)

(* Proof state *)
type judgment = {
  name : string;
  prop : string;
  weight : Weight.t;
  status : status;
}

and status =
  | Assumed
  | Derived of string   (* from which judgment *)
  | Forced of Weight.t  (* forced to this weight by contradiction *)

type proof_state = {
  judgments : (string, judgment) Hashtbl.t;
  weight_eqs : (Weight.t * Weight.t) list;  (* w = v constraints *)
  provables : (string, string * Weight.t) Hashtbl.t;  (* name -> (prop, weight) *)
  fixpoints : (string, Weight.rational) Hashtbl.t;    (* variable -> solved value *)
  encodings : (string, string) Hashtbl.t;  (* name -> encoded prop *)
  infer_ctx : Weight.infer_ctx;  (* inference context for weight solving *)
}

let create () = {
  judgments = Hashtbl.create 16;
  weight_eqs = [];
  provables = Hashtbl.create 16;
  fixpoints = Hashtbl.create 16;
  encodings = Hashtbl.create 16;
  infer_ctx = Weight.create_infer_ctx ();
}

(* Check if weight needs inference (is an Infer variable) *)
let needs_inference = function
  | Weight.Infer _ -> true
  | _ -> false

(* Add a postulate *)
let add_postulate state name prop weight =
  (* If weight needs inference, generate fresh variable *)
  let actual_weight =
    if needs_inference weight then weight
    else weight
  in
  let j = { name; prop; weight = actual_weight; status = Assumed } in
  Hashtbl.replace state.judgments name j;
  Printf.printf "  postulate %s : %s 〔 %s 〕\n" name prop (Weight.to_string actual_weight);
  Ok state

(* Add a derivation *)
let add_derivation state name prop weight deriv =
  match deriv with
  | From (from_name, justification) ->
    (match Hashtbl.find_opt state.judgments from_name with
     | None ->
       Error (Printf.sprintf "Unknown judgment: %s" from_name)
     | Some from_j ->
       (* Use inference to derive weight from source *)
       let derived_weight = Weight.infer_derivation_weight
         ~from_weight:from_j.weight ~step:justification in
       (* If declared weight differs, add constraint for inference *)
       let final_weight =
         if needs_inference weight then begin
           (* Infer from derivation *)
           Weight.add_constraint state.infer_ctx weight derived_weight;
           derived_weight
         end else if not (Weight.equal (Weight.simplify weight) (Weight.simplify derived_weight)) then begin
           Printf.printf "  WARNING: declared weight %s differs from derived %s\n"
             (Weight.to_string weight) (Weight.to_string derived_weight);
           (* Add constraint: declared = derived *)
           Weight.add_constraint state.infer_ctx weight derived_weight;
           derived_weight
         end else
           derived_weight
       in
       let j = { name; prop; weight = final_weight; status = Derived from_name } in
       Hashtbl.replace state.judgments name j;
       Printf.printf "  %s : %s 〔 %s 〕  (from %s by %s)\n"
         name prop (Weight.to_string final_weight) from_name justification;
       Ok state)
  | Direct ->
    let j = { name; prop; weight; status = Assumed } in
    Hashtbl.replace state.judgments name j;
    Printf.printf "  %s : %s 〔 %s 〕  (direct)\n" name prop (Weight.to_string weight);
    Ok state

(* Process a contradiction *)
let add_contradiction state p q =
  match Hashtbl.find_opt state.judgments p,
        Hashtbl.find_opt state.judgments q with
  | Some jp, Some jq ->
    Printf.printf "\n  CONTRADICTION: %s and %s\n" p q;
    Printf.printf "     %s 〔 %s 〕\n" p (Weight.to_string jp.weight);
    Printf.printf "     %s 〔 %s 〕\n" q (Weight.to_string jq.weight);
    (* Find the weight variable(s) to force to 0 *)
    (* If both have same weight -> that weight = 0 *)
    (* If one is constant 1 and other is variable w -> w = 0 *)
    let wp = Weight.simplify jp.weight in
    let wq = Weight.simplify jq.weight in
    let (forced_weight, forced_str) =
      if Weight.equal wp wq then
        (wp, Weight.to_string wp)
      else if Weight.equal wp Weight.one then
        (wq, Weight.to_string wq)
      else if Weight.equal wq Weight.one then
        (wp, Weight.to_string wp)
      else
        (* Both are different variables - force both via product *)
        (Weight.mul wp wq, Printf.sprintf "%s * %s" (Weight.to_string wp) (Weight.to_string wq))
    in
    Printf.printf "     -> %s = 0\n" forced_str;
    (* Add constraint to inference context *)
    Weight.add_zero_constraint state.infer_ctx forced_weight;
    let state = { state with weight_eqs = (forced_weight, Weight.zero) :: state.weight_eqs } in
    (* Update judgments to show forced weight *)
    Hashtbl.iter (fun name j ->
      let jw = Weight.simplify j.weight in
      if Weight.equal jw (Weight.simplify forced_weight) ||
         Weight.equal jw (Weight.simplify wp) ||
         Weight.equal jw (Weight.simplify wq) then
        Hashtbl.replace state.judgments name { j with status = Forced Weight.zero }
    ) state.judgments;
    Ok state
  | None, _ -> Error (Printf.sprintf "Unknown judgment: %s" p)
  | _, None -> Error (Printf.sprintf "Unknown judgment: %s" q)

(* Compute negated weight *)
let negate_weight state w =
  let dominated_by_zero = List.exists (fun (w', v) ->
    Weight.equal (Weight.simplify w') (Weight.simplify w) &&
    Weight.equal v Weight.zero
  ) state.weight_eqs in
  if dominated_by_zero then Weight.one
  else Weight.neg w

(* Add a negation/conclusion *)
let add_negation state name from_name =
  match Hashtbl.find_opt state.judgments from_name with
  | None -> Error (Printf.sprintf "Unknown judgment: %s" from_name)
  | Some from_j ->
    let neg_weight = negate_weight state from_j.weight in
    let j = { name; prop = "not " ^ from_j.prop; weight = neg_weight; status = Derived from_name } in
    Hashtbl.replace state.judgments name j;
    Printf.printf "\n  THEREFORE %s : not %s 〔 %s 〕\n" name from_j.prop (Weight.to_string neg_weight);
    Ok state

(* Add a provability assertion: Prov_w(φ) *)
let add_provable state name prop weight =
  Hashtbl.replace state.provables name (prop, weight);
  Printf.printf "  provable %s : Prov(%s) 〔 %s 〕\n" name prop (Weight.to_string weight);
  Ok state

(* Add and solve a fixpoint: x = f(x)
   Currently handles w = neg w -> w = 1/2 *)
let add_fixpoint state name weight_expr =
  let simplified = Weight.simplify weight_expr in
  let result = match simplified with
    | Weight.Neg (Weight.Var v) when v = name ->
        (* w = neg w -> w = 1/2 (negation fixpoint) *)
        let half = Weight.solve_negation_fixpoint () in
        Hashtbl.replace state.fixpoints name half;
        Printf.printf "\n  FIXPOINT: %s = neg %s\n" name name;
        Printf.printf "     Solved: %s = %s\n" name (Weight.rat_to_string half);
        Some half
    | Weight.Neg (Weight.Infer n) ->
        (* Inference variable fixpoint: ?n = neg ?n -> ?n = 1/2 *)
        let half = Weight.solve_negation_fixpoint () in
        Hashtbl.replace state.fixpoints name half;
        Printf.printf "\n  FIXPOINT: %s = neg ?%d\n" name n;
        Printf.printf "     Solved: %s = %s\n" name (Weight.rat_to_string half);
        (* Add to inference context *)
        state.infer_ctx.fixpoints <- (n, fun x -> Weight.Neg x) :: state.infer_ctx.fixpoints;
        Some half
    | Weight.Mul (Weight.Var v1, Weight.Var v2) when v1 = name && v2 = name ->
        (* w = w*w -> w = 0 or w = 1 (idempotent) *)
        Printf.printf "\n  FIXPOINT: %s = %s * %s\n" name name name;
        Printf.printf "     Solutions: 0 or 1 (choosing 1)\n";
        let one = Weight.rat_one in
        Hashtbl.replace state.fixpoints name one;
        Some one
    | Weight.Var v when v = name ->
        (* w = w (trivial, any value works) *)
        Printf.printf "\n  FIXPOINT: %s = %s (trivial)\n" name name;
        None
    | _ ->
        Printf.printf "\n  FIXPOINT: %s = %s (unknown form)\n" name (Weight.to_string simplified);
        None
  in
  match result with
  | Some _ -> Ok state
  | None -> Ok state

(* Add an encoding: ⌈φ⌉ *)
let add_encoding state name prop =
  Hashtbl.replace state.encodings name prop;
  Printf.printf "  encode %s = ⌈%s⌉\n" name prop;
  Ok state

(* Get the solved weight for a variable if available *)
let get_solved_weight state var_name =
  Hashtbl.find_opt state.fixpoints var_name

(* Process a single declaration *)
let process_decl state = function
  | Postulate (name, prop, weight) -> add_postulate state name prop weight
  | Derive (name, prop, weight, deriv) -> add_derivation state name prop weight deriv
  | Contradict (p, q) -> add_contradiction state p q
  | Negate (name, from_name) -> add_negation state name from_name
  | Provable (name, prop, weight) -> add_provable state name prop weight
  | Fixpoint (name, weight) -> add_fixpoint state name weight
  | Encode (name, prop) -> add_encoding state name prop

(* Run a proof *)
let check_proof decls =
  Printf.printf "\n==============================================================\n";
  Printf.printf "  ProbTT Proof Checker\n";
  Printf.printf "==============================================================\n\n";

  Weight.reset_infer ();  (* Reset inference counter for fresh run *)
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
    (match Weight.solve_inference final_state.infer_ctx with
     | Ok subst ->
       Printf.printf "\n==============================================================\n";
       Printf.printf "  Proof checked successfully\n";
       (* Print inferred weights if any *)
       if subst <> [] then begin
         Printf.printf "\n  Inferred weights:\n";
         List.iter (fun (n, w) ->
           Printf.printf "    ?%d = %s\n" n (Weight.to_string w)
         ) subst
       end;
       (* Print solved fixpoints *)
       if Hashtbl.length final_state.fixpoints > 0 then begin
         Printf.printf "\n  Solved fixpoints:\n";
         Hashtbl.iter (fun name value ->
           Printf.printf "    %s = %s\n" name (Weight.rat_to_string value)
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

(* === √2 proof as data === *)
let sqrt2_proof_decls =
  let w = Weight.var "w" in
  [
    Postulate ("sqrt2_rational", "√2_is_rational", w);
    Postulate ("gcd_is_1", "gcd(p,q)=1", w);
    Derive ("p_even", "p_is_even", w, From ("sqrt2_rational", "algebra"));
    Derive ("q_even", "q_is_even", w, From ("p_even", "substitution"));
    Derive ("gcd_geq_2", "gcd(p,q)≥2", w, From ("q_even", "both_even"));
    Contradict ("gcd_is_1", "gcd_geq_2");
    Negate ("sqrt2_irrational", "sqrt2_rational");
  ]

let run_sqrt2_proof () =
  Printf.printf "
╔══════════════════════════════════════════════════════════════╗
║  √2 Irrationality Proof                                      ║
║                                                              ║
║  Structure:                                                  ║
║  1. Assume √2 = p/q in lowest terms, at weight w             ║
║  2. Derive p even, q even (weight preserved)                 ║
║  3. Contradiction: gcd=1 AND gcd≥2                           ║
║  4. Therefore w = 0, so ¬(√2 rational) has weight 1          ║
╚══════════════════════════════════════════════════════════════╝
";
  check_proof sqrt2_proof_decls
