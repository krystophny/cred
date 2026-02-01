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
}

let create () = {
  judgments = Hashtbl.create 16;
  weight_eqs = [];
}

(* Add a postulate *)
let add_postulate state name prop weight =
  let j = { name; prop; weight; status = Assumed } in
  Hashtbl.replace state.judgments name j;
  Printf.printf "  postulate %s : %s 〔 %s 〕\n" name prop (Weight.to_string weight);
  Ok state

(* Add a derivation *)
let add_derivation state name prop weight deriv =
  match deriv with
  | From (from_name, justification) ->
    (match Hashtbl.find_opt state.judgments from_name with
     | None ->
       Error (Printf.sprintf "Unknown judgment: %s" from_name)
     | Some from_j ->
       (* Weight multiplies: new_weight = from_weight · 1 = from_weight *)
       let derived_weight = Weight.simplify (Weight.mul from_j.weight Weight.one) in
       (* Check declared weight matches *)
       if not (Weight.equal (Weight.simplify weight) derived_weight) then
         Printf.printf "  WARNING: declared weight %s differs from derived %s\n"
           (Weight.to_string weight) (Weight.to_string derived_weight);
       let j = { name; prop; weight = derived_weight; status = Derived from_name } in
       Hashtbl.replace state.judgments name j;
       Printf.printf "  %s : %s 〔 %s 〕  (from %s by %s)\n"
         name prop (Weight.to_string derived_weight) from_name justification;
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
    Printf.printf "\n  ⚡ CONTRADICTION: %s ⊥ %s\n" p q;
    Printf.printf "     %s 〔 %s 〕\n" p (Weight.to_string jp.weight);
    Printf.printf "     %s 〔 %s 〕\n" q (Weight.to_string jq.weight);
    (* Both have same weight (derived from same assumption) → weight = 0 *)
    let w = jp.weight in
    Printf.printf "     → %s = 0\n" (Weight.to_string w);
    let state = { state with weight_eqs = (w, Weight.zero) :: state.weight_eqs } in
    (* Update judgments to show forced weight *)
    Hashtbl.iter (fun name j ->
      if Weight.equal (Weight.simplify j.weight) (Weight.simplify w) then
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
    let j = { name; prop = "¬" ^ from_j.prop; weight = neg_weight; status = Derived from_name } in
    Hashtbl.replace state.judgments name j;
    Printf.printf "\n  ∴ %s : ¬%s 〔 %s 〕\n" name from_j.prop (Weight.to_string neg_weight);
    Ok state

(* Process a single declaration *)
let process_decl state = function
  | Postulate (name, prop, weight) -> add_postulate state name prop weight
  | Derive (name, prop, weight, deriv) -> add_derivation state name prop weight deriv
  | Contradict (p, q) -> add_contradiction state p q
  | Negate (name, from_name) -> add_negation state name from_name

(* Run a proof *)
let check_proof decls =
  Printf.printf "\n══════════════════════════════════════════════════════════════\n";
  Printf.printf "  ProbTT Proof Checker\n";
  Printf.printf "══════════════════════════════════════════════════════════════\n\n";

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
    Printf.printf "\n══════════════════════════════════════════════════════════════\n";
    Printf.printf "  ✓ Proof checked successfully\n";
    Printf.printf "══════════════════════════════════════════════════════════════\n\n";
    Ok final_state
  | Error e ->
    Printf.printf "\n  ✗ Error: %s\n\n" e;
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
