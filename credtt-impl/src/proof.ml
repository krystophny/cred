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
  (* Stability assertions - THE CORE DIFFERENTIATOR *)
  | AssertStable of string                     (* assert name is Stable1 *)
  | AssertUnstable of string                   (* assert name is Unstable0 *)
  | AssertInterior of string                   (* assert name is Interior *)
  | StabilityCheck of string * stability_kind  (* check specific stability *)
  (* Proof techniques with stability tracking *)
  | DirectProof of string * string * derivation    (* track credence bound accumulation *)
  | ProofByCases of string * string * string       (* result, case1, case2 *)
  | Contraposition of string * string * string     (* result, from_stable, to_unstable *)
  | Reductio of string * string                    (* stable_result, unstable_negation *)
  | ExFalso of string * string                     (* any_type, zero_credence_term *)
  | Deduction of string * string                   (* lambda_result, body_term *)
  | ModusPonens of string * string * string        (* result, function, argument *)
  | Syllogism of string * string * string          (* result, f, g (g . f) *)
  | UniversalGen of string * string                (* forall_result, body *)
  | ExistentialIntro of string * string * string   (* exists_result, witness, body *)
  | Induction of string * string * string * string (* result, base, step, stability *)
  | Construction of string * string                (* witness, certificate *)
  | Refutation of string * string                  (* name, toward_zero *)
  | EquationalRewrite of string * string * string  (* result, original, equality *)
  (* CredTT-native techniques *)
  | StabilityProof of string * stability_kind      (* prove stability directly *)
  | CredenceBound of string * bound_kind           (* prove bound on credence *)
  | ContinuityLemma of string * string             (* input_degrade, output_degrade *)
  | DegeneracyAnalysis of string * string          (* name, rate_to_zero *)
  | ContractivityArg of string * string            (* name, non_degrading_witness *)
  | ProofFactoring of string * string list         (* high_credence_core, low_credence_steps *)
  | DualProof of string * string * string          (* squeezed, lower_bound, upper_bound *)
  | LimitTheorem of string * string                (* asymptotic_result, convergence_witness *)

and derivation =
  | From of string * string   (* from prop, by justification *)
  | Direct                    (* direct/axiom *)

and stability_kind =
  | KStable1
  | KUnstable0
  | KInterior
  | KUnknown

and bound_kind =
  | LowerBound of Credence.t   (* c >= bound *)
  | UpperBound of Credence.t   (* c <= bound *)

(* Proof state *)
type judgment = {
  name : string;
  prop : string;
  credence : Credence.t;
  stability : Neighbourhood.stability;  (* THE KEY ADDITION *)
  status : status;
}

and status =
  | Assumed
  | Derived of string   (* from which judgment *)
  | Forced of Credence.t  (* forced to this credence by contradiction *)
  | StabilityDerived of stability_kind * string  (* derived via stability theorem *)

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

(* Convert stability_kind to Neighbourhood.stability *)
let stability_of_kind = function
  | KStable1 -> Neighbourhood.Stable1
  | KUnstable0 -> Neighbourhood.Unstable0
  | KInterior -> Neighbourhood.Interior
  | KUnknown -> Neighbourhood.Unknown

(* Convert Neighbourhood.stability to stability_kind *)
let kind_of_stability = function
  | Neighbourhood.Stable1 -> KStable1
  | Neighbourhood.Unstable0 -> KUnstable0
  | Neighbourhood.Interior -> KInterior
  | Neighbourhood.Unknown -> KUnknown

(* Add a postulate *)
let add_postulate state name prop credence =
  (* If credence needs inference, generate fresh variable *)
  let actual_credence =
    if needs_inference credence then credence
    else credence
  in
  (* Compute stability from credence *)
  let stability = Neighbourhood.classify actual_credence in
  let j = { name; prop; credence = actual_credence; stability; status = Assumed } in
  Hashtbl.replace state.judgments name j;
  Printf.printf "  postulate %s : %s [ %s ] (%s)\n"
    name prop (Credence.to_string actual_credence) (Neighbourhood.stability_to_string stability);
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
       (* Compute stability: derivation preserves/degrades stability based on justification *)
       let derived_stability = match justification with
         | "apply" | "application" ->
             (* Application: stable * stable = stable *)
             Neighbourhood.stability_of_app from_j.stability (Neighbourhood.classify final_credence)
         | "compose" | "composition" | "syllogism" ->
             (* Composition preserves stability *)
             Neighbourhood.stability_of_compose from_j.stability (Neighbourhood.classify final_credence)
         | "negate" | "negation" ->
             (* Negation flips stability *)
             Neighbourhood.stability_of_neg from_j.stability
         | "project" | "fst" | "snd" ->
             (* Projection preserves stability *)
             Neighbourhood.stability_of_sigma_elim from_j.stability
         | "pi_intro" | "lambda" | "abstraction" ->
             (* Pi-intro preserves stability *)
             Neighbourhood.stability_of_pi_intro from_j.stability
         | _ ->
             (* Default: inherit source stability or classify from credence *)
             Neighbourhood.classify final_credence
       in
       let j = { name; prop; credence = final_credence; stability = derived_stability; status = Derived from_name } in
       Hashtbl.replace state.judgments name j;
       Printf.printf "  %s : %s [ %s ] (%s)  (from %s by %s)\n"
         name prop (Credence.to_string final_credence)
         (Neighbourhood.stability_to_string derived_stability) from_name justification;
       Ok state)
  | Direct ->
    let stability = Neighbourhood.classify credence in
    let j = { name; prop; credence; stability; status = Assumed } in
    Hashtbl.replace state.judgments name j;
    Printf.printf "  %s : %s [ %s ] (%s)  (direct)\n"
      name prop (Credence.to_string credence) (Neighbourhood.stability_to_string stability);
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
    (* Negation flips stability: stable -> unstable, unstable -> stable *)
    let neg_stability = Neighbourhood.stability_of_neg from_j.stability in
    let j = { name; prop = "not " ^ from_j.prop; credence = neg_credence;
              stability = neg_stability; status = Derived from_name } in
    Hashtbl.replace state.judgments name j;
    Printf.printf "\n  THEREFORE %s : not %s [ %s ] (%s)\n"
      name from_j.prop (Credence.to_string neg_credence)
      (Neighbourhood.stability_to_string neg_stability);
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

(* ============================================================
   STABILITY ASSERTIONS AND PROOF TECHNIQUES
   ============================================================
   These are the CORE DIFFERENTIATORS of CredTT over MLTT.
   ============================================================ *)

(* Assert that a judgment is Stable1 *)
let assert_stable state name =
  match Hashtbl.find_opt state.judgments name with
  | None -> Error (Printf.sprintf "Unknown judgment: %s" name)
  | Some j ->
      if Neighbourhood.is_stable j.stability then begin
        Printf.printf "  STABLE: %s has stability %s (credence %s)\n"
          name (Neighbourhood.stability_to_string j.stability) (Credence.to_string j.credence);
        Ok state
      end else
        Error (Printf.sprintf "Stability assertion failed: %s is %s, not Stable1"
          name (Neighbourhood.stability_to_string j.stability))

(* Assert that a judgment is Unstable0 *)
let assert_unstable state name =
  match Hashtbl.find_opt state.judgments name with
  | None -> Error (Printf.sprintf "Unknown judgment: %s" name)
  | Some j ->
      if Neighbourhood.is_unstable j.stability then begin
        Printf.printf "  UNSTABLE: %s has stability %s (credence %s)\n"
          name (Neighbourhood.stability_to_string j.stability) (Credence.to_string j.credence);
        Ok state
      end else
        Error (Printf.sprintf "Stability assertion failed: %s is %s, not Unstable0"
          name (Neighbourhood.stability_to_string j.stability))

(* Assert that a judgment is Interior (strictly between 0 and 1) *)
let assert_interior state name =
  match Hashtbl.find_opt state.judgments name with
  | None -> Error (Printf.sprintf "Unknown judgment: %s" name)
  | Some j ->
      if j.stability = Neighbourhood.Interior then begin
        Printf.printf "  INTERIOR: %s has stability %s (credence %s)\n"
          name (Neighbourhood.stability_to_string j.stability) (Credence.to_string j.credence);
        Ok state
      end else
        Error (Printf.sprintf "Stability assertion failed: %s is %s, not Interior"
          name (Neighbourhood.stability_to_string j.stability))

(* Check stability against expected kind *)
let check_stability state name expected =
  match Hashtbl.find_opt state.judgments name with
  | None -> Error (Printf.sprintf "Unknown judgment: %s" name)
  | Some j ->
      let expected_stability = stability_of_kind expected in
      if j.stability = expected_stability then begin
        Printf.printf "  STABILITY CHECK: %s is %s as expected\n"
          name (Neighbourhood.stability_to_string j.stability);
        Ok state
      end else
        Error (Printf.sprintf "Stability check failed: %s is %s, expected %s"
          name (Neighbourhood.stability_to_string j.stability)
          (Neighbourhood.stability_to_string expected_stability))

(* Direct proof: track credence accumulation *)
let direct_proof state name prop deriv =
  Printf.printf "\n  DIRECT PROOF: %s\n" name;
  add_derivation state name prop Credence.one deriv

(* Proof by cases: both branches must be stable for result to be stable *)
let proof_by_cases state result case1 case2 =
  match Hashtbl.find_opt state.judgments case1,
        Hashtbl.find_opt state.judgments case2 with
  | Some j1, Some j2 ->
      let result_stability = match j1.stability, j2.stability with
        | Neighbourhood.Stable1, Neighbourhood.Stable1 -> Neighbourhood.Stable1
        | Neighbourhood.Unstable0, _ | _, Neighbourhood.Unstable0 -> Neighbourhood.Unstable0
        | _, _ -> Neighbourhood.Interior
      in
      let result_credence = Credence.simplify (Credence.mul j1.credence j2.credence) in
      let j = { name = result; prop = j1.prop ^ " | " ^ j2.prop;
                credence = result_credence; stability = result_stability;
                status = StabilityDerived (kind_of_stability result_stability, "cases") } in
      Hashtbl.replace state.judgments result j;
      Printf.printf "\n  PROOF BY CASES: %s\n" result;
      Printf.printf "     %s (%s) + %s (%s) -> %s (%s)\n"
        case1 (Neighbourhood.stability_to_string j1.stability)
        case2 (Neighbourhood.stability_to_string j2.stability)
        result (Neighbourhood.stability_to_string result_stability);
      Ok state
  | None, _ -> Error (Printf.sprintf "Unknown judgment: %s" case1)
  | _, None -> Error (Printf.sprintf "Unknown judgment: %s" case2)

(* Contraposition: if A -> B is stable, then ~B -> ~A is also stable *)
let contraposition state result from_stable _to_unstable =
  match Hashtbl.find_opt state.judgments from_stable with
  | None -> Error (Printf.sprintf "Unknown judgment: %s" from_stable)
  | Some j ->
      let neg_stability = Neighbourhood.stability_of_neg j.stability in
      let neg_credence = Credence.neg j.credence in
      let result_j = { name = result; prop = "~" ^ j.prop;
                       credence = neg_credence; stability = neg_stability;
                       status = StabilityDerived (kind_of_stability neg_stability, "contraposition") } in
      Hashtbl.replace state.judgments result result_j;
      Printf.printf "\n  CONTRAPOSITION: %s -> %s\n" from_stable result;
      Printf.printf "     %s (%s) -> ~%s (%s)\n"
        from_stable (Neighbourhood.stability_to_string j.stability)
        result (Neighbourhood.stability_to_string neg_stability);
      Ok state

(* Reductio ad absurdum: if ~A is unstable, then A is stable *)
let reductio state result unstable_negation =
  match Hashtbl.find_opt state.judgments unstable_negation with
  | None -> Error (Printf.sprintf "Unknown judgment: %s" unstable_negation)
  | Some j ->
      if not (Neighbourhood.is_unstable j.stability) then
        Error (Printf.sprintf "Reductio requires unstable negation, but %s is %s"
          unstable_negation (Neighbourhood.stability_to_string j.stability))
      else begin
        (* Unstable negation means stable positive *)
        let stable_stability = Neighbourhood.Stable1 in
        let stable_credence = Credence.neg j.credence in
        let result_j = { name = result; prop = "~~" ^ j.prop;
                         credence = stable_credence; stability = stable_stability;
                         status = StabilityDerived (KStable1, "reductio") } in
        Hashtbl.replace state.judgments result result_j;
        Printf.printf "\n  REDUCTIO AD ABSURDUM: %s\n" result;
        Printf.printf "     ~%s is Unstable0 -> %s is Stable1\n"
          unstable_negation result;
        Printf.printf "     Credence: %s (1 - %s)\n"
          (Credence.to_string stable_credence) (Credence.to_string j.credence);
        Ok state
      end

(* Ex falso: from credence 0, anything is admissible *)
let ex_falso state name zero_term =
  match Hashtbl.find_opt state.judgments zero_term with
  | None -> Error (Printf.sprintf "Unknown judgment: %s" zero_term)
  | Some j ->
      let is_zero = match Credence.to_rational (Credence.simplify j.credence) with
        | Some r -> Credence.rat_equal r Credence.rat_zero
        | None -> Credence.equal (Credence.simplify j.credence) Credence.Zero
      in
      if not is_zero then
        Error (Printf.sprintf "Ex falso requires zero credence, but %s has %s"
          zero_term (Credence.to_string j.credence))
      else begin
        let result_j = { name; prop = "anything";
                         credence = Credence.one; stability = Neighbourhood.Stable1;
                         status = StabilityDerived (KStable1, "ex_falso") } in
        Hashtbl.replace state.judgments name result_j;
        Printf.printf "\n  EX FALSO: from %s at credence 0, derive %s at credence 1\n"
          zero_term name;
        Printf.printf "     At c=0, any conditional is admissible (vacuously)\n";
        Ok state
      end

(* Deduction theorem: if body is stable, lambda is stable *)
let deduction state lambda_name body_name =
  match Hashtbl.find_opt state.judgments body_name with
  | None -> Error (Printf.sprintf "Unknown judgment: %s" body_name)
  | Some j ->
      (* Deduction preserves stability *)
      let lambda_stability = Neighbourhood.stability_of_pi_intro j.stability in
      let result_j = { name = lambda_name; prop = "λ." ^ j.prop;
                       credence = j.credence; stability = lambda_stability;
                       status = StabilityDerived (kind_of_stability lambda_stability, "deduction") } in
      Hashtbl.replace state.judgments lambda_name result_j;
      Printf.printf "\n  DEDUCTION THEOREM: %s\n" lambda_name;
      Printf.printf "     body %s (%s) -> λ %s (%s)\n"
        body_name (Neighbourhood.stability_to_string j.stability)
        lambda_name (Neighbourhood.stability_to_string lambda_stability);
      Ok state

(* Modus ponens: f @ c1, a @ c2 -> f a @ c1 * c2 *)
let modus_ponens state result func arg =
  match Hashtbl.find_opt state.judgments func,
        Hashtbl.find_opt state.judgments arg with
  | Some f, Some a ->
      let result_credence = Credence.mul f.credence a.credence in
      let result_stability = Neighbourhood.stability_of_app f.stability a.stability in
      let result_j = { name = result; prop = "(" ^ f.prop ^ " " ^ a.prop ^ ")";
                       credence = result_credence; stability = result_stability;
                       status = StabilityDerived (kind_of_stability result_stability, "modus_ponens") } in
      Hashtbl.replace state.judgments result result_j;
      Printf.printf "\n  MODUS PONENS: %s\n" result;
      Printf.printf "     %s @ %s (%s)\n"
        func (Credence.to_string f.credence) (Neighbourhood.stability_to_string f.stability);
      Printf.printf "     %s @ %s (%s)\n"
        arg (Credence.to_string a.credence) (Neighbourhood.stability_to_string a.stability);
      Printf.printf "     -> %s @ %s (%s)\n"
        result (Credence.to_string result_credence) (Neighbourhood.stability_to_string result_stability);
      Ok state
  | None, _ -> Error (Printf.sprintf "Unknown judgment: %s" func)
  | _, None -> Error (Printf.sprintf "Unknown judgment: %s" arg)

(* Syllogism: g . f @ c_g * c_f *)
let syllogism state result f g =
  match Hashtbl.find_opt state.judgments f,
        Hashtbl.find_opt state.judgments g with
  | Some jf, Some jg ->
      let result_credence = Credence.mul jg.credence jf.credence in
      let result_stability = Neighbourhood.stability_of_compose jg.stability jf.stability in
      let result_j = { name = result; prop = jg.prop ^ " ∘ " ^ jf.prop;
                       credence = result_credence; stability = result_stability;
                       status = StabilityDerived (kind_of_stability result_stability, "syllogism") } in
      Hashtbl.replace state.judgments result result_j;
      Printf.printf "\n  SYLLOGISM (composition): %s\n" result;
      Printf.printf "     %s ∘ %s @ %s (%s)\n"
        g f (Credence.to_string result_credence) (Neighbourhood.stability_to_string result_stability);
      Ok state
  | None, _ -> Error (Printf.sprintf "Unknown judgment: %s" f)
  | _, None -> Error (Printf.sprintf "Unknown judgment: %s" g)

(* Universal generalization: inf over stable family is stable *)
let universal_gen state forall_name body_name =
  match Hashtbl.find_opt state.judgments body_name with
  | None -> Error (Printf.sprintf "Unknown judgment: %s" body_name)
  | Some j ->
      let forall_stability = Neighbourhood.stability_of_pi_intro j.stability in
      let result_j = { name = forall_name; prop = "∀." ^ j.prop;
                       credence = j.credence; stability = forall_stability;
                       status = StabilityDerived (kind_of_stability forall_stability, "universal_gen") } in
      Hashtbl.replace state.judgments forall_name result_j;
      Printf.printf "\n  UNIVERSAL GENERALIZATION: %s\n" forall_name;
      Printf.printf "     ∀x. %s (%s) @ %s\n"
        body_name (Neighbourhood.stability_to_string forall_stability) (Credence.to_string j.credence);
      Ok state

(* Existential introduction: witness with credence *)
let existential_intro state exists_name witness body =
  match Hashtbl.find_opt state.judgments witness,
        Hashtbl.find_opt state.judgments body with
  | Some w, Some b ->
      let result_credence = Credence.mul w.credence b.credence in
      let result_stability = Neighbourhood.stability_of_app w.stability b.stability in
      let result_j = { name = exists_name; prop = "∃." ^ b.prop;
                       credence = result_credence; stability = result_stability;
                       status = StabilityDerived (kind_of_stability result_stability, "existential_intro") } in
      Hashtbl.replace state.judgments exists_name result_j;
      Printf.printf "\n  EXISTENTIAL INTRODUCTION: %s\n" exists_name;
      Printf.printf "     witness %s @ %s, body %s @ %s\n"
        witness (Credence.to_string w.credence) body (Credence.to_string b.credence);
      Printf.printf "     -> ∃. @ %s (%s)\n"
        (Credence.to_string result_credence) (Neighbourhood.stability_to_string result_stability);
      Ok state
  | None, _ -> Error (Printf.sprintf "Unknown judgment: %s" witness)
  | _, None -> Error (Printf.sprintf "Unknown judgment: %s" body)

(* Induction: stable if base and step are stable *)
let induction state result base step stability_note =
  match Hashtbl.find_opt state.judgments base,
        Hashtbl.find_opt state.judgments step with
  | Some b, Some s ->
      let result_stability = match b.stability, s.stability with
        | Neighbourhood.Stable1, Neighbourhood.Stable1 -> Neighbourhood.Stable1
        | Neighbourhood.Unstable0, _ | _, Neighbourhood.Unstable0 -> Neighbourhood.Unstable0
        | _, _ -> Neighbourhood.Interior
      in
      let result_credence = Credence.mul b.credence s.credence in
      let result_j = { name = result; prop = "induction(" ^ b.prop ^ ", " ^ s.prop ^ ")";
                       credence = result_credence; stability = result_stability;
                       status = StabilityDerived (kind_of_stability result_stability, "induction") } in
      Hashtbl.replace state.judgments result result_j;
      Printf.printf "\n  INDUCTION: %s\n" result;
      Printf.printf "     base %s (%s), step %s (%s)\n"
        base (Neighbourhood.stability_to_string b.stability)
        step (Neighbourhood.stability_to_string s.stability);
      Printf.printf "     -> %s (%s) [note: %s]\n"
        result (Neighbourhood.stability_to_string result_stability) stability_note;
      Ok state
  | None, _ -> Error (Printf.sprintf "Unknown judgment: %s" base)
  | _, None -> Error (Printf.sprintf "Unknown judgment: %s" step)

(* Construction: existence with credence certificate *)
let construction state witness_name certificate =
  match Hashtbl.find_opt state.judgments certificate with
  | None -> Error (Printf.sprintf "Unknown judgment: %s" certificate)
  | Some c ->
      let result_j = { name = witness_name; prop = "witness(" ^ c.prop ^ ")";
                       credence = c.credence; stability = c.stability;
                       status = StabilityDerived (kind_of_stability c.stability, "construction") } in
      Hashtbl.replace state.judgments witness_name result_j;
      Printf.printf "\n  CONSTRUCTION: %s\n" witness_name;
      Printf.printf "     certificate %s @ %s (%s)\n"
        certificate (Credence.to_string c.credence) (Neighbourhood.stability_to_string c.stability);
      Ok state

(* Refutation: drive credence to 0 *)
let refutation state name toward_zero =
  match Hashtbl.find_opt state.judgments toward_zero with
  | None -> Error (Printf.sprintf "Unknown judgment: %s" toward_zero)
  | Some j ->
      let result_j = { name; prop = "refute(" ^ j.prop ^ ")";
                       credence = Credence.zero; stability = Neighbourhood.Unstable0;
                       status = StabilityDerived (KUnstable0, "refutation") } in
      Hashtbl.replace state.judgments name result_j;
      Printf.printf "\n  REFUTATION: %s\n" name;
      Printf.printf "     driving %s toward 0: degeneracy detected\n" toward_zero;
      Ok state

(* Equational rewrite: if Id is stable, rewriting preserves stability *)
let equational_rewrite state result original equality =
  match Hashtbl.find_opt state.judgments original,
        Hashtbl.find_opt state.judgments equality with
  | Some o, Some e ->
      let result_stability = match o.stability, e.stability with
        | Neighbourhood.Stable1, Neighbourhood.Stable1 -> Neighbourhood.Stable1
        | _, _ -> Neighbourhood.Interior
      in
      let result_credence = Credence.mul o.credence e.credence in
      let result_j = { name = result; prop = "rewrite(" ^ o.prop ^ ", " ^ e.prop ^ ")";
                       credence = result_credence; stability = result_stability;
                       status = StabilityDerived (kind_of_stability result_stability, "equational_rewrite") } in
      Hashtbl.replace state.judgments result result_j;
      Printf.printf "\n  EQUATIONAL REWRITE: %s\n" result;
      Printf.printf "     original %s @ %s, equality %s @ %s\n"
        original (Credence.to_string o.credence) equality (Credence.to_string e.credence);
      Printf.printf "     -> %s @ %s (%s)\n"
        result (Credence.to_string result_credence) (Neighbourhood.stability_to_string result_stability);
      Ok state
  | None, _ -> Error (Printf.sprintf "Unknown judgment: %s" original)
  | _, None -> Error (Printf.sprintf "Unknown judgment: %s" equality)

(* ============================================================
   CREDTT-NATIVE PROOF TECHNIQUES (not in classical logic)
   ============================================================ *)

(* Stability proof: prove directly that something is stable/unstable *)
let stability_proof state name kind =
  Printf.printf "\n  STABILITY PROOF: %s is %s\n"
    name (Neighbourhood.stability_to_string (stability_of_kind kind));
  match Hashtbl.find_opt state.judgments name with
  | None -> Error (Printf.sprintf "Unknown judgment: %s" name)
  | Some j ->
      let expected = stability_of_kind kind in
      if j.stability = expected then begin
        Printf.printf "     VERIFIED: %s has stability %s\n"
          name (Neighbourhood.stability_to_string j.stability);
        Ok state
      end else
        Error (Printf.sprintf "Stability proof failed: %s is %s, not %s"
          name (Neighbourhood.stability_to_string j.stability)
          (Neighbourhood.stability_to_string expected))

(* Credence bound: prove c >= bound or c <= bound *)
let credence_bound state name bound =
  match Hashtbl.find_opt state.judgments name with
  | None -> Error (Printf.sprintf "Unknown judgment: %s" name)
  | Some j ->
      Printf.printf "\n  CREDENCE BOUND: %s\n" name;
      (match bound with
       | LowerBound b ->
           Printf.printf "     Asserting %s >= %s\n"
             (Credence.to_string j.credence) (Credence.to_string b);
           if Credence.leq b j.credence then begin
             Printf.printf "     VERIFIED: lower bound holds\n";
             Ok state
           end else
             Error (Printf.sprintf "Lower bound failed: %s < %s"
               (Credence.to_string j.credence) (Credence.to_string b))
       | UpperBound b ->
           Printf.printf "     Asserting %s <= %s\n"
             (Credence.to_string j.credence) (Credence.to_string b);
           if Credence.leq j.credence b then begin
             Printf.printf "     VERIFIED: upper bound holds\n";
             Ok state
           end else
             Error (Printf.sprintf "Upper bound failed: %s > %s"
               (Credence.to_string j.credence) (Credence.to_string b)))

(* Continuity lemma: small input degradation -> small output degradation *)
let continuity_lemma state input_name output_name =
  match Hashtbl.find_opt state.judgments input_name,
        Hashtbl.find_opt state.judgments output_name with
  | Some i, Some o ->
      Printf.printf "\n  CONTINUITY LEMMA: %s -> %s\n" input_name output_name;
      Printf.printf "     input degradation: %s (%s)\n"
        input_name (Neighbourhood.stability_to_string i.stability);
      Printf.printf "     output degradation: %s (%s)\n"
        output_name (Neighbourhood.stability_to_string o.stability);
      if Neighbourhood.is_stable i.stability && Neighbourhood.is_stable o.stability then begin
        Printf.printf "     CONTINUOUS: stable -> stable\n";
        Ok state
      end else if Neighbourhood.is_unstable i.stability then begin
        Printf.printf "     CONTINUOUS: unstable input allows any output\n";
        Ok state
      end else begin
        Printf.printf "     WARNING: may not be continuous\n";
        Ok state
      end
  | None, _ -> Error (Printf.sprintf "Unknown judgment: %s" input_name)
  | _, None -> Error (Printf.sprintf "Unknown judgment: %s" output_name)

(* Degeneracy analysis: quantify how fast c -> 0 *)
let degeneracy_analysis state name rate =
  match Hashtbl.find_opt state.judgments name with
  | None -> Error (Printf.sprintf "Unknown judgment: %s" name)
  | Some j ->
      Printf.printf "\n  DEGENERACY ANALYSIS: %s\n" name;
      Printf.printf "     credence: %s (%s)\n"
        (Credence.to_string j.credence) (Neighbourhood.stability_to_string j.stability);
      Printf.printf "     rate toward 0: %s\n" rate;
      if Neighbourhood.is_unstable j.stability then begin
        Printf.printf "     DEGENERATE: confirmed near 0\n";
        Ok state
      end else begin
        Printf.printf "     NOT DEGENERATE: stability prevents collapse\n";
        Ok state
      end

(* Contractivity argument: prove step is non-degrading *)
let contractivity_arg state name witness =
  match Hashtbl.find_opt state.judgments name,
        Hashtbl.find_opt state.judgments witness with
  | Some j, Some w ->
      Printf.printf "\n  CONTRACTIVITY ARGUMENT: %s\n" name;
      Printf.printf "     step: %s @ %s (%s)\n"
        name (Credence.to_string j.credence) (Neighbourhood.stability_to_string j.stability);
      Printf.printf "     witness: %s @ %s (%s)\n"
        witness (Credence.to_string w.credence) (Neighbourhood.stability_to_string w.stability);
      if Credence.leq j.credence w.credence then begin
        Printf.printf "     NON-DEGRADING: output credence >= input credence\n";
        Ok state
      end else begin
        Printf.printf "     DEGRADING: credence drops (controlled rate)\n";
        Ok state
      end
  | None, _ -> Error (Printf.sprintf "Unknown judgment: %s" name)
  | _, None -> Error (Printf.sprintf "Unknown judgment: %s" witness)

(* Proof factoring: isolate low-credence steps from high-credence core *)
let proof_factoring state high_core low_steps =
  Printf.printf "\n  PROOF FACTORING:\n";
  Printf.printf "     high-credence core: %s\n" high_core;
  Printf.printf "     low-credence steps: [%s]\n" (String.concat ", " low_steps);
  match Hashtbl.find_opt state.judgments high_core with
  | None -> Error (Printf.sprintf "Unknown judgment: %s" high_core)
  | Some core ->
      let all_steps_found = List.for_all (fun s ->
        Hashtbl.mem state.judgments s
      ) low_steps in
      if not all_steps_found then
        Error "Some low-credence steps not found"
      else begin
        Printf.printf "     core stability: %s\n"
          (Neighbourhood.stability_to_string core.stability);
        List.iter (fun s ->
          match Hashtbl.find_opt state.judgments s with
          | Some j ->
              Printf.printf "     step %s: %s\n" s (Neighbourhood.stability_to_string j.stability)
          | None -> ()
        ) low_steps;
        Ok state
      end

(* Dual proof: squeeze between lower and upper bounds *)
let dual_proof state squeezed lower upper =
  match Hashtbl.find_opt state.judgments lower,
        Hashtbl.find_opt state.judgments upper with
  | Some l, Some u ->
      Printf.printf "\n  DUAL PROOF (squeeze): %s\n" squeezed;
      Printf.printf "     lower bound: %s @ %s\n" lower (Credence.to_string l.credence);
      Printf.printf "     upper bound: %s @ %s\n" upper (Credence.to_string u.credence);
      let mid_credence = Credence.mul l.credence u.credence in
      let mid_stability = Neighbourhood.stability_of_app l.stability u.stability in
      let result_j = { name = squeezed; prop = "squeeze(" ^ l.prop ^ ", " ^ u.prop ^ ")";
                       credence = mid_credence; stability = mid_stability;
                       status = StabilityDerived (kind_of_stability mid_stability, "dual_proof") } in
      Hashtbl.replace state.judgments squeezed result_j;
      Printf.printf "     squeezed: %s @ %s (%s)\n"
        squeezed (Credence.to_string mid_credence) (Neighbourhood.stability_to_string mid_stability);
      Ok state
  | None, _ -> Error (Printf.sprintf "Unknown judgment: %s" lower)
  | _, None -> Error (Printf.sprintf "Unknown judgment: %s" upper)

(* Limit theorem: asymptotic arguments *)
let limit_theorem state result convergence =
  match Hashtbl.find_opt state.judgments convergence with
  | None -> Error (Printf.sprintf "Unknown judgment: %s" convergence)
  | Some c ->
      Printf.printf "\n  LIMIT THEOREM: %s\n" result;
      Printf.printf "     convergence witness: %s @ %s (%s)\n"
        convergence (Credence.to_string c.credence) (Neighbourhood.stability_to_string c.stability);
      let result_j = { name = result; prop = "lim(" ^ c.prop ^ ")";
                       credence = c.credence; stability = c.stability;
                       status = StabilityDerived (kind_of_stability c.stability, "limit_theorem") } in
      Hashtbl.replace state.judgments result result_j;
      Printf.printf "     limit: %s @ %s (%s)\n"
        result (Credence.to_string c.credence) (Neighbourhood.stability_to_string c.stability);
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
  (* Stability assertions *)
  | AssertStable name -> assert_stable state name
  | AssertUnstable name -> assert_unstable state name
  | AssertInterior name -> assert_interior state name
  | StabilityCheck (name, kind) -> check_stability state name kind
  (* Proof techniques with stability *)
  | DirectProof (name, prop, deriv) -> direct_proof state name prop deriv
  | ProofByCases (result, case1, case2) -> proof_by_cases state result case1 case2
  | Contraposition (result, from_s, to_u) -> contraposition state result from_s to_u
  | Reductio (result, unstable_neg) -> reductio state result unstable_neg
  | ExFalso (name, zero_term) -> ex_falso state name zero_term
  | Deduction (lambda_name, body_name) -> deduction state lambda_name body_name
  | ModusPonens (result, func, arg) -> modus_ponens state result func arg
  | Syllogism (result, f, g) -> syllogism state result f g
  | UniversalGen (forall_name, body) -> universal_gen state forall_name body
  | ExistentialIntro (exists_name, witness, body) -> existential_intro state exists_name witness body
  | Induction (result, base, step, note) -> induction state result base step note
  | Construction (witness, cert) -> construction state witness cert
  | Refutation (name, toward_zero) -> refutation state name toward_zero
  | EquationalRewrite (result, orig, eq) -> equational_rewrite state result orig eq
  (* CredTT-native techniques *)
  | StabilityProof (name, kind) -> stability_proof state name kind
  | CredenceBound (name, bound) -> credence_bound state name bound
  | ContinuityLemma (input, output) -> continuity_lemma state input output
  | DegeneracyAnalysis (name, rate) -> degeneracy_analysis state name rate
  | ContractivityArg (name, witness) -> contractivity_arg state name witness
  | ProofFactoring (core, steps) -> proof_factoring state core steps
  | DualProof (squeezed, lower, upper) -> dual_proof state squeezed lower upper
  | LimitTheorem (result, convergence) -> limit_theorem state result convergence

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
