(* Credence algebra: Product De Morgan
   Minimal structure: 0, 1, *, negation, order
   No addition - disjunction derived via De Morgan duality *)

type t =
  | Zero
  | One
  | Rat of int * int  (* numerator, denominator - proper rational representation *)
  | Mul of t * t
  | Neg of t
  | Var of string
  | Infer of int  (* inference variable, assigned during unification *)
  | DepVar of string * int  (* dependent credence: c(x) where x is variable at de Bruijn index *)
  | Sup of string * t       (* supremum over bound variable: sup x. c(x) *)
  | Inf of string * t       (* infimum over bound variable: inf x. c(x) *)

let zero = Zero
let one = One
let rat n d = Rat (n, d)
let mul w v = Mul (w, v)
let neg w = Neg w
let var s = Var s
let dep_var x i = DepVar (x, i)
let sup x w = Sup (x, w)
let inf x w = Inf (x, w)

(* Inference variable generation *)
let infer_counter = ref 0
let fresh_infer () =
  let n = !infer_counter in
  incr infer_counter;
  Infer n

let reset_infer () = infer_counter := 0

let c_or c v = Neg (Mul (Neg c, Neg v))

(* GCD for simplifying rationals *)
let rec gcd_int a b = if b = 0 then abs a else gcd_int b (a mod b)

(* Simplify Rat to canonical form, converting 0/d to Zero and n/n to One *)
let simplify_rat n d =
  if d = 0 then invalid_arg "simplify_rat: denominator is zero"
  else if n = 0 then Zero
  else
    let g = gcd_int n d in
    let n' = n / g in
    let d' = d / g in
    (* Normalize sign to denominator *)
    let (n'', d'') = if d' < 0 then (-n', -d') else (n', d') in
    if n'' = 0 then Zero
    else if n'' = d'' then One
    else Rat (n'', d'')

let rec simplify = function
  | Mul (One, w) -> simplify w
  | Mul (w, One) -> simplify w
  | Mul (Zero, _) -> Zero
  | Mul (_, Zero) -> Zero
  | Neg (Neg w) -> simplify w
  | Neg Zero -> One
  | Neg One -> Zero
  | Rat (n, d) -> simplify_rat n d
  | Mul (w, v) ->
      let w' = simplify w in
      let v' = simplify v in
      (match w', v' with
       | Zero, _ | _, Zero -> Zero
       | One, x | x, One -> x
       | Rat (n1, d1), Rat (n2, d2) -> simplify_rat (n1 * n2) (d1 * d2)
       | _, _ -> Mul (w', v'))
  | Neg w ->
      let w' = simplify w in
      (match w' with
       | Zero -> One
       | One -> Zero
       | Neg w'' -> w''
       | Rat (n, d) -> simplify_rat (d - n) d  (* 1 - n/d = (d-n)/d *)
       | _ -> Neg w')
  | Infer n -> Infer n
  | DepVar (x, i) -> DepVar (x, i)
  | Sup (x, w) ->
      let w' = simplify w in
      (match w' with
       | Zero -> Zero            (* sup(x. 0) = 0 *)
       | One -> One              (* sup(x. 1) = 1 *)
       | _ -> Sup (x, w'))
  | Inf (x, w) ->
      let w' = simplify w in
      (match w' with
       | Zero -> Zero            (* inf(x. 0) = 0 *)
       | One -> One              (* inf(x. 1) = 1 *)
       | _ -> Inf (x, w'))
  | w -> w

let rec equal w1 w2 =
  match simplify w1, simplify w2 with
  | Zero, Zero -> true
  | One, One -> true
  | Rat (n1, d1), Rat (n2, d2) -> n1 * d2 = n2 * d1  (* cross-multiply to compare *)
  | Var s1, Var s2 -> s1 = s2
  | Infer n1, Infer n2 -> n1 = n2
  | DepVar (x1, i1), DepVar (x2, i2) -> x1 = x2 && i1 = i2
  | Sup (x1, w1'), Sup (x2, w2') -> x1 = x2 && equal w1' w2'
  | Inf (x1, w1'), Inf (x2, w2') -> x1 = x2 && equal w1' w2'
  | Mul (a1, b1), Mul (a2, b2) -> equal a1 a2 && equal b1 b2
  | Neg w1', Neg w2' -> equal w1' w2'
  | _, _ -> false

let leq w1 w2 =
  match simplify w1, simplify w2 with
  | Zero, _ -> true
  | _, One -> true
  | Rat (n1, d1), Rat (n2, d2) -> n1 * d2 <= n2 * d1  (* compare by cross-multiply *)
  | w1', w2' -> equal w1' w2'

let rec pp fmt = function
  | Zero -> Format.fprintf fmt "0"
  | One -> Format.fprintf fmt "1"
  | Rat (n, d) -> Format.fprintf fmt "%d/%d" n d
  | Var s -> Format.fprintf fmt "%s" s
  | Infer n -> Format.fprintf fmt "?%d" n
  | DepVar (x, i) -> Format.fprintf fmt "%s(%d)" x i
  | Sup (x, w) -> Format.fprintf fmt "sup(%s. %a)" x pp w
  | Inf (x, w) -> Format.fprintf fmt "inf(%s. %a)" x pp w
  | Mul (w, v) -> Format.fprintf fmt "(%a * %a)" pp w pp v
  | Neg w -> Format.fprintf fmt "(1 - %a)" pp w

let to_string w =
  let buf = Buffer.create 16 in
  let fmt = Format.formatter_of_buffer buf in
  pp fmt w;
  Format.pp_print_flush fmt ();
  Buffer.contents buf

(* Rational credence representation for exact computation *)
type rational = { num: int; den: int }

let gcd a b =
  let rec go a b = if b = 0 then a else go b (a mod b) in
  go (abs a) (abs b)

let rat_normalize r =
  if r.den = 0 then invalid_arg "rat_normalize: denominator is zero"
  else
    let g = gcd r.num r.den in
    let sign = if r.den < 0 then -1 else 1 in
    { num = sign * r.num / g; den = sign * r.den / g }

let rat_zero = { num = 0; den = 1 }
let rat_one = { num = 1; den = 1 }
let rat_half = { num = 1; den = 2 }

let rat_mul a b = rat_normalize { num = a.num * b.num; den = a.den * b.den }
let rat_neg a = rat_normalize { num = a.den - a.num; den = a.den }
let rat_equal a b =
  let a' = rat_normalize a in
  let b' = rat_normalize b in
  a'.num = b'.num && a'.den = b'.den

let rat_to_string r =
  let r' = rat_normalize r in
  if r'.den = 1 then string_of_int r'.num
  else Printf.sprintf "%d/%d" r'.num r'.den

(* Try to evaluate credence to rational *)
let rec to_rational = function
  | Zero -> Some rat_zero
  | One -> Some rat_one
  | Rat (n, d) -> Some (rat_normalize { num = n; den = d })
  | Neg w ->
      (match to_rational w with
       | Some r -> Some (rat_neg r)
       | None -> None)
  | Mul (a, b) ->
      (match to_rational a, to_rational b with
       | Some ra, Some rb -> Some (rat_mul ra rb)
       | _, _ -> None)
  | Var _ -> None
  | Infer _ -> None
  | DepVar _ -> None
  | Sup (_, w) ->
      (* sup(x. w) = w only if w is constant (doesn't depend on bound var)
         LIMITATION (Issue #116): We don't check variable dependency here.
         For now, we optimistically assume constant body. A full implementation
         would check depends_on_var and return None for dependent bodies. *)
      to_rational w
  | Inf (_, w) ->
      (* inf(x. w) = w only if w is constant (doesn't depend on bound var)
         LIMITATION (Issue #116): See Sup comment above. *)
      to_rational w

(* Solve c = ¬c for fixed point
   ¬c = 1 - c, so c = 1 - c implies 2c = 1, c = 1/2 *)
let solve_negation_fixpoint () = rat_half

(* Fixpoint solver result type *)
type fixpoint_result =
  | FPSolved of rational           (* unique solution found *)
  | FPMultiple of rational list    (* multiple solutions (e.g., c = c*c has 0 and 1) *)
  | FPIdentity                     (* c = c, always true, not a constraint *)
  | FPUnsolvable of string         (* cannot solve, with reason *)

(* General fixed point detection: given f(c), find c where c = f(c)
   Extended solver handling:
   - c = ¬c -> c = 1/2
   - c = c·c -> c in {0, 1}
   - c = c·k for constant k -> c = 0 (if k <> 1) or identity (if k = 1)
   - c = ¬¬c -> identity (by involution)
   - Other patterns -> unsolvable with error *)
let solve_fixpoint_ext f_of_c c =
  let simplified = simplify (f_of_c (Var c)) in
  match simplified with
  (* c = ¬c -> c = 1/2 *)
  | Neg (Var v) when v = c ->
      FPSolved rat_half

  (* c = c·c -> c = 0 or c = 1 (idempotent case)
     We prefer the non-trivial solution (1) first *)
  | Mul (Var v1, Var v2) when v1 = c && v2 = c ->
      FPMultiple [rat_one; rat_zero]

  (* c = c·k for constant k *)
  | Mul (Var v, k) when v = c ->
      (match to_rational k with
       | Some rk when rat_equal rk rat_one ->
           (* c = c·1 is identity *)
           FPIdentity
       | Some _ ->
           (* c = c·k with k <> 1 implies c = 0
              Proof: c = c·k implies c·(1-k) = 0, and if k <> 1 then c = 0 *)
           FPSolved rat_zero
       | None ->
           FPUnsolvable (Printf.sprintf "c = c * %s: cannot solve with symbolic constant" (to_string k)))

  (* c = k·c for constant k (symmetric case) *)
  | Mul (k, Var v) when v = c ->
      (match to_rational k with
       | Some rk when rat_equal rk rat_one ->
           FPIdentity
       | Some _ ->
           FPSolved rat_zero
       | None ->
           FPUnsolvable (Printf.sprintf "c = %s * c: cannot solve with symbolic constant" (to_string k)))

  (* c = ¬¬c is identity by involution *)
  | Neg (Neg (Var v)) when v = c ->
      FPIdentity

  (* c = c is identity (trivial) *)
  | Var v when v = c ->
      FPIdentity

  | _ ->
      (* Check if it simplifies to identity *)
      if equal simplified (Var c) then FPIdentity
      else FPUnsolvable (Printf.sprintf "Cannot solve c = %s" (to_string simplified))

(* Legacy wrapper returning Option for backward compatibility *)
let solve_fixpoint f_of_c c =
  match solve_fixpoint_ext f_of_c c with
  | FPSolved r -> Some r
  | FPMultiple (r :: _) -> Some r  (* return first solution for compatibility *)
  | FPMultiple [] -> None          (* shouldn't happen *)
  | FPIdentity -> None             (* identity is not a constraint *)
  | FPUnsolvable _ -> None         (* error case returns None for legacy code *)

(* Constraint system for credence solving *)
type constraint_t =
  | CEqual of t * t
  | CLeq of t * t
  | CFixpoint of string * (t -> t)

(* Union-Find for variable unification (Issue #51) *)
module UnionFind = struct
  type uf = {
    parent : (string, string) Hashtbl.t;
    rank : (string, int) Hashtbl.t;
  }

  let create () = { parent = Hashtbl.create 16; rank = Hashtbl.create 16 }

  let rec find uf x =
    match Hashtbl.find_opt uf.parent x with
    | None -> x
    | Some p ->
        let root = find uf p in
        if root <> p then Hashtbl.replace uf.parent x root;
        root

  let union uf x y =
    let rx = find uf x in
    let ry = find uf y in
    if rx <> ry then begin
      let rank_x = Option.value ~default:0 (Hashtbl.find_opt uf.rank rx) in
      let rank_y = Option.value ~default:0 (Hashtbl.find_opt uf.rank ry) in
      if rank_x < rank_y then
        Hashtbl.replace uf.parent rx ry
      else if rank_x > rank_y then
        Hashtbl.replace uf.parent ry rx
      else begin
        Hashtbl.replace uf.parent ry rx;
        Hashtbl.replace uf.rank rx (rank_x + 1)
      end
    end
end

(* Constraint solver result *)
type solve_result = {
  bindings : (string * rational) list;
  unsolved_leq : (t * t) list;  (* CLeq constraints that could not be resolved *)
  conflicts : (string * rational * rational) list;  (* Variables with conflicting assignments *)
}

(* Solve a list of constraints, returning variable assignments (Issue #51)
   Handles:
   - CEqual (Var v, Zero/One): direct assignment
   - CEqual (Var v, Rat): direct assignment
   - CEqual (Var v1, Var v2): variable unification
   - CLeq: constraint propagation for bounds
   - CFixpoint: fixpoint solving *)
let solve_constraints_ext constraints =
  let uf = UnionFind.create () in
  let bindings = Hashtbl.create 8 in
  let leq_constraints = ref [] in

  (* First pass: handle equalities and unification *)
  List.iter (function
    | CEqual (Var v, Zero) | CEqual (Zero, Var v) ->
        Hashtbl.replace bindings v rat_zero
    | CEqual (Var v, One) | CEqual (One, Var v) ->
        Hashtbl.replace bindings v rat_one
    | CEqual (Var v, Rat (n, d)) | CEqual (Rat (n, d), Var v) ->
        Hashtbl.replace bindings v (rat_normalize { num = n; den = d })
    | CEqual (Var v1, Var v2) when v1 <> v2 ->
        (* Unify two variables *)
        UnionFind.union uf v1 v2
    | CFixpoint (v, f) ->
        (match solve_fixpoint f v with
         | Some r -> Hashtbl.replace bindings v r
         | None -> ())
    | CLeq (w1, w2) ->
        leq_constraints := (w1, w2) :: !leq_constraints
    | _ -> ()
  ) constraints;

  (* Propagate bindings through union-find, tracking conflicts *)
  let propagated = Hashtbl.create 8 in
  let conflicts = ref [] in
  Hashtbl.iter (fun v r ->
    let root = UnionFind.find uf v in
    match Hashtbl.find_opt propagated root with
    | None -> Hashtbl.replace propagated root r
    | Some existing when rat_equal existing r -> ()
    | Some existing ->
        (* Record conflict: variable has two different values *)
        conflicts := (v, existing, r) :: !conflicts
  ) bindings;

  (* Assign same value to all unified variables *)
  let final_bindings = Hashtbl.create 8 in
  Hashtbl.iter (fun v _ ->
    let root = UnionFind.find uf v in
    match Hashtbl.find_opt propagated root with
    | Some r -> Hashtbl.replace final_bindings v r
    | None -> ()
  ) bindings;

  (* Also propagate to variables that were unified but not directly bound *)
  Hashtbl.iter (fun v _ ->
    let root = UnionFind.find uf v in
    if not (Hashtbl.mem final_bindings v) then
      match Hashtbl.find_opt propagated root with
      | Some r -> Hashtbl.replace final_bindings v r
      | None -> ()
  ) uf.parent;

  (* Process CLeq constraints: simple bound propagation *)
  let unsolved_leq = List.filter (fun (w1, w2) ->
    match simplify w1, simplify w2 with
    | Zero, _ -> false  (* 0 <= anything: trivially true *)
    | _, One -> false   (* anything <= 1: trivially true *)
    | Var v, Zero ->
        (* v <= 0 implies v = 0 *)
        Hashtbl.replace final_bindings v rat_zero;
        false
    | One, Var v ->
        (* 1 <= v implies v = 1 *)
        Hashtbl.replace final_bindings v rat_one;
        false
    | Rat (n1, d1), Rat (n2, d2) ->
        (* Keep unsatisfied constraints: n1/d1 > n2/d2 means constraint fails *)
        not (n1 * d2 <= n2 * d1)
    | _ -> true  (* Cannot resolve: keep as unsolved *)
  ) !leq_constraints in

  {
    bindings = Hashtbl.fold (fun k v acc -> (k, v) :: acc) final_bindings [];
    unsolved_leq;
    conflicts = !conflicts;
  }

(* Legacy wrapper for backward compatibility *)
let solve_constraints constraints =
  (solve_constraints_ext constraints).bindings

(* Create credence from rational *)
let of_rational r =
  let r' = rat_normalize r in
  if r'.num = 0 then Zero
  else if r'.num = r'.den then One
  else Rat (r'.num, r'.den)

(* Stability predicates - meta-level classification of credences *)

(* Check if credence is stable (robust): c = 1 exactly.

   IMPORTANT: NO THRESHOLDS. Stability is an algebraic property:
   - c = 1 is the unique maximal element, post-fixed under all operations
   - Symbolic stability requires algebraic analysis via Neighbourhood module

   For graded stability (post-fixed points), use Neighbourhood.classify *)
let is_stable_near_one (c : t) : bool =
  match simplify c with
  | One -> true
  | Zero -> false
  | Neg c' ->
      (* ¬c = 1 iff c = 0 *)
      (match simplify c' with
       | Zero -> true
       | _ -> false)
  | _ ->
      (* For symbolic/interior: cannot determine without dynamics analysis *)
      match to_rational (simplify c) with
      | Some r -> rat_equal r rat_one
      | None -> false

(* Check if credence is unstable (vanishing): c = 0 exactly.

   IMPORTANT: NO THRESHOLDS. Instability is an algebraic property:
   - c = 0 is the unique minimal element, absorbed by all operations
   - Symbolic instability requires algebraic analysis via Neighbourhood module

   For graded instability (degenerating sequences), use Neighbourhood.classify *)
let rec is_unstable_near_zero (c : t) : bool =
  match simplify c with
  | Zero -> true
  | One -> false
  | Neg c' ->
      (* ¬c = 0 iff c = 1 *)
      is_stable_near_one c'
  | Mul (a, b) ->
      (* Product = 0 if either factor = 0 *)
      is_unstable_near_zero a || is_unstable_near_zero b
  | _ ->
      match to_rational (simplify c) with
      | Some r -> rat_equal r rat_zero
      | None -> false

(* ========================================================================
   CREDENCE INFERENCE ENGINE
   ========================================================================
   Infers credences from term structure when not explicitly annotated.
   Uses unification with substitution to propagate constraints.
   ======================================================================== *)

(* Substitution: maps inference variables to credences *)
type subst = (int * t) list

let empty_subst : subst = []

let rec apply_subst (s : subst) (w : t) : t =
  match w with
  | Infer n ->
      (match List.assoc_opt n s with
       | Some w' -> apply_subst s w'
       | None -> Infer n)
  | Mul (a, b) -> simplify (Mul (apply_subst s a, apply_subst s b))
  | Neg w' -> simplify (Neg (apply_subst s w'))
  | Sup (x, w') -> Sup (x, apply_subst s w')
  | Inf (x, w') -> Inf (x, apply_subst s w')
  | _ -> w

(* Occurs check: does inference variable n occur in credence c? *)
let rec occurs (n : int) (w : t) : bool =
  match w with
  | Infer m -> n = m
  | Mul (a, b) -> occurs n a || occurs n b
  | Neg w' -> occurs n w'
  | Sup (_, w') -> occurs n w'
  | Inf (_, w') -> occurs n w'
  | _ -> false

(* Unification result *)
type unify_result =
  | Unified of subst
  | Failed of string
  | Fixpoint of int * (t -> t)  (* variable n satisfies n = f(n) *)

(* Substitution for named variables *)
type var_subst = (string * t) list

let empty_var_subst : var_subst = []

let apply_var_subst (vs : var_subst) (w : t) : t =
  let rec go = function
    | Var v ->
        (match List.assoc_opt v vs with
         | Some w' -> go w'
         | None -> Var v)
    | Mul (a, b) -> simplify (Mul (go a, go b))
    | Neg w' -> simplify (Neg (go w'))
    | Sup (x, w') -> Sup (x, go w')
    | Inf (x, w') -> Inf (x, go w')
    | w' -> w'
  in go w

(* Extended substitution: inference vars + named vars *)
type full_subst = {
  infer_bindings : subst;
  var_bindings : var_subst;
}

let empty_full_subst = { infer_bindings = []; var_bindings = [] }

let apply_full_subst (fs : full_subst) (w : t) : t =
  apply_var_subst fs.var_bindings (apply_subst fs.infer_bindings w)

(* Unify two credences, returning substitution or failure *)
let rec unify (s : subst) (w1 : t) (w2 : t) : unify_result =
  let w1' = apply_subst s w1 in
  let w2' = apply_subst s w2 in
  match simplify w1', simplify w2' with
  | Zero, Zero -> Unified s
  | One, One -> Unified s
  | Rat (n1, d1), Rat (n2, d2) when n1 * d2 = n2 * d1 -> Unified s
  | Var v1, Var v2 when v1 = v2 -> Unified s
  | Infer n1, Infer n2 when n1 = n2 -> Unified s

  (* Inference variable on left: bind if no occurs check failure *)
  | Infer n, w ->
      if occurs n w then
        (* Fixpoint: ?n = f(?n) for some f *)
        Fixpoint (n, fun x -> apply_subst [(n, x)] w)
      else
        Unified ((n, w) :: s)

  (* Inference variable on right: symmetric *)
  | w, Infer n ->
      if occurs n w then
        Fixpoint (n, fun x -> apply_subst [(n, x)] w)
      else
        Unified ((n, w) :: s)

  (* Named variable unification: treat as constraint c = value
     This records the constraint but doesn't "fail" unification *)
  | Var _, Zero -> Unified s  (* constraint noted elsewhere *)
  | Var _, One -> Unified s
  | Zero, Var _ -> Unified s
  | One, Var _ -> Unified s

  (* Structural unification *)
  | Mul (a1, b1), Mul (a2, b2) ->
      (match unify s a1 a2 with
       | Unified s' -> unify s' b1 b2
       | other -> other)

  | Neg w1'', Neg w2'' -> unify s w1'' w2''

  (* Named variables match if equal *)
  | Var v1, Var v2 when v1 = v2 -> Unified s

  (* Check structural equality after simplification *)
  | w1'', w2'' when equal w1'' w2'' -> Unified s

  | w1'', w2'' ->
      Failed (Printf.sprintf "Cannot unify %s with %s"
                (to_string w1'') (to_string w2''))

(* Inference context: accumulates constraints during type checking *)
type infer_ctx = {
  mutable constraints : (t * t) list;
  mutable fixpoints : (int * (t -> t)) list;
  mutable subst : subst;
}

let create_infer_ctx () = {
  constraints = [];
  fixpoints = [];
  subst = empty_subst;
}

(* Add a constraint w1 = w2 *)
let add_constraint ctx w1 w2 =
  ctx.constraints <- (w1, w2) :: ctx.constraints

(* Add a constraint that c should be zero (from contradiction) *)
let add_zero_constraint ctx w =
  add_constraint ctx w Zero

(* Solve all accumulated constraints *)
let solve_inference ctx =
  let rec go s = function
    | [] -> Ok s
    | (w1, w2) :: rest ->
        match unify s w1 w2 with
        | Unified s' -> go s' rest
        | Failed msg -> Error msg
        | Fixpoint (n, f) ->
            ctx.fixpoints <- (n, f) :: ctx.fixpoints;
            go s rest
  in
  match go ctx.subst ctx.constraints with
  | Ok s ->
      ctx.subst <- s;
      (* Solve fixpoints: ?n = f(?n) *)
      List.iter (fun (n, f) ->
        let solved = solve_fixpoint f (Printf.sprintf "?%d" n) in
        match solved with
        | Some r ->
            ctx.subst <- (n, of_rational r) :: ctx.subst
        | None -> ()
      ) ctx.fixpoints;
      Ok ctx.subst
  | Error msg -> Error msg

(* Apply solved substitution to get final credence *)
let finalize_credence ctx c =
  let c' = apply_subst ctx.subst c in
  simplify c'

(* Infer credence for a derivation chain.
   Given a sequence of derivation steps, propagate credences through.

   Derivation steps transform credences according to their semantics:
   - Preserving steps: algebra, substitution, etc. keep credence unchanged
   - Negation steps: compute complement (1 - c)
   - Weakening steps: may decrease credence (conservative: preserve)
   - Application requires two credences (handled in proof.ml's modus_ponens)

   For single-source derivations, most steps preserve credence since the
   transformation depends only on the source. Steps that genuinely transform
   a single credence (like negation) are handled explicitly. *)
let infer_derivation_credence ~from_credence ~(step : string) =
  match step with
  (* Preserving steps: logical equivalences, definitional steps *)
  (* NOTE: Contrapositive is a LOGICAL EQUIVALENCE (A->B iff ~B->~A), so it
     preserves credence. The negations happen to the propositions, not credences. *)
  | "algebra" | "substitution" | "both_even" | "self_reference"
  | "definition" | "assumption" | "trivial" | "identity" | "reflexivity"
  | "symmetry" | "congruence" | "rewrite" | "unfold" | "fold"
  | "contrapositive" ->
      from_credence

  (* Negation: c becomes 1-c (applies complement to the credence itself) *)
  | "negate" | "negation" | "complement" ->
      simplify (neg from_credence)

  (* Projection from pair: preserves credence (already joint) *)
  | "fst" | "snd" | "project" | "projection" ->
      from_credence

  (* Induction step: typically preserves base credence *)
  | "induction" | "inductive" ->
      from_credence

  (* Weakening: can only decrease credence, but without target we preserve *)
  | "weaken" | "weakening" ->
      from_credence

  (* Unknown step: preserve credence by default (conservative) *)
  | _ ->
      from_credence

(* Check if a credence has inference variables *)
let rec has_infer = function
  | Infer _ -> true
  | Mul (a, b) -> has_infer a || has_infer b
  | Neg w -> has_infer w
  | _ -> false

(* Collect all inference variables in a credence *)
let rec collect_infers acc = function
  | Infer n -> if List.mem n acc then acc else n :: acc
  | Mul (a, b) -> collect_infers (collect_infers acc a) b
  | Neg w -> collect_infers acc w
  | Sup (_, w) -> collect_infers acc w
  | Inf (_, w) -> collect_infers acc w
  | _ -> acc

(* Pretty print substitution *)
let pp_subst fmt s =
  List.iter (fun (n, w) ->
    Format.fprintf fmt "?%d = %a; " n pp w
  ) s

(* ========================================================================
   DEPENDENT CREDENCES
   ========================================================================
   Credences that depend on a bound variable:
     (x : A) -> B @ c(x)   means the credence varies with x

   Key rules:
   - Lambda: c(x) under binder becomes sup(x. c(x)) for the function
   - Apply: f a @ c(a) gets instantiated credence
   - Uniform case: sup(x. c) = inf(x. c) = c when c doesn't depend on x
   ======================================================================== *)

(* Check if credence depends on bound variable at index i *)
let rec depends_on_var (name : string) (w : t) : bool =
  match w with
  | DepVar (x, _) -> x = name
  | Mul (a, b) -> depends_on_var name a || depends_on_var name b
  | Neg w' -> depends_on_var name w'
  | Sup (x, w') -> x <> name && depends_on_var name w'
  | Inf (x, w') -> x <> name && depends_on_var name w'
  | _ -> false

(* Substitute a value for dependent variable *)
let rec subst_dep_var (name : string) (value : t) (w : t) : t =
  match w with
  | DepVar (x, _) when x = name -> value
  | Mul (a, b) -> simplify (Mul (subst_dep_var name value a, subst_dep_var name value b))
  | Neg w' -> simplify (Neg (subst_dep_var name value w'))
  | Sup (x, w') when x <> name -> Sup (x, subst_dep_var name value w')
  | Inf (x, w') when x <> name -> Inf (x, subst_dep_var name value w')
  | _ -> w

(* Construct dependent Pi credence: given body credence, form sup *)
let dependent_pi_credence (var_name : string) (body_credence : t) : t =
  if depends_on_var var_name body_credence then
    Sup (var_name, body_credence)
  else
    body_credence  (* constant case: sup(x. c) = c *)

(* Instantiate dependent credence at application *)
let instantiate_dep_credence (pi_credence : t) (arg_value_name : string) : t =
  match pi_credence with
  | Sup (x, c) -> subst_dep_var x (Var arg_value_name) c
  | _ -> pi_credence  (* not a dependent credence *)
