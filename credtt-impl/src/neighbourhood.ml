(* Neighbourhood Semantics for CredTT

   Stability is a META-PROPERTY defined via ORDER-THEORETIC DYNAMICS,
   not by equality to endpoints.

   FUNDAMENTAL PRINCIPLE (corrected):
   Stability = non-vanishing under directed iteration

   NOT "c = 1 exactly"
   BUT "infₙ (c · sⁿ) > 0"

   This uses only:
   - Order (≤, >)
   - Multiplication (·)
   - Infimum of descending chains

   NO METRICS. NO ε. NO SUBTRACTION. NO EQUALITY TO 1.

   KEY INSIGHT (non-Archimedean algebras):
   In a general De Morgan algebra, s < 1 does NOT imply sⁿ → 0.
   There can be:
   - Idempotents: c · s = c with 0 < c < 1
   - Plateaus: c stabilizes at non-zero value
   - Fixed points in the interior

   This gives GENUINE STABILITY IN THE INTERIOR - not just {0, 1}!

   CredTT does NOT say "only 0 and 1 matter".
   It says: stability is about FIXED POINTS OF THE DYNAMICS,
   not endpoints of the order. *)

(* Interval representation for credence neighbourhoods *)
type interval = {
  lo: Credence.rational;
  hi: Credence.rational;
  lo_closed: bool;
  hi_closed: bool;
}

(* Neighbourhood types *)
type t =
  | Point of Credence.rational      (* singleton {c} *)
  | Interval of interval            (* (lo, hi) or variants *)
  | Full                            (* [0, 1] - completely unknown *)
  | Empty                           (* impossible/contradiction *)

(* ============================================================
   STABILITY CLASSIFICATION
   ============================================================

   Classification based on order-theoretic dynamics:
   - Robust: c = 1 exactly (maximal element, preserved under all operations)
   - Vanishing: c = 0 exactly (minimal element, absorbed by all operations)
   - Idempotent: c * c = c (only 0 and 1 for standard multiplication)
   - Interior: 0 < c < 1 (degenerates under iteration in Archimedean algebra)
   - Unknown: cannot determine from structure alone

   KEY INSIGHT: In standard [0,1] with multiplication, ONLY 0 and 1 are
   idempotent. Any interior point 0 < c < 1 satisfies c * c < c, meaning
   iteration c^n -> 0 as n -> infinity (Archimedean property). *)

type stability =
  | Robust          (* c = 1: maximal, preserved under multiplication *)
  | Vanishing       (* c = 0: minimal, absorbed by multiplication *)
  | Idempotent      (* c * c = c (only 0 and 1 for real multiplication) *)
  | Interior        (* 0 < c < 1: degenerates under iteration *)
  | Unknown         (* Cannot determine *)

(* For backwards compatibility with existing code *)
let stable1 = Robust
let unstable0 = Vanishing
let degenerate = Vanishing

(* ============================================================
   ALGEBRAIC ANALYSIS
   ============================================================

   We analyze credence expressions structurally to determine
   their dynamic behavior WITHOUT assuming Archimedeanicity. *)

(* Rational comparison helpers *)
let rat_lt a b =
  let a' = Credence.rat_normalize a in
  let b' = Credence.rat_normalize b in
  a'.num * b'.den < b'.num * a'.den

let rat_leq a b =
  let a' = Credence.rat_normalize a in
  let b' = Credence.rat_normalize b in
  a'.num * b'.den <= b'.num * a'.den

let rat_gt a b = rat_lt b a
let rat_geq a b = rat_leq b a

(* Create neighbourhood from a single credence value *)
let of_credence (c : Credence.t) : t =
  match Credence.to_rational c with
  | Some r -> Point r
  | None -> Full  (* symbolic credence -> unknown neighbourhood *)

(* Perturb a credence by epsilon to create an interval *)
let perturb (c : Credence.t) ~(epsilon : Credence.rational) : t =
  match Credence.to_rational c with
  | Some r ->
      let lo = Credence.rat_normalize {
        num = r.num * epsilon.den - epsilon.num * r.den;
        den = r.den * epsilon.den
      } in
      let hi = Credence.rat_normalize {
        num = r.num * epsilon.den + epsilon.num * r.den;
        den = r.den * epsilon.den
      } in
      (* Clamp to [0, 1] *)
      let lo' = if rat_lt lo Credence.rat_zero then Credence.rat_zero else lo in
      let hi' = if rat_gt hi Credence.rat_one then Credence.rat_one else hi in
      Interval { lo = lo'; hi = hi'; lo_closed = true; hi_closed = true }
  | None -> Full

(* Check if a credence is idempotent: c * c = c
   In standard [0,1] multiplication, only 0 and 1 are idempotent.
   For any 0 < c < 1: c * c < c (strictly decreases). *)
let is_idempotent (c : Credence.t) : bool =
  match Credence.simplify c with
  | Credence.One -> true      (* 1 * 1 = 1 *)
  | Credence.Zero -> true     (* 0 * 0 = 0 *)
  | _ ->
      match Credence.to_rational c with
      | Some r ->
          Credence.rat_equal r Credence.rat_zero ||
          Credence.rat_equal r Credence.rat_one
      | None -> false  (* symbolic: cannot determine *)

(* Check if credence is a post-fixed point under multiplication by s:
   c ≤ c · s (i.e., multiplication by s doesn't decrease c) *)
let is_post_fixed_point (c : Credence.t) (s : Credence.t) : bool =
  (* c ≤ c · s holds when s = 1 (trivially)
     or when c = 0 (trivially)
     For symbolic, we conservatively return false *)
  match Credence.simplify c, Credence.simplify s with
  | Credence.Zero, _ -> true          (* 0 ≤ 0 · anything *)
  | _, Credence.One -> true           (* c ≤ c · 1 = c *)
  | Credence.One, Credence.Zero -> false  (* 1 ≤ 0 is false *)
  | Credence.One, _ -> false          (* 1 ≤ 1 · s only if s = 1 *)
  | _ -> false                        (* conservative *)

(* ============================================================
   DYNAMIC STABILITY CLASSIFICATION
   ============================================================

   Classify based on dynamic behavior under iteration:
   - What happens to c · sⁿ as n → ∞?

   In NON-ARCHIMEDEAN algebras, this is NOT determined by
   whether s < 1 or s = 1!

   The key properties are:
   - Is c a fixed point? (c · c = c)
   - Is c absorbed by s? (c · s = c)
   - Does c strictly decrease under s? *)

(* Classify a credence based on its dynamic behavior.
   For concrete rationals, we can determine exactly.
   For symbolic expressions, we propagate through structure. *)
let rec classify (c : Credence.t) : stability =
  match Credence.simplify c with
  | Credence.One -> Robust      (* 1 is robust: preserved under any s <= 1 *)
  | Credence.Zero -> Vanishing  (* 0 is the vanishing point *)
  | Credence.Rat (_, _) -> Idempotent  (* interior rationals are idempotent *)
  | Credence.Neg inner ->
      (* Negation: ~c = 1 - c, swaps 0 <-> 1 at extremes, maps interior to interior *)
      (match classify inner with
       | Robust -> Vanishing     (* ~1 = 0 *)
       | Vanishing -> Robust     (* ~0 = 1 *)
       | Interior -> Interior    (* ~c for 0<c<1 gives 0<1-c<1 *)
       | Idempotent -> Idempotent
       | Unknown -> Unknown)
  | Credence.Mul (a, b) ->
      (* Product behavior: c1 * c2
         - 0 * x = 0 (absorbing)
         - 1 * x = x (identity)
         - interior * interior = interior (stays in (0,1)) *)
      (match classify a, classify b with
       | Vanishing, _ | _, Vanishing -> Vanishing  (* 0 * x = 0 *)
       | Robust, other | other, Robust -> other    (* 1 * x = x *)
       | Interior, Interior -> Interior            (* product of interiors is interior *)
       | Interior, Idempotent | Idempotent, Interior -> Interior
       | Idempotent, Idempotent -> Idempotent
       | Unknown, _ | _, Unknown -> Unknown)
  | Credence.Var _ -> Unknown
  | Credence.Infer _ -> Unknown
  | Credence.DepVar _ -> Unknown
  | Credence.Sup (_, body) ->
      (match classify body with
       | Robust -> Robust
       | Vanishing -> Vanishing
       | Interior -> Interior
       | s -> s)
  | Credence.Inf (_, body) ->
      (match classify body with
       | Robust -> Robust
       | Vanishing -> Vanishing
       | Interior -> Interior
       | s -> s)

(* Classify stability from a neighbourhood.
   KEY INSIGHT: Interior points 0 < c < 1 are NOT idempotent.
   Only 0 and 1 satisfy c * c = c for real multiplication. *)
let classify_neighbourhood (n : t) : stability =
  match n with
  | Point r ->
      if Credence.rat_equal r Credence.rat_one then Robust
      else if Credence.rat_equal r Credence.rat_zero then Vanishing
      else Interior  (* 0 < c < 1: degenerates under iteration *)
  | Interval { lo; hi; _ } ->
      if Credence.rat_equal lo Credence.rat_one &&
         Credence.rat_equal hi Credence.rat_one then Robust
      else if Credence.rat_equal lo Credence.rat_zero &&
              Credence.rat_equal hi Credence.rat_zero then Vanishing
      else if rat_gt lo Credence.rat_zero &&
              rat_lt hi Credence.rat_one then Interior  (* interval in (0,1) *)
      else if Credence.rat_equal lo Credence.rat_zero then
        if Credence.rat_equal hi Credence.rat_one then Unknown  (* full interval *)
        else Interior  (* [0, c) or [0, c] with c < 1 contains interior *)
      else if Credence.rat_equal hi Credence.rat_one then Interior  (* (c, 1] contains interior *)
      else Unknown
  | Full -> Unknown
  | Empty -> Vanishing

(* Propagate neighbourhood through a monotone function *)
let propagate (n : t) (f : Credence.t -> Credence.t) : t =
  match n with
  | Point r ->
      of_credence (f (Credence.of_rational r))
  | Interval { lo; hi; lo_closed; hi_closed } ->
      let f_lo = f (Credence.of_rational lo) in
      let f_hi = f (Credence.of_rational hi) in
      (match Credence.to_rational f_lo, Credence.to_rational f_hi with
       | Some r_lo, Some r_hi ->
           if rat_leq r_lo r_hi then
             Interval { lo = r_lo; hi = r_hi; lo_closed; hi_closed }
           else
             Interval { lo = r_hi; hi = r_lo; lo_closed = hi_closed; hi_closed = lo_closed }
       | _, _ -> Full)
  | Full -> Full
  | Empty -> Empty

(* Intersect two neighbourhoods *)
let intersect (n1 : t) (n2 : t) : t option =
  match n1, n2 with
  | Empty, _ | _, Empty -> Some Empty
  | Full, n | n, Full -> Some n
  | Point r1, Point r2 ->
      if Credence.rat_equal r1 r2 then Some (Point r1) else Some Empty
  | Point r, Interval { lo; hi; lo_closed; hi_closed }
  | Interval { lo; hi; lo_closed; hi_closed }, Point r ->
      let in_lo = if lo_closed then rat_geq r lo else rat_gt r lo in
      let in_hi = if hi_closed then rat_leq r hi else rat_lt r hi in
      if in_lo && in_hi then Some (Point r) else Some Empty
  | Interval i1, Interval i2 ->
      let new_lo, new_lo_closed =
        if rat_gt i1.lo i2.lo then (i1.lo, i1.lo_closed)
        else if rat_lt i1.lo i2.lo then (i2.lo, i2.lo_closed)
        else (i1.lo, i1.lo_closed && i2.lo_closed)
      in
      let new_hi, new_hi_closed =
        if rat_lt i1.hi i2.hi then (i1.hi, i1.hi_closed)
        else if rat_gt i1.hi i2.hi then (i2.hi, i2.hi_closed)
        else (i1.hi, i1.hi_closed && i2.hi_closed)
      in
      if rat_gt new_lo new_hi then Some Empty
      else if Credence.rat_equal new_lo new_hi then
        if new_lo_closed && new_hi_closed then Some (Point new_lo)
        else Some Empty
      else Some (Interval { lo = new_lo; hi = new_hi;
                            lo_closed = new_lo_closed; hi_closed = new_hi_closed })

(* Union of two neighbourhoods *)
let union (n1 : t) (n2 : t) : t =
  match n1, n2 with
  | Empty, n | n, Empty -> n
  | Full, _ | _, Full -> Full
  | Point r1, Point r2 ->
      if Credence.rat_equal r1 r2 then Point r1
      else Interval {
        lo = if rat_lt r1 r2 then r1 else r2;
        hi = if rat_gt r1 r2 then r1 else r2;
        lo_closed = true; hi_closed = true
      }
  | Point r, Interval i | Interval i, Point r ->
      let new_lo, new_lo_closed =
        if rat_lt r i.lo then (r, true)
        else (i.lo, i.lo_closed)
      in
      let new_hi, new_hi_closed =
        if rat_gt r i.hi then (r, true)
        else (i.hi, i.hi_closed)
      in
      Interval { lo = new_lo; hi = new_hi; lo_closed = new_lo_closed; hi_closed = new_hi_closed }
  | Interval i1, Interval i2 ->
      let new_lo, new_lo_closed =
        if rat_lt i1.lo i2.lo then (i1.lo, i1.lo_closed)
        else if rat_gt i1.lo i2.lo then (i2.lo, i2.lo_closed)
        else (i1.lo, i1.lo_closed || i2.lo_closed)
      in
      let new_hi, new_hi_closed =
        if rat_gt i1.hi i2.hi then (i1.hi, i1.hi_closed)
        else if rat_lt i1.hi i2.hi then (i2.hi, i2.hi_closed)
        else (i1.hi, i1.hi_closed || i2.hi_closed)
      in
      Interval { lo = new_lo; hi = new_hi; lo_closed = new_lo_closed; hi_closed = new_hi_closed }

(* ============================================================
   STABILITY PROPAGATION - ORDER-THEORETIC RULES
   ============================================================

   These rules follow from order theory:
   - Robust * Robust = Robust (1 * 1 = 1)
   - Vanishing * anything = Vanishing (0 * x = 0)
   - Interior * Interior = Interior (product of interior stays interior)
   - neg flips Robust <-> Vanishing, Interior stays Interior *)

let stability_of_app (s1 : stability) (s2 : stability) : stability =
  match s1, s2 with
  | Vanishing, _ | _, Vanishing -> Vanishing
  | Robust, other | other, Robust -> other
  | Interior, Interior -> Interior
  | Interior, Idempotent | Idempotent, Interior -> Interior
  | Idempotent, Idempotent -> Idempotent
  | Unknown, _ | _, Unknown -> Unknown

let stability_of_neg (s : stability) : stability =
  match s with
  | Robust -> Vanishing       (* ~1 = 0 *)
  | Vanishing -> Robust       (* ~0 = 1 *)
  | Interior -> Interior      (* ~c for 0<c<1 gives 0<1-c<1 *)
  | Idempotent -> Idempotent
  | Unknown -> Unknown

let stability_of_compose (s1 : stability) (s2 : stability) : stability =
  stability_of_app s1 s2

let stability_of_pi_intro (body_stability : stability) : stability =
  body_stability

let stability_of_sigma_elim (pair_stability : stability) : stability =
  pair_stability

(* ============================================================
   ITERATION AND CONVERGENCE
   ============================================================

   The key question: what is inf_n (c * s^n)?

   In ARCHIMEDEAN algebras (like real [0,1]):
   - 0 < s < 1 implies s^n -> 0 as n -> infinity
   - s = 1 implies s^n = 1
   - s = 0 implies s^n = 0 for n >= 1

   CredTT uses standard [0,1] multiplication which IS Archimedean.
   For any 0 < c < 1, c^n -> 0 as n -> infinity.

   This means:
   - c = 0: preserved (c * s^n = 0)
   - c = 1, s = 1: preserved (1 * 1^n = 1)
   - c = 1, 0 < s < 1: degenerates (1 * s^n -> 0)
   - 0 < c < 1: degenerates (c * s^n -> 0 for any s < 1) *)

type iteration_behavior =
  | Preserves          (* c * s^n = c for all n *)
  | Converges_nonzero  (* inf_n (c * s^n) > 0, but not constant *)
  | Degenerates        (* inf_n (c * s^n) = 0 *)
  | Unknown_limit      (* cannot determine *)

(* Analyze iteration behavior for concrete rational credences.
   Uses the Archimedean property of [0,1]: for 0 < r < 1, r^n -> 0.

   DESIGN NOTE: Returns Unknown_limit for symbolic credences (Var, Infer, DepVar).
   This is CORRECT behavior - we cannot determine iteration limits algebraically
   without knowing concrete values. Callers should handle Unknown_limit by:
   - Using conservative assumptions (treat as potentially degenerating)
   - Requesting user annotation for credence bounds
   - Propagating uncertainty to downstream analysis *)
let iteration_behavior (c : Credence.t) (s : Credence.t) : iteration_behavior =
  match Credence.simplify c, Credence.simplify s with
  | Credence.Zero, _ -> Preserves      (* 0 * s^n = 0 *)
  | _, Credence.One -> Preserves       (* c * 1^n = c *)
  | Credence.One, Credence.Zero -> Degenerates  (* 1 * 0^n = 0 for n > 0 *)
  | Credence.One, _ ->
      (* c = 1, s is something else *)
      (match Credence.to_rational s with
       | Some rs ->
           if Credence.rat_equal rs Credence.rat_one then Preserves
           else if Credence.rat_equal rs Credence.rat_zero then Degenerates
           else Degenerates  (* 1 * s^n -> 0 for 0 < s < 1 *)
       | None -> Unknown_limit)
  | _, Credence.Zero -> Degenerates    (* c * 0^n = 0 for n > 0, any c *)
  | _ ->
      (* Both c and s are non-trivial; check if we have rational values *)
      (match Credence.to_rational c, Credence.to_rational s with
       | Some rc, Some rs ->
           if Credence.rat_equal rc Credence.rat_zero then Preserves
           else if Credence.rat_equal rs Credence.rat_one then Preserves
           else if Credence.rat_equal rs Credence.rat_zero then Degenerates
           else
             (* 0 < c, s < 1: Archimedean property -> degenerates *)
             Degenerates
       | Some rc, None ->
           if Credence.rat_equal rc Credence.rat_zero then Preserves
           else Unknown_limit
       | None, Some rs ->
           if Credence.rat_equal rs Credence.rat_one then Preserves
           else if Credence.rat_equal rs Credence.rat_zero then Degenerates
           else Unknown_limit
       | None, None -> Unknown_limit)

(* Check if step is non-degrading: c · s ≥ c
   This is exactly when s is the identity for c *)
let is_non_degrading (s : Credence.t) : bool =
  match Credence.simplify s with
  | Credence.One -> true
  | _ -> false

(* Check if c is stable under s:
   "stable" means inf_n(c · sⁿ) > 0

   Conservative approximation: return true only when we can prove it *)
let is_stable_under (c : Credence.t) (s : Credence.t) : bool =
  match iteration_behavior c s with
  | Preserves -> classify c <> Vanishing
  | Converges_nonzero -> true
  | Degenerates -> false
  | Unknown_limit -> false  (* conservative *)

(* ============================================================
   BACKWARDS COMPATIBILITY
   ============================================================

   Legacy type alias for code that used old stability type *)

(* Old constructor names for pattern matching compatibility *)

let is_stable (s : stability) : bool =
  s = Robust

let is_unstable (s : stability) : bool =
  s = Vanishing

let is_interior (s : stability) : bool =
  s = Interior

let is_contractive (step_stability : stability) : bool =
  step_stability = Robust

(* ============================================================
   PRETTY PRINTING *)

let pp_stability fmt = function
  | Robust -> Format.fprintf fmt "Robust"
  | Vanishing -> Format.fprintf fmt "Vanishing"
  | Idempotent -> Format.fprintf fmt "Idempotent"
  | Interior -> Format.fprintf fmt "Interior"
  | Unknown -> Format.fprintf fmt "Unknown"

let pp_rational fmt r =
  let r' = Credence.rat_normalize r in
  if r'.den = 1 then Format.fprintf fmt "%d" r'.num
  else Format.fprintf fmt "%d/%d" r'.num r'.den

let pp fmt = function
  | Point r -> Format.fprintf fmt "{%a}" pp_rational r
  | Interval { lo; hi; lo_closed; hi_closed } ->
      Format.fprintf fmt "%c%a, %a%c"
        (if lo_closed then '[' else '(')
        pp_rational lo
        pp_rational hi
        (if hi_closed then ']' else ')')
  | Full -> Format.fprintf fmt "[0, 1]"
  | Empty -> Format.fprintf fmt "empty"

let to_string n =
  let buf = Buffer.create 16 in
  let fmt = Format.formatter_of_buffer buf in
  pp fmt n;
  Format.pp_print_flush fmt ();
  Buffer.contents buf

let stability_to_string s =
  let buf = Buffer.create 16 in
  let fmt = Format.formatter_of_buffer buf in
  pp_stability fmt s;
  Format.pp_print_flush fmt ();
  Buffer.contents buf

(* Credence-level predicates *)
let is_stable_near_one (c : Credence.t) : bool =
  classify c = Robust

let is_unstable_near_zero (c : Credence.t) : bool =
  classify c = Vanishing
