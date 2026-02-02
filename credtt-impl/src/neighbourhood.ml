(* Neighbourhood Semantics for CredTT

   Stability is a meta-property: we reason about whether inhabitation
   persists near credence extrema.

   - Stable₁: robust inhabitation near credence 1
   - Unstable₀: fragile inhabitation near credence 0
   - Interior: neither extreme

   Key insight: classical proof techniques become stability theorems.
   The {0,1} collapse makes neighbourhoods trivial (singletons). *)

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

(* Stability classification *)
type stability =
  | Stable1                         (* robust near 1 *)
  | Unstable0                       (* fragile near 0 *)
  | Interior                        (* neither extreme *)
  | Unknown                         (* cannot classify *)

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

(* Threshold for "near 1" and "near 0" classification *)
let stability_threshold = { Credence.num = 1; den = 10 }  (* 0.1 *)

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

(* Classify stability of a credence *)
let rec classify (c : Credence.t) : stability =
  match Credence.to_rational c with
  | Some r ->
      let one_minus_threshold = Credence.rat_normalize {
        num = stability_threshold.den - stability_threshold.num;
        den = stability_threshold.den
      } in
      if Credence.rat_equal r Credence.rat_one then
        Stable1
      else if Credence.rat_equal r Credence.rat_zero then
        Unstable0
      else if rat_geq r one_minus_threshold then
        Stable1  (* near 1 *)
      else if rat_leq r stability_threshold then
        Unstable0  (* near 0 *)
      else
        Interior
  | None ->
      (* Symbolic credence: try to classify structurally *)
      match Credence.simplify c with
      | Credence.One -> Stable1
      | Credence.Zero -> Unstable0
      | Credence.Neg c' ->
          (* Negation flips stability *)
          (match classify c' with
           | Stable1 -> Unstable0
           | Unstable0 -> Stable1
           | other -> other)
      | Credence.Mul (a, b) ->
          (* Product: stable * stable = stable, anything with unstable = unstable *)
          (match classify a, classify b with
           | Stable1, Stable1 -> Stable1
           | Unstable0, _ | _, Unstable0 -> Unstable0
           | _, _ -> Unknown)
      | _ -> Unknown

(* Classify stability from a neighbourhood *)
let classify_neighbourhood (n : t) : stability =
  match n with
  | Point r ->
      if Credence.rat_equal r Credence.rat_one then Stable1
      else if Credence.rat_equal r Credence.rat_zero then Unstable0
      else
        let one_minus_threshold = Credence.rat_normalize {
          num = stability_threshold.den - stability_threshold.num;
          den = stability_threshold.den
        } in
        if rat_geq r one_minus_threshold then Stable1
        else if rat_leq r stability_threshold then Unstable0
        else Interior
  | Interval { lo; hi; _ } ->
      let one_minus_threshold = Credence.rat_normalize {
        num = stability_threshold.den - stability_threshold.num;
        den = stability_threshold.den
      } in
      if rat_geq lo one_minus_threshold then Stable1
      else if rat_leq hi stability_threshold then Unstable0
      else Interior
  | Full -> Unknown
  | Empty -> Unstable0  (* empty neighbourhood is degenerate *)

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
           (* Determine order (f might be order-reversing like negation) *)
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
      (* Compute intersection of intervals *)
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

(* Union of two neighbourhoods (returns smallest containing neighbourhood) *)
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

(* Stability propagation through type rules *)

(* Application: f @ c1, a @ c2 -> f a @ c1 * c2
   Stable * Stable = Stable *)
let stability_of_app (s1 : stability) (s2 : stability) : stability =
  match s1, s2 with
  | Stable1, Stable1 -> Stable1
  | Unstable0, _ | _, Unstable0 -> Unstable0
  | Unknown, _ | _, Unknown -> Unknown
  | Interior, _ | _, Interior -> Interior

(* Negation: flips stability *)
let stability_of_neg (s : stability) : stability =
  match s with
  | Stable1 -> Unstable0
  | Unstable0 -> Stable1
  | other -> other

(* Composition: g . f preserves stability *)
let stability_of_compose (s1 : stability) (s2 : stability) : stability =
  stability_of_app s1 s2

(* Pi-intro: preserves stability if body is uniformly stable *)
let stability_of_pi_intro (body_stability : stability) : stability =
  body_stability

(* Sigma-elim: preserves stability (projections don't degrade) *)
let stability_of_sigma_elim (pair_stability : stability) : stability =
  pair_stability

(* Check if stability is robust (Stable1) *)
let is_stable (s : stability) : bool =
  match s with
  | Stable1 -> true
  | _ -> false

(* Check if stability is degenerate (Unstable0) *)
let is_unstable (s : stability) : bool =
  match s with
  | Unstable0 -> true
  | _ -> false

(* Pretty printing *)
let pp_stability fmt = function
  | Stable1 -> Format.fprintf fmt "Stable₁"
  | Unstable0 -> Format.fprintf fmt "Unstable₀"
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
  | Empty -> Format.fprintf fmt "∅"

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
