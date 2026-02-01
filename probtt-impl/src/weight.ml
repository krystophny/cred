(* Weight algebra: Product De Morgan
   Minimal structure: 0, 1, *, negation, order
   No addition - disjunction derived via De Morgan duality *)

type t =
  | Zero
  | One
  | Mul of t * t
  | Neg of t
  | Var of string

let zero = Zero
let one = One
let mul w v = Mul (w, v)
let neg w = Neg w
let var s = Var s

let w_or w v = Neg (Mul (Neg w, Neg v))

let rec simplify = function
  | Mul (One, w) -> simplify w
  | Mul (w, One) -> simplify w
  | Mul (Zero, _) -> Zero
  | Mul (_, Zero) -> Zero
  | Neg (Neg w) -> simplify w
  | Neg Zero -> One
  | Neg One -> Zero
  | Mul (w, v) ->
      let w' = simplify w in
      let v' = simplify v in
      if w' = Zero || v' = Zero then Zero
      else if w' = One then v'
      else if v' = One then w'
      else Mul (w', v')
  | Neg w ->
      let w' = simplify w in
      (match w' with
       | Zero -> One
       | One -> Zero
       | Neg w'' -> w''
       | _ -> Neg w')
  | w -> w

let rec equal w1 w2 =
  match simplify w1, simplify w2 with
  | Zero, Zero -> true
  | One, One -> true
  | Var s1, Var s2 -> s1 = s2
  | Mul (a1, b1), Mul (a2, b2) -> equal a1 a2 && equal b1 b2
  | Neg w1', Neg w2' -> equal w1' w2'
  | _, _ -> false

let leq w1 w2 =
  match simplify w1, simplify w2 with
  | Zero, _ -> true
  | _, One -> true
  | w1', w2' -> equal w1' w2'

let rec pp fmt = function
  | Zero -> Format.fprintf fmt "0"
  | One -> Format.fprintf fmt "1"
  | Var s -> Format.fprintf fmt "%s" s
  | Mul (w, v) -> Format.fprintf fmt "(%a * %a)" pp w pp v
  | Neg w -> Format.fprintf fmt "(1 - %a)" pp w

let to_string w =
  let buf = Buffer.create 16 in
  let fmt = Format.formatter_of_buffer buf in
  pp fmt w;
  Format.pp_print_flush fmt ();
  Buffer.contents buf

(* Rational weight representation for exact computation *)
type rational = { num: int; den: int }

let gcd a b =
  let rec go a b = if b = 0 then a else go b (a mod b) in
  go (abs a) (abs b)

let rat_normalize r =
  if r.den = 0 then { num = 0; den = 1 }
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

(* Try to evaluate weight to rational *)
let rec to_rational = function
  | Zero -> Some rat_zero
  | One -> Some rat_one
  | Neg w ->
      (match to_rational w with
       | Some r -> Some (rat_neg r)
       | None -> None)
  | Mul (a, b) ->
      (match to_rational a, to_rational b with
       | Some ra, Some rb -> Some (rat_mul ra rb)
       | _, _ -> None)
  | Var _ -> None

(* Solve w = ¬w for fixed point
   ¬w = 1 - w, so w = 1 - w implies 2w = 1, w = 1/2 *)
let solve_negation_fixpoint () = rat_half

(* General fixed point detection: given f(w), find w where w = f(w)
   For w = ¬w: solution is 1/2
   For w = w·w: solutions are 0 and 1 *)
let solve_fixpoint f_of_w w =
  let simplified = simplify (f_of_w (Var w)) in
  match simplified with
  | Neg (Var v) when v = w ->
      (* w = ¬w → w = 1/2 *)
      Some rat_half
  | Mul (Var v1, Var v2) when v1 = w && v2 = w ->
      (* w = w·w → w = 0 or w = 1 *)
      Some rat_one
  | _ ->
      (* Check if it's the identity: w = w *)
      if equal simplified (Var w) then None
      else None

(* Constraint system for weight solving *)
type constraint_t =
  | CEqual of t * t
  | CLeq of t * t
  | CFixpoint of string * (t -> t)

(* Solve a list of constraints, returning variable assignments *)
let solve_constraints constraints =
  let bindings = Hashtbl.create 8 in
  List.iter (function
    | CEqual (Var v, Zero) | CEqual (Zero, Var v) ->
        Hashtbl.replace bindings v rat_zero
    | CEqual (Var v, One) | CEqual (One, Var v) ->
        Hashtbl.replace bindings v rat_one
    | CFixpoint (v, f) ->
        (match solve_fixpoint f v with
         | Some r -> Hashtbl.replace bindings v r
         | None -> ())
    | _ -> ()
  ) constraints;
  Hashtbl.fold (fun k v acc -> (k, v) :: acc) bindings []

(* Create weight from rational *)
let of_rational r =
  let r' = rat_normalize r in
  if r'.num = 0 then Zero
  else if r'.num = r'.den then One
  else Var (rat_to_string r')
