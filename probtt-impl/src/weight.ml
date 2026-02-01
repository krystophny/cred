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
