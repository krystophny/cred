(* Error types and formatting *)

open Syntax

type t =
  | UnboundVariable of int
  | TypeMismatch of { expected : ty; actual : ty }
  | NotAFunction of ty
  | NotAPair of ty
  | NotASum of ty
  | NotAnIdentity of ty
  | NotEmpty of ty
  | CannotInfer of term
  | WeightNotLeq of Weight.t * Weight.t
  | IdEndpointsNotEqual of term * term
  | ParseError of string
  | FileNotFound of string

let pp fmt = function
  | UnboundVariable i ->
      Format.fprintf fmt "Unbound variable: v%d" i
  | TypeMismatch { expected; actual } ->
      Format.fprintf fmt "Type mismatch:@.  Expected: %a@.  Actual:   %a"
        pp_ty expected pp_ty actual
  | NotAFunction ty ->
      Format.fprintf fmt "Expected function type, got: %a" pp_ty ty
  | NotAPair ty ->
      Format.fprintf fmt "Expected pair type, got: %a" pp_ty ty
  | NotASum ty ->
      Format.fprintf fmt "Expected sum type, got: %a" pp_ty ty
  | NotAnIdentity ty ->
      Format.fprintf fmt "Expected identity type, got: %a" pp_ty ty
  | NotEmpty ty ->
      Format.fprintf fmt "Expected empty type, got: %a" pp_ty ty
  | CannotInfer t ->
      Format.fprintf fmt "Cannot infer type for: %a" pp_term t
  | WeightNotLeq (w1, w2) ->
      Format.fprintf fmt "Weight %a is not <= %a" Weight.pp w1 Weight.pp w2
  | IdEndpointsNotEqual (t1, t2) ->
      Format.fprintf fmt "Identity endpoints not equal: %a vs %a"
        pp_term t1 pp_term t2
  | ParseError msg ->
      Format.fprintf fmt "Parse error: %s" msg
  | FileNotFound path ->
      Format.fprintf fmt "File not found: %s" path

let to_string err =
  let buf = Buffer.create 128 in
  let fmt = Format.formatter_of_buffer buf in
  pp fmt err;
  Format.pp_print_flush fmt ();
  Buffer.contents buf
