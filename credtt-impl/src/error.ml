(* Error types and formatting *)

open Syntax

type t =
  | UnboundVariable of int
  | UnboundName of string  (* Issue #81: unbound variable by name during elaboration *)
  | TypeMismatch of { expected : ty; actual : ty }
  | NotAFunction of ty
  | NotAPair of ty
  | NotASum of ty
  | NotAnIdentity of ty
  | CannotInfer of term
  | CredenceNotLeq of Credence.t * Credence.t
  | IdEndpointsNotEqual of term * term
  | BranchCredenceMismatch of Credence.t * Credence.t
  | StabilityMismatch of { expected : string; actual : string }
  | StabilityRequired of string * string  (* name, required_stability *)
  | ParseError of string
  | FileNotFound of string
  | UnsupportedHole  (* Issue #56: holes are not properly supported *)
  | UnsupportedConstruct of string  (* Issue #59: placeholder for unsupported constructs *)
  | UnboundTypeName of string  (* Issue #79: unbound type name during elaboration *)

let pp fmt = function
  | UnboundVariable i ->
      Format.fprintf fmt "Unbound variable: v%d" i
  | UnboundName name ->
      Format.fprintf fmt "Unbound variable: %s" name
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
  | CannotInfer t ->
      Format.fprintf fmt "Cannot infer type for: %a" pp_term t
  | CredenceNotLeq (c1, c2) ->
      Format.fprintf fmt "Credence %a is not <= %a" Credence.pp c1 Credence.pp c2
  | IdEndpointsNotEqual (t1, t2) ->
      Format.fprintf fmt "Identity endpoints not equal: %a vs %a"
        pp_term t1 pp_term t2
  | BranchCredenceMismatch (c1, c2) ->
      Format.fprintf fmt "Case branches must have equal credences: left=%a, right=%a"
        Credence.pp c1 Credence.pp c2
  | StabilityMismatch { expected; actual } ->
      Format.fprintf fmt "Stability mismatch:@.  Expected: %s@.  Actual:   %s"
        expected actual
  | StabilityRequired (name, required) ->
      Format.fprintf fmt "Stability assertion failed for '%s': required %s" name required
  | ParseError msg ->
      Format.fprintf fmt "Parse error: %s" msg
  | FileNotFound path ->
      Format.fprintf fmt "File not found: %s" path
  | UnsupportedHole ->
      Format.fprintf fmt "Holes (?) are not supported in elaboration. Use explicit terms or type annotations."
  | UnsupportedConstruct what ->
      Format.fprintf fmt "Unsupported construct: %s" what
  | UnboundTypeName name ->
      Format.fprintf fmt "Unbound type name: %s" name

let to_string err =
  let buf = Buffer.create 128 in
  let fmt = Format.formatter_of_buffer buf in
  pp fmt err;
  Format.pp_print_flush fmt ();
  Buffer.contents buf
