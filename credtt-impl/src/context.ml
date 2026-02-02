(* Context operations following agda/CredTT/Context.agda
   Extended to track credences for each binding.
   Variables are introduced with credences via extend_with_credence.
   Default extend uses credence 1 for backwards compatibility. *)

open Syntax
open Subst

(* Each binding stores type and credence *)
type binding = { ty : ty; credence : Credence.t }
type t = binding list

let empty : t = []

(* Extend context with type and credence *)
let extend_with_credence (ctx : t) (ty : ty) (credence : Credence.t) : t =
  { ty; credence } :: ctx

(* Backwards-compatible extend: uses credence 1 *)
let extend (ctx : t) (ty : ty) : t =
  extend_with_credence ctx ty Credence.one

(* Lookup returns both type and credence *)
let lookup (ctx : t) (i : int) : (ty * Credence.t) option =
  let rec go ctx i acc =
    match ctx with
    | [] -> None
    | { ty; credence } :: rest ->
        if i = 0 then
          let rec wk_n ty n =
            if n = 0 then ty else wk_n (wk_ty ty) (n - 1)
          in
          Some (wk_n ty (acc + 1), credence)
        else go rest (i - 1) (acc + 1)
  in
  go ctx i 0

let length (ctx : t) : int = List.length ctx

let pp fmt ctx =
  let rec go i = function
    | [] -> ()
    | { ty; credence } :: rest ->
        Format.fprintf fmt "  v%d : %a @ %a@." i pp_ty ty Credence.pp credence;
        go (i + 1) rest
  in
  Format.fprintf fmt "Context:@.";
  go 0 (List.rev ctx)
