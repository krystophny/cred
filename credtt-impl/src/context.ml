(* Context operations following agda/CredTT/Context.agda *)

open Syntax
open Subst

type t = ty list

let empty : t = []

let extend (ctx : t) (ty : ty) : t = ty :: ctx

let lookup (ctx : t) (i : int) : ty option =
  let rec go ctx i acc =
    match ctx with
    | [] -> None
    | ty :: rest ->
        if i = 0 then
          let rec wk_n ty n =
            if n = 0 then ty else wk_n (wk_ty ty) (n - 1)
          in
          Some (wk_n ty (acc + 1))
        else go rest (i - 1) (acc + 1)
  in
  go ctx i 0

let length (ctx : t) : int = List.length ctx

let pp fmt ctx =
  let rec go i = function
    | [] -> ()
    | ty :: rest ->
        Format.fprintf fmt "  v%d : %a@." i pp_ty ty;
        go (i + 1) rest
  in
  Format.fprintf fmt "Context:@.";
  go 0 (List.rev ctx)
