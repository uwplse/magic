(*
 * Plugin basics
 * 
 * Note: In this example plugin, I don't ever update evd, the evar_map.
 * This is OK for exemplary purposes, but if you do this when you make 
 * your own magic spells, you may find that if you do this the universe may be 
 * inconsistent inside your plugin, but consistent outside of your plugin with
 * the same terms. This means your spells may fail when they ought to succeed.
 *)

open Environ
open Evd
open Term
open Names
open Command

(* Constant ID *)
let k_fresh = ref (1)

(* Get a fresh constant identifier *)
let fid () : int =
  let id = !k_fresh in
  k_fresh := id + 1;
  id

(* Intern a term *)
let intern env evd t : types =
  fst (Constrintern.interp_constr env evd t)

(* Extern a term *)
let extern env evd t : Constrexpr.constr_expr =
  Constrextern.extern_constr true env evd t

(* Define a new Coq term *)
let define_term (n : Id.t) (env : env) (evd : evar_map) (trm : types) : unit =
  do_definition
    n
    (Global, false, Definition)
    None
    []
    None
    (extern env evd trm)
    None
    (Lemmas.mk_hook (fun _ _ -> ()))
