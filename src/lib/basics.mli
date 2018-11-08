(*
 * Plugin basics
 *)

open Environ
open Evd
open Constr
open Names

(* Get a fresh constant identifier *)
val fid : unit -> int
       
(* --- Representations --- *)

(* Internalize *)
val intern : env -> evar_map -> Constrexpr.constr_expr -> types

(* Externalize *)
val extern : env -> evar_map -> types -> Constrexpr.constr_expr

(* --- Definitions --- *)

(* Define a new Coq term *)
val define_term : Id.t -> evar_map -> types -> unit
