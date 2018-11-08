(*
 * Recursive substitutions on a term
 *)

open Environ
open Constr
open Evd

(* Map a substitution over subterms of a term *)
val all_substs :
  (env -> evar_map -> types -> types -> bool) ->
  env ->
  evar_map ->
  (types * types) ->
  types ->
  types
    
(*
 * Substitute all subterms of that are convertible to a source
 * term with a destination term
 *)
val all_conv_substs : env -> evar_map -> (types * types) -> types -> types

