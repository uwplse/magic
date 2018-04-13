(*
 * Basic term and environment management, and some useful constants
 *)

open Environ
open Evd
open Term
open Declarations
open Names

module CRD = Context.Rel.Declaration

(* --- Constants --- *)
               
val eq_sym : types
               
(* --- Term and environment management --- *)
               
(* Convertibility *)
val convertible :
  ?reds:Names.transparent_state -> env -> evar_map -> types -> types -> bool

(* Infer the type of a term in an environment *)
val infer_type : env -> evar_map -> types -> types

(* Check whether a term has a given type *)
val has_type : env -> evar_map -> types -> types -> bool

(* betaiotazeta, which is often useful, but doesn't fully normalize *)
val reduce_term : env -> evar_map -> types -> types

(* betaiotazeta on the type *)
val reduce_type : env -> evar_map -> types -> types

(* Push a local binding *)
val push_local : (name * types) -> env -> env

(* Push a let-in definition to an environment *)
val push_in : (name * types * types) -> env -> env
                    
(* Lookup n rels and remove then *)
val lookup_pop : int -> env -> (env * CRD.t list)

(* Return a list of all indexes in env, starting with 1 *)
val all_rel_indexes : env -> int list

(* Get bindings for a fixpoint *)
val bindings_for_fix : name array -> types array -> CRD.t list

(* Lookup a definition *)
val lookup_definition : env -> types -> types

(* Unwrap a term until it is no longer a definition *)
val unwrap_definition : env -> types -> types
  
(* Get the name of a term if it's constant, otherwise fail *)
val name_of_const : types -> Id.t

(* Try to get a name, and if it fails, call the default *)
val id_or_default : types -> (types -> Id.t) -> (unit -> Id.t) -> Id.t

(* Add a suffix to a name ID *)
val with_suffix : string -> Id.t -> Id.t

(* Get a fresh constant identifier with a prefix as an ID *)
val fresh_with_prefix : string -> unit -> Id.t
                 
(* Zoom all the way into a lambda term *)
val zoom_lambda_term : env -> types -> (env * types)

(* Reconstruct a lambda from an environment and a body *)
val reconstruct_lambda : env -> types -> types
                                           
(* Check if a term is exactly a rewrite induction principle *)
val is_rewrite : types -> bool

       
