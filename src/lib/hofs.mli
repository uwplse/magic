(*
 * Higher-order functions on terms.
 * 
 * There are a lot more of these in the PUMPKIN PATCH repository
 * if they are useful for you.
 *)

open Collections
open Term
open Environ
open Evd
open Coqterms
open Names

(*
 * Map a function over a term in an environment
 * Update the environment as you go
 * Update the argument of type 'a using the a supplied update function
 * Return a new term
 *)
val map_term_env :
  (env -> 'a -> types -> types) ->
  ('a -> 'a) ->
  env ->
  'a ->
  types ->
  types

(*
 * Map a function over a term in an environment
 * Only apply the function when a proposition is true
 * Apply the function eagerly
 * Update the environment as you go
 * Update the argument of type 'a using the a supplied update function
 * Return a new term
 *)
val map_term_env_if :
  (env -> 'a -> types -> bool) ->
  (env -> 'a -> types -> types) ->
  ('a -> 'a) ->
  env ->
  'a ->
  types ->
  types
