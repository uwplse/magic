(*
 * The Reducio spell reduces the target back to its normal size.
 * Please do not use this on humans unless they are impacted by Engorgio.
 *
 * This is a simple version of Reducio.
 * More complex versions are left to the witch or wizard.
 *)

open Environ
open Term
open Evd
open Coqterms
open Sectumsempra
open Debruijn

(*
 * Check if two consecutive factors are inverses
 *)
let are_inverses (evd : evar_map) (env', trm') (env, trm) : bool =
  try
    let (_, t, b) = destProd (reduce_type env evd trm) in
    let (_, t', b') = destProd (reduce_type env' evd trm') in
    convertible env evd t (unshift b') && convertible env' evd (unshift b) t'
  with _ ->
    false

(*
 * Filter out every pair of consecutive inverses
 *)
let rec filter_inverses (evd : evar_map) (fs : factors) =
  match fs with
  | f' :: (f :: tl) ->
     if are_inverses evd f' f then
       filter_inverses evd tl
     else
       f' :: (filter_inverses evd (f :: tl))
  | _ ->
     fs

(*
 * Like Levicorpus, the foundations of Reducio are grounded in Sectumsempra.
 * Reducio first slices the target into pieces, then looks for redundant pieces
 * to get rid of, then reconstructs the target. When it fails,
 * it simply produces the original term.
 *
 * Note: This is precisely why it can be dangerous to use on humans if they 
 * have not been engorged first, since they will not have any redundant 
 * pieces to get rid of.
 *
 * In this simple version, two pieces are redundant exactly when one
 * has the inverse type of the other, and the spell only gets rid
 * of consecutive redundant pieces.
 *)
let reducio_body (env : env) (evd : evar_map) (trm : types) : types =
  let fs = List.rev (factor_term env evd trm) in
  let red_fs = List.hd fs :: (filter_inverses evd (List.tl fs)) in
  let red = apply_factors red_fs in
  if has_type env evd (infer_type env evd trm) red then
    reduce_term env evd red
  else
    trm
