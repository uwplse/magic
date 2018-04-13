(*
 * Recursive substitutions on a term
 *)

open Environ
open Term
open Evd
open Hofs
open Debruijn
open Coqterms

(* Map a substitution over a term *)
let all_substs p env evd (src, dst) trm : types =
  map_term_env_if
    (fun en (s, _) t -> p en evd s t)
    (fun _ (_, d) _ -> d)
    (fun (s, d) -> (shift s, shift d))
    env
    (src, dst)
    trm
       
(* In env, substitute all subterms of trm that are convertible to src with dst *)
let all_conv_substs =
  all_substs convertible
