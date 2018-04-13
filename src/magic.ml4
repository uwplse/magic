DECLARE PLUGIN "wand"

open Term
open Names
open Environ
open Constrarg
open Evd
open Tactics
open Basics
open Coqterms
open Printing (* useful for debugging *)

(* --- Spells --- *)

(*
 * These modules contain the magic behind the non-trivial spells.
 * You should inspect and modify these as needed.
 *)
       
open Sectumsempra
open Levicorpus
open Reducio

(* --- Spell top-levels --- *)

(* Geminio *)
let geminio_in (trm : types) : unit Proofview.tactic =
  let (evd, env) = Lemmas.get_current_context () in
  letin_pat_tac None Anonymous ((evd, evd), trm) Locusops.nowhere

(* Sectumsempra *)
let sectumsempra target : unit =
  let (evd, env) = Lemmas.get_current_context () in
  let trm = intern env evd target in
  let id = id_or_default trm name_of_const (fresh_with_prefix "factor") in
  let body = unwrap_definition env trm in
  let fs = sectumsempra_body env evd body in
  List.iteri
    (fun i lemma ->
      let lemma_id = with_suffix (string_of_int i) id in
      define_term lemma_id env evd lemma;
      Printf.printf "Defined %s\n" (Id.to_string lemma_id))
    fs

(* Common Levicorpus logic *)
let levicorpus_common env evd trm define =
  let inverted = levicorpus_body env evd trm in
  if Option.has_some inverted then
    let flipped = Option.get inverted in
    define env evd flipped
  else
    failwith "Could not flip the body upside-down; are you sure this is a human?"

(* Tactic version of Levicorpus *)
let levicorpus_in (trm : types) : unit Proofview.tactic =
  let (evd, env) = Lemmas.get_current_context () in
  let body = unwrap_definition env trm in
  let define env evd trm =
    letin_pat_tac None Anonymous ((evd, evd), trm) Locusops.nowhere
  in levicorpus_common env evd body define

(* Command version of Levicorpus *)
let levicorpus target : unit =
  let (evd, env) = Lemmas.get_current_context () in
  let trm = intern env evd target in
  let name_of_inv t = with_suffix "inv" (name_of_const t) in
  let inv_id = id_or_default trm name_of_inv (fresh_with_prefix "inverse") in
  let body = unwrap_definition env trm in
  let define env evd trm =
    define_term inv_id env evd trm;
    Printf.printf "Defined %s\n" (Id.to_string inv_id)
  in levicorpus_common env evd body define

(* Reducio *)
let reducio target : unit =
  let (evd, env) = Lemmas.get_current_context () in
  let trm = intern env evd target in
  let name_of_red t = with_suffix "red" (name_of_const t) in
  let red_id = id_or_default trm name_of_red (fresh_with_prefix "reduced") in
  let body = unwrap_definition env trm in
  let red = reducio_body env evd body in
  define_term red_id env evd red;
  Printf.printf "Defined %s\n" (Id.to_string red_id)
                
(* --- Spells --- *)

(*
 * Simply duplicates a term in the context.
 *)
TACTIC EXTEND geminio
| [ "geminio" constr(target) ] ->
  [ geminio_in target ]
END
              
(* 
 * Slices the body of the target. 
 * For more details, see Snape (1971).
 *)
VERNAC COMMAND EXTEND Sectumsempra CLASSIFIED AS SIDEFF
| [ "Sectumsempra" constr(target) ] ->
  [ sectumsempra target ]
END

(* 
 * Flips the body of the target upside-down.
 * This is the command version of the spell.
 * For more details, see Snape (1975).
 *)
VERNAC COMMAND EXTEND Levicorpus CLASSIFIED AS SIDEFF
| [ "Levicorpus" constr(target) ] ->
  [ levicorpus target ]
END

(* 
 * Tactic version of the Levicorpus spell.
 *)
TACTIC EXTEND levicorpus
| [ "levicorpus" constr(target) ] ->
  [ levicorpus_in target ]
END

(* 
 * Reduces the target to its normal size.
 *)
VERNAC COMMAND EXTEND Reducio CLASSIFIED AS SIDEFF
| [ "Reducio" constr(target) ] ->
  [ reducio target ]
END
