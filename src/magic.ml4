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

(*
 * Some of these are implemented, and some are left as exercises.
 * Do the exercises in whichever order you please. 
 * Tests for these exercises are in the coq/exercises directory.
 *)
       
(* Tactic version of Geminio *)
let geminio_in (trm : types) : unit Proofview.tactic =
  let (evd, env) = Lemmas.get_current_context () in
  letin_pat_tac None Anonymous ((evd, evd), trm) Locusops.nowhere

(*
 * Exercise 1 [2 points]: Implement a command version of Geminio,
 * which takes an expicit identifier n and defines it to refer 
 * to the cloned term. This is a nice way to get used to the infrastructure.
 * It should be about two lines of code.
 *
 * If successful, GeminioNamed.v should compile.
 *)
let geminio_named n target : unit =
  () (* Your code here *)
                
(*
 * Exercise 2 [5 points]: Implement a command version of Geminio
 * that automatically determines the identifier name by adding the
 * "_clone" suffix, so that f is cloned to f_clone.
 * 
 * If successful, Geminio.v should compile.
 *)
let geminio target : unit =
  () (* Your code here *)
                
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

(*
 * Exercise 3 [10 points]: Implement a tactic version of Sectumsempra.
 * 
 * Hint: To form a name from an identifier, you can use the Name constructor.
 * To string tactics together, see tclTHEN proofview.mli in the 
 * Coq source code.
 * 
 * If successful, Sectumsempra.v should compile.
 *)
let sectumsempra_in trm : unit Proofview.tactic =
  Proofview.tclUNIT () (* Your code here *)

(* Common code for Levicorpus *)
let levicorpus_common env evd trm define =
  (* Your extended code here *)
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

(*
 * Exercise 4 [15 points]: Implement a version of Reducio that
 * also gets rid of factors with the identity type.
 * That is, a term with the following factors:
 *
 * A -> B
 * B -> C
 * C -> C
 * C -> B
 * B -> D
 *
 * should reduce to a term with the following factors:
 *
 * A -> B
 * B -> D
 *
 * If successful, ReducioDuo.v should compile.
 *)
let reducio_duo target : unit =
  () (* Your code here *)
                
(*
 * Exercise 5 [15 points]: Implement a version of Reducio
 * that handles nested inverses. So, for example,
 * a term with factors of the following types:
 *
 * A -> B
 * B -> C
 * C -> D
 * D -> C
 * C -> B
 * B -> E
 *
 * should reduce to a term with the following factors:
 *
 * A -> B
 * B -> E
 *
 * If successful, ReducioTria.v should compile.
 *)
let reducio_tria target : unit =
  () (* Your code here *)

(*
 * Exercise 6 [20 points]: Implement a version of Reducio
 * that handles cycles. So, for example,
 * a term with factors of the following types:
 *
 * A -> B
 * B -> C
 * C -> D
 * D -> B
 * B -> E
 *
 * should reduce to a term with the following factors:
 *
 * A -> B
 * B -> E
 *
 * If successful, ReducioMaxima.v should compile.
 *)
let reducio_maxima target : unit =
  () (* Your code here *)
                
(* --- Spells --- *)

(*
 * Simply duplicates a term in the context.
 *)
TACTIC EXTEND geminio
| [ "geminio" constr(target) ] ->
  [ geminio_in target ]
END

(*
 * Command version of Geminio (left to the wizard).
 *)
VERNAC COMMAND EXTEND Geminio CLASSIFIED AS SIDEFF
| [ "Geminio" constr(target) ] ->
  [ geminio target  ]
| [ "Geminio" constr(target) "as" ident(n)] ->
  [ geminio_named n target ]
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
 * Tactic version of the Sectumsempra spell.
 *)
TACTIC EXTEND sectumsempra
| [ "sectumsempra" constr(target) ] ->
  [ sectumsempra_in target ]
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
| [ "Reducio" "Duo" constr(target) ] ->
  [ reducio_duo target ]
| [ "Reducio" "Tria" constr(target) ] ->
  [ reducio_tria target ]
| [ "Reducio" "Maxima" constr(target) ] ->
  [ reducio_maxima target ]   
END
