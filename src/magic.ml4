DECLARE PLUGIN "wand"

open Stdarg
open Names
open Environ
open Constr
open Evd
open Tactics
open Basics
open Coqterms
open Substitution (* useful for later exercises *)
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
let geminio_in (etrm : EConstr.constr) : unit Proofview.tactic =
  let (evm, env) = Pfedit.get_current_context () in
  letin_pat_tac false None Anonymous (evm, etrm) Locusops.nowhere

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
  let (evm, env) = Pfedit.get_current_context () in
  let trm = intern env evm target in
  let id = id_or_default trm name_of_const (fresh_with_prefix "factor") in
  let body = unwrap_definition env trm in
  let fs = sectumsempra_body env evm body in
  List.iteri
    (fun i lemma ->
      let lemma_id = with_suffix (string_of_int i) id in
      define_term lemma_id evm lemma;
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
let levicorpus_common env evm trm define =
  let inverted = levicorpus_body env evm trm in
  if Option.has_some inverted then
    let flipped = Option.get inverted in
    define evm flipped
  else
    failwith "Could not flip the body upside-down; are you sure this is a human?"

(* Tactic version of Levicorpus *)
let levicorpus_in (etrm : EConstr.t) : unit Proofview.tactic =
  let (evm, env) = Pfedit.get_current_context () in
  let trm = EConstr.to_constr evm etrm in
  let body = unwrap_definition env trm in
  let define evm trm =
    let etrm = EConstr.of_constr trm in
    letin_pat_tac false None Anonymous (evm, etrm) Locusops.nowhere
  in levicorpus_common env evm body define

(* Command version of Levicorpus *)
let levicorpus target : unit =
  let (evm, env) = Pfedit.get_current_context () in
  let trm = intern env evm target in
  let name_of_inv t = with_suffix "inv" (name_of_const t) in
  let inv_id = id_or_default trm name_of_inv (fresh_with_prefix "inverse") in
  let body = unwrap_definition env trm in
  let define evm trm =
    define_term inv_id evm trm;
    Printf.printf "Defined %s\n" (Id.to_string inv_id)
  in levicorpus_common env evm body define

(* Reducio *)
let reducio target : unit =
  let (evm, env) = Pfedit.get_current_context () in
  let trm = intern env evm target in
  let name_of_red t = with_suffix "red" (name_of_const t) in
  let red_id = id_or_default trm name_of_red (fresh_with_prefix "reduced") in
  let body = unwrap_definition env trm in
  let red = reducio_body env evm body in
  define_term red_id evm red;
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

(*
 * Exercise 7 [15 points] The Relashio spell releases the target
 * from a binding. Implement a simple version of Relashio
 * that takes a constant c and abstracts all terms convertible with c
 * in target at the highest level possible.
 * So, for example, given the following two definitions:
 *
 * Definition bar (n : nat) := n + 0.
 * Definition foo (n : nat) := n + (0 + 0).
 *
 * casting the following spells:
 *
 * Relashio 0 in foo.
 * Relashio 0 in bar.
 *
 * should produce two terms foo_rel, bar_rel which both have the same body
 * (the name of the released binding m is irrelevant):
 *
 * fun (m : nat) (n : nat) => n + m
 *
 * Hint: The all_conv_substs function from substitution.ml will do this
 * substitution for you. This is all doable in about 10 lines of code.
 *
 * If successful, Relashio.v should compile.
 *)
let relashio c target : unit =
  () (* Your code here *)

(*
 * Bonus (I'll buy you a beer if you're the first one
 * to implement this): Implement the Lumos tactic, which helps
 * the user when they are stuck during an inductive proof. 
 * Lumos lights up the way by generating an intermediate goal and inductive
 * hypothesis that are generalized versions of the current goal and inductive
 * hypothesis. his allows the user to play around trying to prove the 
 * intermediate goal, and see if that's the inductive hypothesis they 
 * really want. They can then go back and change the theorem statement 
 * appropriately.
 *
 * Hint: You'll want something similar to all_conv_substs to generalize
 * the inductive hypothesis, but you'll likely need to be smarter about how you
 * generalize if you want to produce useful goals.
 *)
let lumos_in trm :  unit Proofview.tactic =
  Proofview.tclUNIT () (* Your code here *)
                
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

(* 
 * Releases the binding to c in target.
 *)
VERNAC COMMAND EXTEND Relashio CLASSIFIED AS SIDEFF
| [ "Relashio" constr(c) "in" constr(target) ] ->
  [ relashio c target ]
END

(*
 * Helps a user who is stuck during induction.
 *)
TACTIC EXTEND lumos
| [ "lumos" constr(target) ] ->
  [ lumos_in target ]
END
    
