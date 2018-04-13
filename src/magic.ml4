DECLARE PLUGIN "wand"

open Term
open Names
open Environ
open Constrarg
open Evd
open Tactics
open Collections
open Basics
open Coqterms
open Debruijn
open Substitution
open Printing (* useful for debugging *)
(* TODO clean above again *)

(* --- Spells --- *)

(*
 * These modules contain the magic behind each of these spells.
 * You should inspect and modify these as needed.
 *)
       
open Sectumsempra

(* --- Levicorpus --- *)

(*
 * What the Levicorpus spell shows is that benign and
 * useful magic can sometimes be built on dark magic.
 * 
 * While Sectumsempra alone is a dark spell, Levicorpus,
 * a much more innocent spell that simply flips bodies upside-down,
 * is built on the foundations of Sectumsempra (Snape's prior work): It would be too
 * difficult to simply flip a complex body upside-down, so instead,
 * the spell works by getting all of the parts, flipping each part upside-down, 
 * and then reconstructing those parts in the opposite order.
 *
 * It is painless for the target, who never notices being deconstructed to begin with.
 * 
 * This is also a simplified version; consult me for details on how to handle 
 * other kinds of bodies, or see the PUMPKIN PATCH paper.
 *)

(* 
 * Invert rewrites by exploiting symmetry of equality.
 * Simplified inversion for this toy plugin only handles sequences of rewrites. 
 *)
let invert_rewrite (env : env) (evd : evar_map) (trm : types) : (env * types) option =
  let trm = reduce_term env evd trm in
  match kind_of_term trm with
  | Lambda (n, t, b) ->
     let env_b = push_local (n, t) env in
     let t' = unshift (reduce_term env_b evd (infer_type env_b evd b)) in
     let trm' = all_conv_substs env evd (t, t') trm in
     let goal_type = mkProd (n, t', t) in
     let (n, t', b') = destLambda trm' in
     if isApp b' && is_rewrite (fst (destApp b')) then
       let (f, args) = destApp b' in
       let i_eq = Array.length args - 1 in
       let eq = args.(i_eq) in
       let eq_type = infer_type env evd eq in
       let eq_typ_args = Array.to_list (snd (destApp eq_type)) in
       let eq_args = List.append eq_typ_args [eq] in
       let eq_r = mkApp (eq_sym, Array.of_list eq_args) in
       let i_src = 1 in
       let i_dst = 4 in
       let args_r =
         Array.mapi
	   (fun i a ->
	     if i = i_eq then
	       eq_r
	     else if i = i_src then
	       args.(i_dst)
	     else if i = i_dst then
	       args.(i_src)
	     else
	       a)
	   args
       in Some (env, mkLambda (n, t', mkApp (f, args_r)))
     else
       None
  | _ ->
     Some (env, trm)
          
                        
(*
 * Given the factors for a term and an inverter,
 * invert every factor, and produce the inverse factors by reversing it.
 *
 * That is, take [X; X -> Y; Y -> Z] and produce [Z; Z -> Y; Y -> X].
 *
 * If inverting any term along the way fails, produce the empty list.
 *
 * For simplicity, we assume a sequence of rewrites for this example plugin.
 *)
let invert_factors (evd : evar_map) (fs : factors) : factors =
  let inverse_options = List.map (fun (en, f) -> invert_rewrite en evd f) fs in
  let inverted = List.rev (get_all_or_none inverse_options) in
  match inverted with (* swap final hypothesis *)
  | (env_inv, trm_inv) :: t when List.length t > 0 ->
     let (n, h_inv, _) = destLambda (snd (last t)) in
     let env_inv = push_rel CRD.(LocalAssum(n, h_inv)) (pop_rel_context 1 env_inv) in
     (env_inv, trm_inv) :: t
  | _ ->
     inverted
                        
(* Invert a body in an environment *)
let invert (env : env) (evd : evar_map) (trm : types) : types option =
  let inv_fs = invert_factors evd (factor_term env evd trm) in
  if List.length inv_fs > 0 then
    Some (apply_factors inv_fs)
  else
    None

(* Invert a body and define the result *)
let invert_body n env evd trm =
  let inverted = invert env evd trm in
  if Option.has_some inverted then
    let flipped = Option.get inverted in
    define_term n env evd flipped;
    Printf.printf "Defined %s\n" (Id.to_string n)
  else
    failwith "Could not flip the body upside-down; are you sure this is a human?"

(* Tactic version *)
let invert_body_in n env evd trm =
  let inverted = invert env evd trm in
  if Option.has_some inverted then
    let flipped = Option.get inverted in
    letin_pat_tac None n ((evd, evd), flipped) Locusops.nowhere
  else
    failwith "Could not flip the body upside-down; are you sure this is a human?"

(* --- Reducio --- *)

(*
 * The Reducio spell reduces the target back to its normal size.
 * Please do not use this on humans unless they are impacted by Engorgio.
 *
 * This is a simple version of Reducio.
 * More complex versions are left to the witch or wizard.
 *)

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
let reduce_body (env : env) (evd : evar_map) (trm : types) : types =
  let fs = List.rev (factor_term env evd trm) in
  let red_fs = List.hd fs :: (filter_inverses evd (List.tl fs)) in
  let red = apply_factors red_fs in
  if has_type env evd (infer_type env evd trm) red then
    reduce_term env evd red
  else
    trm

(* --- Spell top-levels --- *)

let geminio_in (trm : types) : unit Proofview.tactic =
  let (evd, env) = Lemmas.get_current_context () in
  letin_pat_tac None Anonymous ((evd, evd), trm) Locusops.nowhere
                    
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

let levicorpus_in (trm : types) : unit Proofview.tactic =
  let (evd, env) = Lemmas.get_current_context () in
  let body = unwrap_definition env trm in
  invert_body_in Anonymous env evd body
    
let levicorpus target : unit =
  let (evd, env) = Lemmas.get_current_context () in
  let trm = intern env evd target in
  let name_of_inv t = with_suffix "inv" (name_of_const t) in
  let inv_id = id_or_default trm name_of_inv (fresh_with_prefix "inverse") in
  invert_body inv_id env evd (unwrap_definition env trm)

let reducio target : unit =
  let (evd, env) = Lemmas.get_current_context () in
  let trm = intern env evd target in
  let name_of_red t = with_suffix "red" (name_of_const t) in
  let red_id = id_or_default trm name_of_red (fresh_with_prefix "reduced") in
  let body = unwrap_definition env trm in
  let red = reduce_body env evd body in
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
