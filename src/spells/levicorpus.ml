(*
 * Levicorpus flips a body upside-down (inverts a proof body).
 * What the Levicorpus spell shows is that benign and
 * useful magic can sometimes be built on dark magic.
 * 
 * While Sectumsempra alone is a dark spell, Levicorpus,
 * a much more innocent spell,
 * is built on the foundations of Sectumsempra (Snape's prior work): 
 * It would be too difficult to simply flip a complex body upside-down,
 * so instead, the spell works by getting all of the parts, 
 * flipping each part upside-down, and then reconstructing those parts 
 * in the opposite order.
 *
 * It is painless for the target, who never notices being deconstructed to 
 * begin with.
 * 
 * This is also a simplified version; consult me for details on how to handle 
 * other kinds of bodies, or see the PUMPKIN PATCH paper.
 *)

open Term
open Names
open Environ
open Evd
open Collections
open Coqterms
open Debruijn
open Substitution
open Printing (* useful for debugging *)
open Sectumsempra

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
let levicorpus_body (env : env) (evd : evar_map) (trm : types) : types option =
  let inv_fs = invert_factors evd (factor_term env evd trm) in
  if List.length inv_fs > 0 then
    Some (apply_factors inv_fs)
  else
    None
