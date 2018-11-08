(*
 * The Sectumsempra [Snape (1971)] spell cuts the body of a proof into pieces.
 * We call each of these pieces a factor.
 * See Example.v for more information.
 *
 * This is the implementation of the simplest existing version of this spell.
 * This simple exemplary version makes a lot of assumptions about the body,
 * and only handles certain kinds of types. More general versions of this 
 * exist; if you are interested, let me know.
 *)

open Constr
open Names
open Environ
open Evd
open Collections
open Basics
open Coqterms
open Debruijn
open Printing (* useful for debugging *)

module CRD = Context.Rel.Declaration
             
(* --- Sectumsempra --- *)

type factors = (env * types) list

let assum : types = mkRel 1
                          
(* Apply the assumption in the term *)
let apply_assumption (fs : factors) (trm : types) : types =
  if List.length fs > 0 then assum else trm

(* Check if the term is the assumption *)
let is_assumption (env : env) (evd : evar_map) (trm : types) : bool =
  convertible env evd trm assum
                  
(* Swap out the assumption for a new one *)
let assume (env : env) (n : name) (typ : types) : env =
  push_local (n, typ) (pop_rel_context 1 env)

(*
 * Auxiliary path-finding function when we have a sequence of applications
 * and the hypothesis we care about is the assumption (last bound term
 * in the environment, or Rel 1).
 *
 * The type path is in reverse order for efficiency, and is really
 * a list of environments (assumptions) and terms. When we refer to
 * "the end" it is the head of the list.
 *
 * The spell works as follows:
 * 1. If a term is the assumption, return a single path with
 *    the environment and term, which is the identity path.
 * 2. Otherwise, if it is an application:
 *    a. Recursively get the type path for each argument.
 *    b. If there are multiple nonempty type paths, then we cannot abstract out
 *       the assumption in a single function, so return the identity path.
 *    c. Otherwise, get the only non-empty path, then:
 *       i. Zoom in on each argument with the current assumption
 *       ii. Assume the conclusion of the element at the end of the path
 *       ii. Apply the function to the zoomed arguments in the environment
 *            with the new assumption, and add that to the end of the path
 *       iv. If applying the assumption at any point fails, return the empty
 *           path
 *
 * In other words, this is going as deep into the term as possible and
 * finding some Y for which X -> Y. It is then assuming Y,
 * and asking if there is some path from Y to the conclusion.
 *)
let rec find_path (env : env) (evd : evar_map) (trm : types) : factors =
  if is_assumption env evd trm then
    [(env, trm)]
  else
    match kind trm with
    | App (f, args) ->
       let paths = Array.map (find_path env evd) args in
       let nonempty_paths =
         List.filter
           (fun l -> List.length l > 0)
           (Array.to_list paths)
       in
       if List.length nonempty_paths > 1 then
	 [(env, trm)]
       else if List.length nonempty_paths = 1 then
	 let path = List.hd nonempty_paths in
	 let (env_arg, arg) = List.hd path in
         let assume_arg i a = apply_assumption (Array.get paths i) a in
         let args_assumed = Array.mapi assume_arg args in
	 try
           let t = unshift (reduce_type env_arg evd arg) in
	   (assume env Anonymous t, mkApp (f, args_assumed)) :: path
	 with _ ->
	   []
       else
	 []
    | _ ->
       []

(*
 * Given a term trm, if the type of trm is a function type
 * X -> Z, find factors through which it passes
 * (e.g., [H : X, F : X -> Y, G : Y -> Z] where trm = G o F)
 *
 * First zoom in all the way, then use the auxiliary path-finding
 * function.
 *)
let factor_term (env : env) (evd : evar_map) (trm : types) : factors =
  let (env_zoomed, trm_zoomed) = zoom_lambda_term env (reduce_term env evd trm) in
  let path_body = find_path env_zoomed evd trm_zoomed in
  List.map
    (fun (env, body) ->
      if is_assumption env evd body then
	(env, body)
      else
	let (n, _, t) = CRD.to_tuple @@ lookup_rel 1 env in
	(pop_rel_context 1 env, mkLambda (n, t, body)))
    path_body

(*
 * Reconstruct factors as terms using hypotheses from the environment.
 * This produces a friendly form in the correct order.
 * The other form is useful for efficiency for other spells, like levicorpus.
 *)
let reconstruct_factors (fs : factors) : types list =
  List.map
    (fun (en, t) -> reconstruct_lambda en t)
    (List.tl (List.rev fs))

(* Apply factors to reconstruct a single term *)
let apply_factors (fs : factors) : types =
  let (env, base) = List.hd fs in
  let body =
    List.fold_right
      (fun (_, t) t_app ->
        mkApp (shift t, Array.make 1 t_app))
      (List.tl fs)
      base
  in reconstruct_lambda env body

(* Sectumsempra *)
let sectumsempra_body (env : env) (evd : evar_map) (body : types) : types list =
  reconstruct_factors (factor_term env evd body)
