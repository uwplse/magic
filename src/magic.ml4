DECLARE PLUGIN "wand"

open Term
open Names
open Environ
open Constrarg
open Format
open Univ
open Printer
open Declarations
open Command
open Evd

module CRD = Context.Rel.Declaration

(* --- Auxiliary functions --- *)

(* seq from template-coq *)
let rec range (min : int) (max : int) : int list =
  if min < max then
    min :: range (min + 1) max
  else
    []

(* Creates a list from the index 1 to max, inclusive *)
let from_one_to (max : int) : int list =
  range 1 (max + 1)

(* --- Plugin basics --- *)

(*
 * In this example plugin, I don't ever update evd.
 * This is OK for these spells, but if you do this when you make 
 * your own magic spells, you may find that if you do this the universe may be 
 * inconsistent inside your plugin, but consistent outside of your plugin with
 * the same terms. This means your spells may fail when they ought to succeed.
 *)

(* Intern a term *)
let intern env evd t : types =
  fst (Constrintern.interp_constr env evd t)

(* Extern a term *)
let extern env evd t : Constrexpr.constr_expr =
  Constrextern.extern_constr true env evd t

(* Define a new Coq term *)
let define_term (n : Id.t) (env : env) (evd : evar_map) (trm : types) : unit =
  do_definition
    n
    (Global, false, Definition)
    None
    []
    None
    (extern env evd trm)
    None
    (Lemmas.mk_hook (fun _ _ -> ()))

(* --- Basic term and environment management --- *)
                             
(* Convertibility *)
let convertible = Reductionops.is_conv

(* Infer a type (can cause universe leaks, but inconsequential for magic lesson) *)
let infer_type (env : env) (evd : evar_map) (trm : types) : types =
  Typing.unsafe_type_of env evd trm
                    
(* Default reducer *)
let reduce_term (env : env) (evd : evar_map) (trm : types) : types =
  Reductionops.nf_betaiotazeta evd trm

(* Default reducers on types *)
let reduce_type (env : env) (evd : evar_map) (trm : types) : types =
  reduce_term env evd (infer_type env evd trm)

(* Push a local binding *)
let push_local (n, t) = push_rel CRD.(LocalAssum (n, t))

(* Push a let-in definition to an environment *)
let push_in (n, e, t) = push_rel CRD.(LocalDef(n, e, t))
                    
(* Lookup n rels and remove then *)
let lookup_pop (n : int) (env : env) =
  let rels = List.map (fun i -> lookup_rel i env) (from_one_to n) in
  (pop_rel_context n env, rels)

(* Push bindings for a fixpoint *)
let bindings_for_fix (names : name array) (typs : types array) : CRD.t list =
  Array.to_list
    (CArray.map2_i
       (fun i name typ -> CRD.LocalAssum (name, Vars.lift i typ))
       names typs)

(* Lookup a definition *)
let lookup_definition (env : env) (def : types) : types =
  match kind_of_term def with
  | Const (c, u) ->
     let c_body = (lookup_constant c env).const_body in
     (match c_body with
      | Def cs -> Mod_subst.force_constr cs
      | OpaqueDef o -> Opaqueproof.force_proof (Global.opaque_tables ()) o
      | _ -> failwith "an axiom has no definition")
  | Ind _ -> def
  | _ -> failwith "not a definition"

(* 
 * Fully lookup a def in env which may be an alias
 * Don't fully delta-expand
 *)
let unwrap_definition (env : env) (trm : types) : types =
  let rec unwrap t =
    try
      unwrap (lookup_definition env t)
    with _ ->
      t
  in unwrap (lookup_definition env trm)

(* Get the name of a constant term *)
let name_of_const (trm : types) =
 match kind_of_term trm with
 | Const (c, u) ->
    let kn = Constant.canonical c in
    let (modpath, dirpath, label) = KerName.repr kn in
    Id.of_string_soft (Label.to_string label)
 | _ -> failwith "term must be a constant"
                 
(* Zoom all the way into a lambda term *)
let rec zoom_lambda_term (env : env) (trm : types) : env * types =
  match kind_of_term trm with
  | Lambda (n, t, b) ->
     zoom_lambda_term (push_local (n, t) env) b
  | _ ->
     (env, trm)

(* Reconstruct a lambda from an environment, but stop when i are left *)
let rec reconstruct_lambda_n (env : env) (b : types) (i : int) : types =
  if nb_rel env = i then
    b
  else
    let (n, _, t) = CRD.to_tuple @@ lookup_rel 1 env in
    let env' = pop_rel_context 1 env in
    reconstruct_lambda_n env' (mkLambda (n, t, b)) i

(* Reconstruct a lambda from an environment *)
let reconstruct_lambda (env : env) (b : types) : types =
  reconstruct_lambda_n env b 0

(* --- Higher-order functions on terms --- *)

(* Recurse on a mapping function with an environment for a fixpoint *)
let map_rec_env_fix map_rec d env a (ns : name array) (ts : types array) =
  let fix_bindings = bindings_for_fix ns ts in
  let env_fix = push_rel_context fix_bindings env in
  let n = List.length fix_bindings in
  let d_n = List.fold_left (fun a' _ -> d a') a (range 0 n) in
  map_rec env_fix d_n

(*
 * Map a function over a term in an environment
 * Update the environment as you go
 * Update the argument of type 'a using the a supplied update function
 * Return a new term
 *)
let rec map_term_env f d (env : env) (a : 'a) (trm : types) : types =
  let map_rec = map_term_env f d in
  match kind_of_term trm with
  | Cast (c, k, t) ->
     let c' = map_rec env a c in
     let t' = map_rec env a t in
     mkCast (c', k, t')
  | Prod (n, t, b) ->
     let t' = map_rec env a t in
     let b' = map_rec (push_local (n, t) env) (d a) b in
     mkProd (n, t', b')
  | Lambda (n, t, b) ->
     let t' = map_rec env a t in
     let b' = map_rec (push_local (n, t) env) (d a) b in
     mkLambda (n, t', b')
  | LetIn (n, trm, typ, e) ->
     let trm' = map_rec env a trm in
     let typ' = map_rec env a typ in
     let e' = map_rec (push_in (n, e, typ) env) (d a) e in
     mkLetIn (n, trm', typ', e')
  | App (fu, args) ->
     let fu' = map_rec env a fu in
     let args' = Array.map (map_rec env a) args in
     mkApp (fu', args')
  | Case (ci, ct, m, bs) ->
     let ct' = map_rec env a ct in
     let m' = map_rec env a m in
     let bs' = Array.map (map_rec env a) bs in
     mkCase (ci, ct', m', bs')
  | Fix ((is, i), (ns, ts, ds)) ->
     let ts' = Array.map (map_rec env a) ts in
     let ds' = Array.map (map_rec_env_fix map_rec d env a ns ts) ds in
     mkFix ((is, i), (ns, ts', ds'))
  | CoFix (i, (ns, ts, ds)) ->
     let ts' = Array.map (map_rec env a) ts in
     let ds' = Array.map (map_rec_env_fix map_rec d env a ns ts) ds in
     mkCoFix (i, (ns, ts', ds'))
  | Proj (p, c) ->
     let c' = map_rec env a c in
     mkProj (p, c')
  | _ ->
     f env a trm

(* --- The ugliest part of magic, DeBruijn indices --- *)

(*
 * This is not quite a canonical shift/unshift like you're used to in theory.
 * If you want to know why, ask, but it's fine for the spells in question.
 *)

(*
 * Map a function over a term, when the environment doesn't matter
 * Update the argument of type 'a using the a supplied update function
 * Return a new term
 *)
let map_term f d (a : 'a) (trm : types) : types =
  map_term_env (fun _ a t -> f a t) d empty_env a trm

(* Unshift an index by n *)
let unshift_i_by (n : int) (i : int) : int =
  i - n

(* Shift an index by n *)
let shift_i_by (n : int) (i : int) : int =
  unshift_i_by (- n) i

(* Unshift an index *)
let unshift_i (i : int) : int =
  unshift_i_by 1 i

(* Shift an index *)
let shift_i (i : int) : int =
  shift_i_by 1 i
    
(*
 * Unshifts a term by n if it is greater than the maximum index
 * max of a local binding
 *)
let unshift_local (max : int) (n : int) (trm : types) : types =
  map_term
    (fun (m, adj) t ->
      match kind_of_term t with
      | Rel i ->
         let i' = if i > m then unshift_i_by adj i else i in
         mkRel i'
      | _ ->
         t)
    (fun (m, adj) -> (shift_i m, adj))
    (max, n)
    trm

(*
 * Shifts a term by n if it is greater than the maximum index
 * max of a local binding
 *)
let shift_local (max : int) (n : int) (trm : types) : types =
  unshift_local max (- n) trm

(* Decrement the relative indexes of a term t by n *)
let unshift_by (n : int) (trm : types) : types =
  unshift_local 0 n trm

(* Increment the relative indexes of a term t by n *)
let shift_by (n : int) (t : types) : types  =
  unshift_by (- n) t

(* Increment the relative indexes of a term t by one *)
let shift (t : types) : types  =
  shift_by 1 t

(* Decrement the relative indexes of a term t by one *)
let unshift (t : types) : types =
  unshift_by 1 t
                
(* --- Sectumsempra logic --- *)

(*
 * This is the implementation of the simplest existing version of the sectumsempra 
 * (factoring) spell, which cuts a proof term into pieces.
 * The simple version doesn't handle terms with dependent types like A -> B -> C B,
 * which assumes a linear path, and which assumes the assumption is the 
 * last argument to the function. It also assumes a certain kind of term,
 * and doesn't handle some more complex terms.
 *
 * More general versions of this exist; if you are interested, let me know.
 *) 
               
type factors = (env * types) list

let assum : types = mkRel 1
                          
(* Apply the assumption in the term *)
let apply_assumption (fs : factors) (trm : types) : types =
  if List.length fs > 0 then
    assum
  else
    trm

(* Check if the term is the assumption *)
let is_assumption (env : env) (evd : evar_map) (trm : types) : bool =
  convertible env evd trm assum
                  
(* Swap out the assumption for a new one *)
let assume (env : env) (n : name) (typ : types) : env =
  push_local (n, typ) (pop_rel_context 1 env)

(*
 * Auxiliary path-finding function, once we are zoomed into a lambda
 * and the hypothesis we care about is the assumption (first term
 * in the environment).
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
    match kind_of_term trm with
    | App (f, args) ->
       let paths = Array.map (find_path env evd) args in
       let nonempty_paths = List.filter (fun l -> List.length l > 0) (Array.to_list paths) in
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

(* --- Command top-levels --- *)

(* Factor a term into a sequence of lemmas *)
let sectumsempra trm_ext : unit =
  let (evd, env) = Lemmas.get_current_context () in
  let trm = intern env evd trm_ext in
  let name = name_of_const trm in
  let prefix = Id.to_string name in
  let body = unwrap_definition env trm in
  let fs = reconstruct_factors (factor_term env evd body) in
  List.iteri
    (fun i lemma ->
      let lemma_id_string = String.concat "_" [prefix; string_of_int i] in
      let lemma_id = Id.of_string lemma_id_string in
      define_term lemma_id env evd lemma;
      Printf.printf "Defined %s\n" lemma_id_string)
    fs                  
                        
(* --- Commands --- *)

(* 
 * Slices a term into its parts. For more details, see Snape (1971).
 *)
VERNAC COMMAND EXTEND Sectumsempra CLASSIFIED AS SIDEFF
| [ "Sectumsempra" constr(trm) ] ->
  [ sectumsempra trm ]
END
