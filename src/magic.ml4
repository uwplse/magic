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
open Tactics
open Collections

module CRD = Context.Rel.Declaration

(* --- Auxiliary functions --- *)

(* Constant ID *)
let k_fresh = ref (1)

(* Get a fresh constant identifier *)
let fid () : int =
  let id = !k_fresh in
  k_fresh := id + 1;
  id

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

(* Check whether a term has a given type *)
let has_type (env : env) (evd : evar_map) (typ : types) (trm : types) : bool =
  try
    let trm_typ = infer_type env evd trm in
    convertible env evd trm_typ typ
  with _ -> false
                        
(* Filter trms to those that have type typ in env *)
let filter_by_type (env : env) (evd : evar_map) (typ : types) (trms : types list) : types list =
  try
    List.filter (has_type env evd typ) trms
  with _ ->
    []
                    
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

(* Return a list of all indexes in env, starting with 1 *)
let all_rel_indexes (env : env) : int list =
  from_one_to (nb_rel env)

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
 * If it's not a definition, return the original term
 * Don't fully delta-expand
 *)
let rec unwrap_definition (env : env) (trm : types) : types =
  try
    unwrap_definition env (lookup_definition env trm)
  with _ ->
    trm
  
(* Get the name of a term if it's constant, otherwise fail *)
let name_of_const (trm : types) =
 match kind_of_term trm with
 | Const (c, u) ->
    let kn = Constant.canonical c in
    let (modpath, dirpath, label) = KerName.repr kn in
    Id.of_string_soft (Label.to_string label)
 | _ ->
    failwith "not a constant"

(* Try to get a name, and if it fails, call the default *)
let id_or_default (trm : types) get_id default =
  try
    get_id trm
  with _ ->
    default ()

(* Add a suffix to a name ID *)
let with_suffix (suffix : string) (id : Id.t) : Id.t =
  Id.of_string (String.concat "_" [Id.to_string id; suffix])

(* Get a fresh constant identifier with a prefix as an ID *)
let fresh_with_prefix (prefix : string) () : Id.t =
  let id_string = string_of_int (fid ()) in
  with_suffix id_string (Id.of_string prefix)
                 
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

(* --- Useful constants --- *)

(*
 * This is not a good way to construct constants. Don't copy it.
 * See recent coq-club email on this topic.
 *)

(* eq_ind_r *)
let eq_ind_r : types =
  mkConst
    (Constant.make2
       (ModPath.MPfile
          (DirPath.make (List.map Id.of_string ["Logic"; "Init"; "Coq"])))
       (Label.make "eq_ind_r"))

(* eq_ind *)
let eq_ind : types =
  mkConst
    (Constant.make2
       (ModPath.MPfile
          (DirPath.make (List.map Id.of_string ["Logic"; "Init"; "Coq"])))
       (Label.make "eq_ind"))

(* eq_rec_r *)
let eq_rec_r : types =
  mkConst
    (Constant.make2
       (ModPath.MPfile
          (DirPath.make (List.map Id.of_string ["Logic"; "Init"; "Coq"])))
       (Label.make "eq_rec_r"))

(* eq_rec *)
let eq_rec : types =
  mkConst
    (Constant.make2
       (ModPath.MPfile
          (DirPath.make (List.map Id.of_string ["Logic"; "Init"; "Coq"])))
       (Label.make "eq_rec"))

(* eq_sym *)
let eq_sym : types =
  mkConst
    (Constant.make2
       (ModPath.MPfile
          (DirPath.make (List.map Id.of_string ["Logic"; "Init"; "Coq"])))
       (Label.make "eq_sym"))
                       
(*
 * Check if a term is a rewrite via eq_ind or eq_ind_r
 * For efficiency, just check eq_constr
 * Don't consider convertible terms for now
 *)
let is_rewrite (trm : types) : bool =
  eq_constr trm eq_ind_r ||
  eq_constr trm eq_ind ||
  eq_constr trm eq_rec_r ||
  eq_constr trm eq_rec

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

(*
 * Map a function over a term in an environment
 * Only apply the function when a proposition is true
 * Apply the function eagerly
 * Update the environment as you go
 * Update the argument of type 'a using the a supplied update function
 * Return a new term
 *)
let rec map_term_env_if p f d (env : env) (a : 'a) (trm : types) : types =
  let map_rec = map_term_env_if p f d in
  if p env a trm then
    f env a trm
  else
    match kind_of_term trm with
    | Cast (c, k, t) ->
       let c' = map_rec env a c in
       let t' = map_rec env a t in
       mkCast (c', k, t')
    | Prod (n, t, b) ->
       let t' = map_rec env a t in
       let b' = map_rec (push_rel CRD.(LocalAssum(n, t')) env) (d a) b in
       mkProd (n, t', b')
    | Lambda (n, t, b) ->
       let t' = map_rec env a t in
       let b' = map_rec (push_rel CRD.(LocalAssum(n, t')) env) (d a) b in
       mkLambda (n, t', b')
    | LetIn (n, trm, typ, e) ->
       let trm' = map_rec env a trm in
       let typ' = map_rec env a typ in
       let e' = map_rec (push_rel CRD.(LocalDef(n, e, typ')) env) (d a) e in
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
    | Proj (pr, c) ->
       let c' = map_rec env a c in
       mkProj (pr, c')
    | _ ->
       trm

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

(* --- Higher substitutions --- *)

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

(* --- Debugging terms and environments --- *)
             
(*
 * Using pp, prints directly to a string
 *)
let print_to_string (pp : formatter -> 'a -> unit) (trm : 'a) : string =
  Format.asprintf "%a" pp trm

(* Gets n as a string *)
let name_as_string (n : name) : string =
  match n with
  | Name id -> string_of_id id
  | Anonymous -> "_"

(* Pretty prints a term using Coq's pretty printer *)
let print_constr (fmt : formatter) (c : constr) : unit  =
  Pp.pp_with fmt (Printer.pr_constr c)

(* Pretty prints a universe level *)
let print_univ_level (fmt : formatter) (l : Level.t) =
  Pp.pp_with fmt (Level.pr l)

(* Prints a universe *)
let universe_as_string u =
  match Universe.level u with
  | Some l -> print_to_string print_univ_level l
  | None -> Printf.sprintf "Max{%s}" (String.concat ", " (List.map (print_to_string print_univ_level) (LSet.elements (Universe.levels u))))

(* Gets a sort as a string *)
let sort_as_string s =
  match s with
  | Prop _ -> if s = prop_sort then "Prop" else "Set"
  | Type u -> Printf.sprintf "Type %s" (universe_as_string u)

(* Prints a term *)
let rec term_as_string (env : env) (trm : types) =
  match kind_of_term trm with
  | Rel i ->
     (try
       let (n, _, _) = CRD.to_tuple @@ lookup_rel i env in
       Printf.sprintf "(%s [Rel %d])" (name_as_string n) i
     with
       Not_found -> Printf.sprintf "(Unbound_Rel %d)" i)
  | Var v ->
     string_of_id v
  | Meta mv ->
     failwith "Metavariables are not yet supported"
  | Evar (k, cs) ->
     Printf.sprintf "??"
  | Sort s ->
     sort_as_string s
  | Cast (c, k, t) ->
     Printf.sprintf "(%s : %s)" (term_as_string env c) (term_as_string env t)
  | Prod (n, t, b) ->
     Printf.sprintf "(Π (%s : %s) . %s)" (name_as_string n) (term_as_string env t) (term_as_string (push_rel CRD.(LocalAssum(n, t)) env) b)
  | Lambda (n, t, b) ->
     Printf.sprintf "(λ (%s : %s) . %s)" (name_as_string n) (term_as_string env t) (term_as_string (push_rel CRD.(LocalAssum(n, t)) env) b)
  | LetIn (n, trm, typ, e) ->
     Printf.sprintf "(let (%s : %s) := %s in %s)" (name_as_string n) (term_as_string env typ) (term_as_string env typ) (term_as_string (push_rel CRD.(LocalDef(n, e, typ)) env) e)
  | App (f, xs) ->
     Printf.sprintf "(%s %s)" (term_as_string env f) (String.concat " " (List.map (term_as_string env) (Array.to_list xs)))
  | Const (c, u) ->
     let ker_name = Constant.canonical c in
     string_of_kn ker_name
  | Construct (((i, i_index), c_index), u) ->
     let mutind_body = lookup_mind i env in
     let ind_body = mutind_body.mind_packets.(i_index) in
     let constr_name_id = ind_body.mind_consnames.(c_index - 1) in
     string_of_id constr_name_id
  | Ind ((i, i_index), u) ->
     let mutind_body = lookup_mind i env in
     let ind_bodies = mutind_body.mind_packets in
     let name_id = (ind_bodies.(i_index)).mind_typename in
     string_of_id name_id
  | Case (ci, ct, m, bs) ->
     let (i, i_index) = ci.ci_ind in
     let mutind_body = lookup_mind i env in
     let ind_body = mutind_body.mind_packets.(i_index) in
     Printf.sprintf
       "(match %s : %s with %s)"
       (term_as_string env m)
       (term_as_string env ct)
       (String.concat
          " "
          (Array.to_list
             (Array.mapi
                (fun c_i b ->
                  Printf.sprintf
                    "(case %s => %s)"
                    (string_of_id (ind_body.mind_consnames.(c_i)))
                    (term_as_string env b))
                bs)))
  | Fix ((is, i), (ns, ts, ds)) ->
     let env_fix = push_rel_context (bindings_for_fix ns ds) env in
     String.concat
       " with "
       (map3
          (fun n t d ->
            Printf.sprintf
             "(Fix %s : %s := %s)"
             (name_as_string n)
             (term_as_string env t)
             (term_as_string env_fix d))
          (Array.to_list ns)
          (Array.to_list ts)
          (Array.to_list ds))
  | CoFix (i, (ns, ts, ds)) ->
     Printf.sprintf "TODO" (* TODO *)
  | Proj (p, c) ->
     Printf.sprintf "TODO" (* TODO *)

(* --- Coq environments --- *)

(* Gets env as a string *)
let env_as_string (env : env) : string =
  let all_relis = all_rel_indexes env in
  String.concat
    ",\n"
    (List.map
       (fun i ->
         let (n, b, t) = CRD.to_tuple @@ lookup_rel i env in
         Printf.sprintf "%s (Rel %d): %s" (name_as_string n) i (term_as_string (pop_rel_context i env) t))
       all_relis)

(* Print a separator string *)
let print_separator unit : unit =
  Printf.printf "%s\n\n" "-----------------"

(* Debug a term *)
let debug_term (env : env) (trm : types) (descriptor : string) : unit =
  Printf.printf "%s: %s\n\n" descriptor (term_as_string env trm)

(* Debug a list of terms *)
let debug_terms (env : env) (trms : types list) (descriptor : string) : unit =
  List.iter (fun t -> debug_term env t descriptor) trms

(* Debug an environment *)
let debug_env (env : env) (descriptor : string) : unit =
  Printf.printf "%s: %s\n\n" descriptor (env_as_string env)
             
(* --- Sectumsempra --- *)

(*
 * This is the implementation of the simplest existing version of the sectumsempra 
 * spell, which cuts a body into pieces.
 *
 * This simple exemplary version makes a lot of assumptions about the body.
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
  let fs = reconstruct_factors (factor_term env evd body) in
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
