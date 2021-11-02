(*
 * Basic term and environment management, and some useful constants
 *)

open Basics
open Environ
open Declarations
open Constr
open Names
open Evd
open Collections

module CRD = Context.Rel.Declaration

(* --- Basic term and environment management --- *)
    
(* Convertibility *)
let convertible env evm (trm1 : types) (trm2 : types) : bool =
  let etrm1 = EConstr.of_constr trm1 in
  let etrm2 = EConstr.of_constr trm2 in
  Reductionops.is_conv env evm etrm1 etrm2

(* Infer a type (can cause universe leaks; not a problem for this plugin) *)
let infer_type (env : env) (evd : evar_map) (trm : types) : types =
  let jmt = Typeops.infer env trm in
  j_type jmt

(* Check whether a term has a given type *)
let has_type (env : env) (evd : evar_map) (typ : types) (trm : types) : bool =
  try
    let trm_typ = infer_type env evd trm in
    convertible env evd trm_typ typ
  with _ -> false
                    
(* Default reducer *)
let reduce_term (env : env) (evd : evar_map) (trm : types) : types =
  EConstr.to_constr
    evd
    (Reductionops.nf_betaiotazeta env evd (EConstr.of_constr trm))

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
let bindings_for_fix (names : name array) (typs : types array) : rel_declaration list =
  Array.to_list
    (CArray.map2_i
       (fun i name typ -> CRD.LocalAssum (name, Vars.lift i typ))
       names typs)

(* Lookup a definition *)
let lookup_definition (env : env) (def : types) : types =
  match kind def with
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
 match kind trm with
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
  match kind trm with
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
 * For efficiency, just check syntactic equality
 * Don't consider convertible terms for now
 *)
let is_rewrite (trm : types) : bool =
  equal trm eq_ind_r ||
  equal trm eq_ind ||
  equal trm eq_rec_r ||
  equal trm eq_rec
