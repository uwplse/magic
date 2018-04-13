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

(*
 * The Sectumsempra [Snape (1971)] spell cuts the body of a proof into pieces.
 * We call each of these pieces a factor.
 * See Example.v for more information.
 *)

(*
 * Factors are a list of terms and environments stored in reverse order (!!!).
 * If you reverse the list, then the first element is the assumption,
 * and every element after that takes the element before it to a new term.
 * So for the factors  [H : X, F : X -> Y, G : Y -> Z], we store
 * [(env ++ Y, G (Rel 1) : Z), (env ++ X, G (Rel 1) : Y), ..., (env, X)].
 * 
 * You can get these back as lambdas by calling reconstruct_factors,
 * but this form is efficient for folding it back together for inversion.
 *)
type factors = (env * types) list

(*
 * Given a term trm, if the type of trm is a function type
 * X -> Z, find factors through which it passes
 * (e.g., [H : X, F : X -> Y, G : Y -> Z] where trm = G o F).
 *
 * First zoom in all the way, then use the auxiliary path-finding
 * function.
 *)
val factor_term : env -> evar_map -> types -> factors

(* Apply factors to reconstruct a single term *)
val apply_factors : factors -> types
                                                
(* Sectumsempra *)
val sectumsempra_body : env -> evar_map -> types -> types list
