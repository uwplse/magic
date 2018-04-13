(*
 * The Reducio spell reduces the target back to its normal size.
 * Please do not use this on humans unless they are impacted by Engorgio.
 *
 * This is a simple version of Reducio.
 * More complex versions are left to the witch or wizard.
 *)

open Environ
open Term
open Evd

(*
 * Like Levicorpus, the foundations of Reducio are grounded in Sectumsempra.
 * Reducio first slices the target into pieces, then looks for redundant pieces
 * to get rid of, then reconstructs the target. When it fails,
 * it simply produces the original term.
 *
 * Note: This is precisely why it can be dangerous to use on humans if they 
 * have not been engorged first, since they will not have any redundant 
 * pieces to get rid of.
 *)
val reducio_body : env -> evar_map -> types -> types
