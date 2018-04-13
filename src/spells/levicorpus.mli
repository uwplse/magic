open Environ
open Evd
open Term

(*
 * Levicorpus flips a body upside-down (inverts a proof body).
 * What the Levicorpus spell shows is that benign and
 * useful magic can sometimes be built on dark magic.
 * 
 * This is also a simplified version; consult me for details on how to handle 
 * other kinds of bodies, or see the PUMPKIN PATCH paper.
 *)

(* Invert a body in an environment *)
val levicorpus_body : env -> evar_map -> types -> types option
