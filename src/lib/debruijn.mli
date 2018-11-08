(*
 * The ugliest part of magic, DeBruijn indices.
 *
 * This is not quite a canonical shift/unshift like you're used to in theory.
 * In particular, depending on the term you pass it, unshift (shift t) might
 * not be t. There's a reason for this, but you can ignore it for
 * the sake of this plugin.
 *)

open Constr

(* Decrement the relative indexes of a term t by n *)
val unshift_by : int -> types -> types

(* Increment the relative indexes of a term t by n *)
val shift_by : int -> types -> types

(* Increment the relative indexes of a term t by one *)
val shift : types -> types

(* Decrement the relative indexes of a term t by one *)
val unshift : types -> types
