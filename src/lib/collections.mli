(*
 * Auxiliary functions on collections
 *)

(* [min, max) *)
val range : int -> int -> int list

(* [1, max] *)
val from_one_to : int -> int list
        
(*
 * Get values from a list of optionals only if every optional is some
 * Otherwise, return the empty list
 *)
val get_all_or_none : 'a option list -> 'a list

(* Gets the last element of l *)
val last : 'a list -> 'a

(* Map3 *)
val map3 : ('a -> 'b -> 'c -> 'd) -> 'a list -> 'b list -> 'c list -> 'd list
