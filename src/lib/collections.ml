(*
 * Auxiliary functions on collections
 *)

(* seq from template-coq *)
let rec range (min : int) (max : int) : int list =
  if min < max then
    min :: range (min + 1) max
  else
    []

(* Creates a list from the index 1 to max, inclusive *)
let from_one_to (max : int) : int list =
  range 1 (max + 1)
        
(*
 * Get values from a list of optionals only if every optional is some
 * Otherwise, return the empty list
 *)
let get_all_or_none (l : 'a option list) : 'a list =
  if List.for_all Option.has_some l then
    List.map Option.get l
  else
    []

(* Gets the last element of l *)
let last (l : 'a list) = List.hd (List.rev l)

(* Map3 *)
let rec map3 (f : 'a -> 'b -> 'c -> 'd) l1 l2 l3 : 'd list =
  match (l1, l2, l3) with
  | ([], [], []) ->
     []
  | (h1 :: t1, h2 :: t2, h3 :: t3) ->
     let r = f h1 h2 h3 in r :: map3 f t1 t2 t3
