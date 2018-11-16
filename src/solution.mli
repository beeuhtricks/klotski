open Prelude

val loop : ('a -> bool) -> ('a -> 'a) -> 'a -> 'a
val exists : ('a -> bool) -> 'a list -> bool
val find : ('a -> bool) -> 'a list -> 'a
val near : int -> int list

val flat_map : 'e rel -> ('e list -> 'e list)
val iter_rel : 'e rel -> int -> 'e rel
val solve : 'a rel -> 'a prop -> 'a -> 'a
val solve_path : 'a rel -> 'a prop -> 'a -> 'a list

val archive_map : ('a, 'set) set_operations -> 'a rel ->
  ('set * 'a list) -> ('set * 'a list)
val solve' : ('a, 'set) set_operations -> 'a rel -> 'a prop -> 'a -> 'a
val solve_path' : ('a list, 'set) set_operations -> 'a rel ->
  'a prop -> 'a -> 'a list
val solve_puzzle : ('c, 'm) puzzle -> ('c list, 's) set_operations -> 'c -> 'c list
exception Illegal

val final : board -> bool
val move_piece : board -> piece -> direction -> board option
val possible_moves : board -> move list
exception Neg
exception Pos
module BoardSet : Set.S with type elt = board
val solve_klotski : board -> board list
