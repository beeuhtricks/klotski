exception NotFound
type 'e rel = 'e -> 'e list
type 'e prop = 'e -> bool
type ('a, 'set) set_operations = {
  empty : 'set;
  mem : 'a -> 'set -> bool;
  add : 'a -> 'set -> 'set;
}
type ('configuration, 'move) puzzle = {
  move : 'configuration -> 'move -> 'configuration;
  possible_moves : 'configuration -> 'move list;
  final : 'configuration -> bool;
}
type piece_kind = S | H | V | C | X
type piece = piece_kind * int
val x : piece_kind * int
val s : piece_kind * int
val h : piece_kind * int
val c0 : piece_kind * int
val c1 : piece_kind * int
val c2 : piece_kind * int
val c3 : piece_kind * int
val v0 : piece_kind * int
val v1 : piece_kind * int
val v2 : piece_kind * int
val v3 : piece_kind * int
val all_pieces : piece list
type board = piece array array
val initial_board : (piece_kind * int) array array
val initial_board_simpler : (piece_kind * int) array array
val initial_board_trivial : (piece_kind * int) array array
type direction = { dcol : int; drow : int; }
type move = Move of piece * direction * board
val move : 'a -> move -> board
