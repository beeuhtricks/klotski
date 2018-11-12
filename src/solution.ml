open Prelude

let rec loop (p : 'a -> bool) (f : 'a -> 'a) (x : 'a) : 'a =
  if p x
  then x
  else loop p f (f x)

let rec exists (p : 'a -> bool) (l : 'a list) : bool =
  match l with
  | [] -> false
  | x :: _ when p x -> true
  | _ :: xs -> exists p xs

let rec find (p : 'a -> bool) (l : 'a list) : 'a =
  match l with
  | [] -> raise NotFound
  | x :: _ when p x -> x
  | _ :: xs -> find p xs

(* --- Part A: A Generic Problem Solver --- *)

let near (x : int) : int list =
  let rec count accu i =
    if (x - 2) <= i && i <= (x + 2)
    then count (i :: accu) (i - 1)
    else accu
  in
  count [] (x + 2)

let rec flat_map (r : 'e rel) : 'e list -> 'e list =
  let rec flatten accu = function
    | [] -> List.rev accu
    | x :: xs -> flatten (r x @ accu) xs
  in
  flatten []

let rec iter_rel (rel : 'e rel) (n : int) : 'e rel =
  if n <= 1
  then rel
  else fun x -> flat_map rel ((iter_rel rel (n - 1)) x)

let solve (r : 'a rel) (p : 'a prop) (x : 'a) : 'a =
  loop (exists p) (flat_map r) [x] |> find p

let solve_path (r : 'a rel) (p : 'a prop) (x : 'a) : 'a list =
  let path_r l = List.map (fun x -> x :: l) (r (List.hd l)) in
  let path_p l = p (List.hd l) in
  solve path_r path_p [x]
  |> List.rev

let archive_map (opset : ('a, 'set) set_operations) (r : 'a rel) ((s, l) : ('set * 'a list)) : ('set * 'a list) =
  let l' = List.filter (fun x -> not (opset.mem x s)) (flat_map r l)
  and update s x = opset.add x s in
  let s' = List.fold_left update s l' in
  (s', l')

let solve' (opset : ('a, 'set) set_operations) (r : 'a rel) (p : 'a prop)  (x : 'a) : 'a =
  let pl (s, l) = exists p l in
  let rl (s, l) = archive_map opset r (s, l) in
  loop pl rl (opset.empty, [x]) |> fun (_, l) -> find p l

let solve_path'  (opset : ('a list, 'set) set_operations) (r : 'a rel) (p : 'a prop)  (x : 'a) : 'a list =
  let path_r l = List.map (fun x -> x :: l) (r (List.hd l)) in
  let path_p l = p (List.hd l) in
  solve' opset path_r path_p [x]
  |> List.rev

let solve_puzzle (p : ('c, 'm) puzzle) (opset : ('c list, 's) set_operations) (c : 'c) : 'c list  =
  let update_puzzle c = List.map (fun m -> p.move c m) (p.possible_moves c) in
  solve_path' opset update_puzzle p.final c

(* --- Part B: A Solver for Klotski --- *)

let final (board: board) : bool = match board with
  | [| [| _ ;   _   ;   _   ; _ |] ;
       [| _ ;   _   ;   _   ; _ |] ;
       [| _ ;   _   ;   _   ; _ |] ;
       [| _ ; (S,_) ; (S,_) ; _ |] ;
       [| _ ; (S,_) ; (S,_) ; _ |] |] -> true
  | _ -> false

exception OutOfBounds

let move_piece (board : board) (piece : piece) ({ drow; dcol } : direction) : board option =
  let rec find_piece (i, j) = match board.(i).(j) with
    | p when p = piece -> (j, i)
    | _ when j < 3 -> find_piece (i, j + 1)
    | _ when i < 4 -> find_piece (i + 1, 0)
    | _ -> (0, 0)
  in
  let left_upper = find_piece (0,0) in
  let old_pos = match fst piece with
    | S -> [left_upper; (fst left_upper + 1, snd left_upper); (fst left_upper, snd left_upper + 1); (fst left_upper + 1, snd left_upper + 1)]
    | H -> [left_upper; (fst left_upper + 1, snd left_upper)]
    | V -> [left_upper; (fst left_upper, snd left_upper + 1)]
    | _ -> [left_upper] in
  let shift (x, y) = (x + dcol, y + drow) in
  let new_pos = List.rev_map shift old_pos |> List.rev in
  let empty board (x, y) =
    try
      match board.(y).(x) with
    | (X, _) -> true
    | _ -> false
    with _ -> false in
  let empty_or_me = fun accu (x, y) ->
    try (empty board (x, y) || board.(y).(x) = piece) && accu
    with
    _ -> false
  in
  let spaces_empty = List.fold_left empty_or_me true new_pos in
  if not spaces_empty
  then None
  else
    let new_board = Array.map Array.copy board in
    let update (x, y) = Array.set new_board.(y) x piece in
    let erase (x, y) = Array.set new_board.(y) x (X, 0) in
  List.iter erase old_pos;
  List.iter update new_pos;
  Some new_board

let possible_moves (board : board) : move list =
  let dirs = [{ drow = -1; dcol = 0 }; { drow = 1; dcol = 0 }; { drow = 0; dcol = 1 }; { drow = 0; dcol = -1 }] in
  let get_moves piece =
    List.fold_left (fun accu dir ->
        match move_piece board piece dir with
        | None -> accu
        | Some board' -> (Move (piece, dir, board')) :: accu) [] dirs
  in
  List.map get_moves all_pieces |> List.flatten

let klotski : (board, move) puzzle = { move; possible_moves; final }

exception Neg
exception Pos

module BoardSet = Set.Make (struct
    type t = board
    let compare (b1 : board) (b2 : board) : int =
      let cmp p1 p2 = match (fst p1, fst p2) with
        | (S, S) | (H, H) | (X, X) -> 0
        | (C, C) | (V, V) -> compare (snd p1) (snd p2)
        | (S, _) -> 1
        | (_, S) -> -1
        | (H, _) -> 1
        | (_, H) -> -1
        | (C, _) -> 1
        | (_, C) -> -1
        | (V, _) -> 1
        | (_, V) -> -1
      in
      try
        (for i = 0 to 4 do
           let r1 = b1.(i) and r2 = b2.(i) in
           for j = 0 to 3 do
             let p1 = r1.(j) and p2 = r2.(j) in
             let result = cmp p1 p2 in
             if result < 0
             then raise Neg
             else if result > 0
             then raise Pos
             else ()
           done
         done);
        0
      with
      | Neg -> -1
      | Pos -> 1
  end)

let solve_klotski (initial_board : board) : board list =
  let opset = { empty = BoardSet.empty;
                mem = (fun l s -> BoardSet.mem (List.hd l) s);
                add = (fun l s -> BoardSet.add (List.hd l) s) }
  in
  solve_puzzle klotski opset initial_board

let solved = solve_klotski initial_board_simpler
