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
exception Illegal

let move_piece (board : board) (piece : piece) ({ drow; dcol } : direction) : board option =
  let new_board = Array.make 5 (Array.make 4 x)
  and old_board = Array.map Array.copy board in
  try (for i = 0 to 4 do
         for j = 0 to 3 do
           if old_board.(i).(j) = piece
           then let dest_piece = old_board.(i + drow).(j + dcol) in
             if (dest_piece = x) || (dest_piece = piece)
             then let dest_row = Array.copy new_board.(i + drow) in
               (dest_row.(j + dcol) <- old_board.(i).(j);
                new_board.(i + drow) <- dest_row)
             else raise Illegal;
           else if old_board.(i).(j) = x
           then ()
           else let new_row = Array.copy new_board.(i) in
             (new_row.(j) <- old_board.(i).(j); new_board.(i) <- new_row)
         done
       done);
    Some new_board
  with _ -> None


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
        | _ -> -1
      in
      try
        (for i = 0 to 4 do
           let r1 = b1.(i) and r2 = b2.(i) in
           for j = 0 to 3 do
             let result = cmp r1.(j) r2.(j) in
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
