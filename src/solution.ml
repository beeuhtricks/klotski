open Prelude

let rec loop p f x =
  if p x
  then x
  else loop p f (f x)

let rec exists p l =
  match l with
  | [] -> false
  | x :: _ when p x -> true
  | _ :: xs -> exists p xs

let rec find p l =
  match l with
  | [] -> raise NotFound
  | x :: _ when p x -> x
  | _ :: xs -> find p xs

(* --- Part A: A Generic Problem Solver --- *)

let near x =
  let rec count accu i =
    if (x - 2) <= i && i <= (x + 2)
    then count (i :: accu) (i - 1)
    else accu
  in
  count [] (x + 2)

let flat_map r =
  let rec flatten accu = function
    | [] -> List.rev accu
    | x :: xs -> flatten (r x @ accu) xs
  in
  flatten []

let rec iter_rel rel n =
  if n <= 1
  then rel
  else fun x -> flat_map rel ((iter_rel rel (n - 1)) x)

let solve r p x = loop (exists p) (flat_map r) [x] |> find p

let solve_path r p x =
  let path_r l = List.map (fun x -> x :: l) (r (List.hd l)) in
  let path_p l = p (List.hd l) in
  solve path_r path_p [x]
  |> List.rev

let archive_map opset r (s, l) =
  let next_list = flat_map r l in
  let rec dedup accuS accuL = function
    | [] -> (accuS, accuL)
    | x :: xs when not (opset.mem x accuS) && not (opset.mem x s) -> dedup (opset.add x accuS) (x :: accuL) xs
    | _ :: xs -> dedup accuS accuL xs
  in
  dedup s [] next_list

let solve' opset r p x =
  let pl (_, l) = exists p l in
  let rl (s, l) = archive_map opset r (s, l) in
  loop pl rl (opset.empty, [x]) |> fun (_, l) -> find p l

let solve_path' opset r p x =
  let path_r l = List.map (fun x -> x :: l) (r (List.hd l)) in
  let path_p l = p (List.hd l) in
  solve' opset path_r path_p [x]
  |> List.rev

let solve_puzzle p opset c =
  let update_puzzle c = List.map (fun m -> p.move c m) (p.possible_moves c) in
  solve_path' opset update_puzzle p.final c

(* --- Part B: A Solver for Klotski --- *)

let final (board: board) : bool = match board with
  | [|[| _ ;   _   ;   _   ; _ |] ;
      [| _ ;   _   ;   _   ; _ |] ;
      [| _ ;   _   ;   _   ; _ |] ;
      [| _ ; (S,_) ; (S,_) ; _ |] ;
      [| _ ; (S,_) ; (S,_) ; _ |] |] -> true
  | _ -> false

let cmp p1 p2 = match (fst p1, fst p2) with
  | (S, S) | (H, H) | (X, X) | (C, C) | (V, V) -> 0
  | (S, _) -> 1
  | (_, S) -> -1
  | (H, _) -> 1
  | (_, H) -> -1
  | (C, _) -> 1
  | (_, C) -> -1
  | (V, _) -> 1
  | _ -> -1

let cmp_ineff p1 p2 = match (fst p1, fst p2) with
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

exception Illegal

let move_piece board piece { drow; dcol } =
  let new_board = Array.make 5 (Array.make 4 x)
  and old_board = Array.map Array.copy board in
  let empty = x in
  try (for y = 0 to 4 do
         for x = 0 to 3 do
           if old_board.(y).(x) = piece
           then let dest_piece = old_board.(y + drow).(x + dcol) in
                if cmp dest_piece empty = 0 || (dest_piece = piece)
                then let dest_row = Array.copy new_board.(y + drow) in
                     (dest_row.(x + dcol) <- old_board.(y).(x);
                      new_board.(y + drow) <- dest_row)
                else raise Illegal;
           else if old_board.(y).(x) = empty
           then ()
           else let new_row = Array.copy new_board.(y) in
                (new_row.(x) <- old_board.(y).(x); new_board.(y) <- new_row)
         done
       done);
      Some new_board
  with _ -> None

let possible_moves board =
  let empty = x in
  let dirs = [|{drow=0;dcol=1}; {drow=0;dcol= -1}; {drow=1;dcol=0}; {drow= -1;dcol=0}|] in
  let adjacent x y =
    let accu = ref [] in
    if x < 3
    then (accu := board.(y).(x + 1) :: !accu)
    else ();
    if x > 0
    then (accu := board.(y).(x - 1) :: !accu)
    else ();
    if y < 4
    then (accu := board.(y + 1).(x) :: !accu)
    else ();
    if y > 0
    then (accu := board.(y - 1).(x) :: !accu)
    else ();
    !accu
  in

  let adjs = ref [] in

  for y = 0 to 4 do
    for x = 0 to 3 do
      if cmp board.(y).(x) empty = 0
      then (adjs := (adjacent x y) @ !adjs)
      else ();
    done
  done;

  adjs := List.sort_uniq cmp_ineff !adjs;

  let moves = ref [] in

  for n = 0 to List.length !adjs - 1 do
    let cpiece = List.nth !adjs n in
    if cpiece <> empty
    then for d = 0 to 3 do
           let dir = dirs.(d) in
           match move_piece board cpiece dir with
           | None -> ()
           | Some board' -> moves := Move(cpiece, dir, board') :: !moves;
         done
    else ();
  done;
  !moves

exception Neg
exception Pos

module BoardSet = Set.Make (struct
                      type t = board
                      let compare b1 b2 =
                        try
                          (for i = 0 to 4 do
                             let r1 = b1.(i) and r2 = b2.(i) in
                             for j = 0 to 3 do
                               let result = cmp_ineff r1.(j) r2.(j) in
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

module BoardKindSet = Set.Make (struct
                          type t = board
                          let compare b1 b2 =
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

let klotski = { move; possible_moves; final }

let solve_klotski initial_board =
  let opset = { empty = BoardKindSet.empty;
                mem = (fun l s -> BoardKindSet.mem (List.hd l) s);
                add = (fun l s -> BoardKindSet.add (List.hd l) s) }
  in
  solve_puzzle klotski opset initial_board

let solved = solve_klotski initial_board_trivial
and solved_harder = solve_klotski initial_board_simpler
and solved_hardest = solve_klotski initial_board
