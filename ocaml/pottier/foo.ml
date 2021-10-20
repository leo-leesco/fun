let rec filter p xs =
  match xs with
  | [] ->
      []
  | x :: xs ->
      if p x then x :: filter p xs else filter p xs

let rec map f xs =
  match xs with
  | [] ->
      []
  | x :: xs ->
      f x :: map f xs

let foo (xs : int list) : int list =
  filter (fun x -> x <> 0) (map (fun x -> x + 1) xs)

let () =
  assert (foo [ -1; 0; +1 ] = [ 1; 2 ]);
  Printf.printf "Success.\n"
