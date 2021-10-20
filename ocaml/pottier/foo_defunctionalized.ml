type (_, _) closure =
  | NEqZero   : (int, bool) closure
  | Increment : (int,  int) closure

let rec apply =
  fun (type a b) (this : (a, b) closure) (that : a) : b ->
    match this with
    | NEqZero ->
        let x = that in
        x <> 0
    | Increment ->
        let x = that in
        x + 1

let rec filter p xs =
  match xs with
  | [] ->
      []
  | x :: xs ->
      if apply p x then x :: filter p xs else filter p xs

let rec map f xs =
  match xs with
  | [] ->
      []
  | x :: xs ->
      apply f x :: map f xs

let foo (xs : int list) : int list =
  filter NEqZero (map Increment xs)

let () =
  assert (foo [ -1; 0; +1 ] = [ 1; 2 ]);
  Printf.printf "Success.\n"
