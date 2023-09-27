(* Streams as an existential type. *)

(* Without a [Skip] constructor, for simplicity. *)

(* ------------------------------------------------------------------------------ *)

(* When queried, a producer function returns one of the following: *)

type ('a, 's) step =
  | Done                           (* the stream is exhausted *)
  | Yield of 'a * 's    (* here is an element and a new state *)

(* The type of streams. *)

type 'a stream =
  | Stream:
              (* The [next] method: *) ('s -> ('a, 's) step) *
              (* The current state: *)  's
         (* together form a stream: *) -> 'a stream

(* ------------------------------------------------------------------------------ *)

(* Conversions between streams and lists, both ways. *)

let stream (xs : 'a list) : 'a stream =
  let next xs =
    match xs with
    |      [] -> Done
    | x :: xs -> Yield (x, xs)
  in
  Stream (next, xs)            (* packing an existential type *)

(* Since the function [next] that appears in the definition of [stream] is closed,
   it can be hoisted to the top level, under the name [stream_next]. *)

let stream_next xs =
  match xs with
  |      [] -> Done
  | x :: xs -> Yield (x, xs)

let stream (xs : 'a list) : 'a stream =
  Stream (stream_next, xs)

(* [unstream] is a CONSUMER function, and it is recursive, as it repeatedly
   queries the producer [xs], until it is exhausted. *)

(* [unstream] is in fact a special case of [foldr]. *)

(* One could also define it as a special case of [foldl]. That would require
   reversing the list at the end, but would allow the code to be tail-recursive. *)

let unstream (Stream (next, s) : 'a stream) : 'a list =
  let rec unfold s =
    match next s with
    | Done         -> []
    | Yield (x, s) -> x :: unfold s
  in
  unfold s

(* ------------------------------------------------------------------------------ *)

(* Basic functions on streams. *)

(* [return x] is a stream whose single element is [x]. *)

let return (x : 'a) : 'a stream =
  let next s =
    if s then Yield (x, false) else Done
  in
  Stream (next, true)          (* packing an existential type *)
(* [interval lo hi] is the stream of the integers from [lo] included
   to [hi] excluded. *)

let interval lo hi : int stream =
  let next i =
    if i < hi then Yield (i, i + 1) else Done
  in
  Stream (next, lo)

(* [map f xs] is the stream obtained by applying [f] in turn to each
   of the elements of the stream [xs]. *)

let map (f : 'a -> 'b) (xs : 'a stream) : 'b stream =
  let Stream (next, s) = xs in                   (* unpacking *)
  let next s =
    match next s with
    | Done         -> Done
    | Yield (x, s) -> Yield (f x, s)
  in
  Stream (next, s)                                 (* packing *)

(* [filter p xs] is the stream obtained by keeping only the elements
   that satisfy [p] in the stream [xs]. *)

(* Here, [next] is recursive. If the definition of the type [step] had
   a [Skip] constructor then we would be able to give a non-recursive
   definition of [next]. *)

let rec filter (p : 'a -> bool) (Stream (next, s) : 'a stream) =
  let next s =
    match next s with
    | Done         -> Done
    | Yield (x, s) -> if p x then Yield (x, s) else next s
  in
  Stream (next, s)

(* [append xs ys] is the concatenation of the streams [xs] and [ys]. *)

(* Here, [next] is recursive. If the definition of the type [step] had
   a [Skip] constructor then we would be able to give a non-recursive
   definition of [next]. *)

let append (Stream (next1, s1)) (Stream (next2, s2)) =
  let open Either in
  let rec next s =
    match s with
    | Left s1 ->
        begin match next1 s1 with
        | Done           -> next (Right s2)
        | Yield (x1, s1) -> Yield (x1, Left s1)
        end
    | Right s2 ->
        begin match next2 s2 with
        | Done           -> Done
        | Yield (x2, s2) -> Yield (x2, Right s2)
        end
  in
  Stream (next, Left s1)

(* EXERCISE: write [zip], [concatMap]. *)

(* [foldl f z xs] computes [List.fold_left f z (unstream xs)]. *)

(* This is a CONSUMER function, and it is recursive, as it repeatedly
   queries the producer [xs], until it is exhausted. *)

let foldl f z (Stream (next, s)) =
  let rec go z s =
    match next s with
    | Done         -> z
    | Yield (x, s) -> go (f x z) s
  in
  go z s

(* EXERCISE: write [foldr]. *)

(* [sum xs] is the sum of the elements of the stream [xs]. *)

let sum xs =
  foldl (+) 0 xs

(* ------------------------------------------------------------------------------ *)

(* Test. *)

let even x =
  x mod 2 = 0

let () =
  (* The sum of the even integers comprised between 0 and 12, inclusive. *)
  (* The expected result is 6 * 7 = 42. *)
  interval 0 13
  |> filter even
  |> sum
  |> Printf.printf "%d\n%!"
