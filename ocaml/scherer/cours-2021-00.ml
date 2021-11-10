(* this file was live-programmed during the course

   Effects, lecture 0
   November 10th, 2021
*)

(* Variation 0 *)
type expr =
  | Int of int
  | Add of expr * expr

let rec eval = function
  | Int n -> n
  | Add (a, b) -> eval a + eval b
                 
let example =
  Add (Int 20, Add (Int 20, Int 2))


(* Variation 1: option as a failure effect *)
type expr =
  | Int of int
  | Div of expr * expr

(* indirect-style version *)
let rec eval : expr -> int option =
  function
  | Int n -> Some n
  | Div (a, b) ->
    match eval a with
    | None -> None
    | Some va ->
    match eval b with
    | None -> None
    | Some vb ->
    if vb = 0 then None
    else Some (va / vb)


val bind : 'a option -> ('a -> 'b option) -> 'b option
let return v = Some v
let bind a f =
  match a with
  | None -> None
  | Some va -> f va
let fail = None

let ( let* ) = bind

(* direct-style version *)
let rec eval : expr -> int option =
  function
  | Int n -> return n
  | Div (a, b) ->
    let* va = eval a in
    let* vb = eval b in
    if vb = 0 then fail
    else return (va / vb)

let example =
  Div (Int 20, Int 2)


(* Counting effect *)
type count = Count of int
let return : 'a -> 'a * count =
  fun x -> x, Count 0

let ( let* ) : 'a * count -> ('a -> 'b * count) -> 'b * count =
  fun (va, Count ca) f ->
    let (vb, Count cb) = f va in 
    vb, Count (ca + cb)

(* A state effect: random number generator (RNG) *)
module RngEval (Rng : sig
  type t
  val init : int array -> t
  val next : max:int -> t -> int * t
end) = struct
  type expr =
    | Int of int
    | Add of expr * expr
    | Random of int

  type 'a with_rng = Rng.t -> 'a * Rng.t
  let return (v : 'a) : 'a with_rng =
    fun rng -> (v, rng)

  let bind (a : 'a with_rng) (f : 'a -> 'b with_rng) 
    : 'b with_rng
    =
    fun rng ->
    let va, rng = a rng in
    f va rng
  let ( let* ) = bind

  let rec eval e rng : int * Rng.t =
    match e with
    | Int n -> n, rng
    | Random bound ->
      Rng.next ~max:bound rng
    | Add (a, b) ->
      let va, rng = eval a rng in
      let vb, rng = eval b rng in
      va + vb, rng
      
  let rec eval e : int with_rng =
    match e with
    | Int n -> return n
    | Random bound ->
      Rng.next ~max:bound
    | Add (a, b) ->
      let* va = eval a in
      let* vb = eval b in
      return (va + vb)
end

