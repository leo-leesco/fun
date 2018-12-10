open Printf

(* -------------------------------------------------------------------------- *)

(* A simple type of binary trees. *)

type tree =
  | Leaf
  | Node  of { data: int; left: tree; right: tree }

(* -------------------------------------------------------------------------- *)

(* Constructors. *)

let node data left right =
  Node { data; left; right }

let singleton data =
  node data Leaf Leaf

(* -------------------------------------------------------------------------- *)

(* A sample tree. *)

let christmas =
  node 6
    (node 2 (singleton 0) (singleton 1))
    (node 5 (singleton 3) (singleton 4))

(* -------------------------------------------------------------------------- *)

(* A test procedure. *)

let test name walk =
  printf "Testing %s...\n%!" name;
  walk christmas;
  walk christmas;
  flush stdout

(* -------------------------------------------------------------------------- *)

(* A recursive depth-first traversal, with postfix printing. *)

let rec walk (t : tree) : unit =
  match t with
  | Leaf ->
      ()
  | Node { data; left; right } ->
      walk left;
      walk right;
      printf "%d\n" data

let () =
  test "walk" walk

(* -------------------------------------------------------------------------- *)

(* A CPS traversal. *)

let rec walkk (t : tree) (k : unit -> 'a) : 'a =
  match t with
  | Leaf ->
      k()
  | Node { data; left; right } ->
      walkk left (fun () ->
      walkk right (fun () ->
      printf "%d\n" data;
      k()))

let walk t =
  walkk t (fun t -> t)

let () =
  test "walkk" walk

(* -------------------------------------------------------------------------- *)

(* A CPS-defunctionalized traversal. *)

type kont =
  | Init
  | GoneL of { data: int; tail: kont; right: tree }
  | GoneR of { data: int;              tail: kont }

let rec walkkd (t : tree) (k : kont) : unit =
  match t with
  | Leaf ->
      apply k ()
  | Node { data; left; right } ->
      walkkd left (GoneL { data; tail = k; right })

and apply k () =
  match k with
  | Init ->
      ()
  | GoneL { data; tail; right } ->
      walkkd right (GoneR { data; tail })
  | GoneR { data; tail } ->
      printf "%d\n" data;
      apply tail ()

let walk t =
  walkkd t Init

let () =
  test "walkkd" walk

(* CPS, defunctionalized, with in-place allocation of continuations. *)

(* [Init] is encoded by [Leaf].

   [GoneL { data; tail; right }] is encoded by:
   - setting [status] to [GoneL]; and
   - storing [tail] in the [left] field.
   - the [data] and [right] fields retain their original value.

   [GoneR { data; tail }] is encoded by:
   - setting [status] to [GoneR]; and
   - storing [tail] in the [right] field.
   - the [data] and [left] fields retain their original value.

   The [status] field is meaningful only when the memory block is
   being viewed as a continuation. If it is being viewed as a tree,
   then (by convention) [status] must be [GoneL]. (We could also
   let the type [status] have three values, but I prefer to use just
   two, for the sake of economy.)

   Does that sound crazy? Well, it is, in a way. *)

type status = GoneL | GoneR
type mtree  =  Leaf | Node of {
    data: int;           mutable status: status;
    mutable left: mtree; mutable right: mtree
  }
type mkont = mtree

(* Constructors. *)

let node data left right =
  Node { data; status = GoneL; left; right }

let singleton data =
  node data Leaf Leaf

(* A sample tree. *)

let christmas =
  node 6
    (node 2 (singleton 0) (singleton 1))
    (node 5 (singleton 3) (singleton 4))

(* A test. *)

let test name walk =
  printf "Testing %s...\n%!" name;
  walk christmas;
  walk christmas;
  flush stdout

(* The code. *)

let rec walkkdi (t : mtree) (k : mkont) : unit =
  match t with
  | Leaf ->
      (* We decide to let [apply] takes a tree as a second argument,
         instead of just a unit value. Indeed, in order to restore
         the [left] or [right] fields of [k], we need the address
         of the child [t] out of which we are coming. *)
      apply k t
  | Node ({ left; _ } as n) ->
      (* At this point, [t] is a tree.
         [n] is a name for its root record. *)
      (* Change this tree to a [GoneL] continuation. *)
      assert (n.status = GoneL);
      n.left (* n.tail *) <- k;
      (* [t] now represents a continuation. Go down into the left
         child, with this continuation. *)
      walkkdi left (t : mkont)

and apply (k : mkont) (child : mtree) : unit =
  match k with
  | Leaf -> ()
  | Node ({ status = GoneL; left = tail; right; _ } as n) ->
      (* We are popping a [GoneL] frame, that is, coming out of
         a left child. *)
      n.status <- GoneR;       (* update continuation! *)
      n.left <- child;    (* restore orig. left child! *)
      n.right (* n.tail *) <- tail;
      (* [k] now represents a [GoneR] continuation. Go down into
         the right child, with [k] as a continuation. *)
      walkkdi right k
  | Node ({ data; status = GoneR; right = tail; _ } as n) ->
      printf "%d\n" data;
      n.status <- GoneL;     (* change back to a tree! *)
      n.right <- child;  (* restore orig. right child! *)
      (* [k] now represents a valid tree again. *)
      apply tail (k : mtree)

let walk t =
  walkkdi t Leaf

let () =
  test "walkkdi" walk
