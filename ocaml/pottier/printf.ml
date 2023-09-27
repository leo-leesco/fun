(* First attempt. In this simple approach, we can implement [printf]
   and [bprintf], both of which have eventual return type [unit]. We
   cannot implement [sprintf] or [kprintf], which have other eventual
   return types. *)

(* In our code, [fprintf] and [kprintf] have the same type, but they have
   different specs: [fprintf emit desc] may call [emit] many times in
   succession to emit its output in several pieces, whereas [kprintf k
   desc] is expected to invoke the continuation [k] exactly once.

   So, [let fprintf = kprintf] is a correct (suboptimal) implementation,
   whereas [let kprintf = fprintf] would be incorrect. *)

module Simple = struct

  type _ desc =
    | Nil  :                                         unit desc
    | Lit  :            string * 'a desc ->            'a desc
    | Hole : ('data -> string) * 'a desc -> ('data -> 'a) desc

  let fprintf (type a) (emit : string -> unit) (desc : a desc) : a =
    let rec eval : type a . a desc -> a =
      fun desc ->
        match desc with
        | Nil ->
            ()
        | Lit (s, desc) ->
            emit s;
            eval desc
        | Hole (to_string, desc) ->
            fun x ->
              emit (to_string x);
              eval desc
    in
    eval desc

  let printf desc =
    let emit = print_string in
    fprintf emit desc

  let bprintf b desc =
    let emit = Buffer.add_string b in
    fprintf emit desc

  (* [sprintf] cannot be implemented:
  let sprintf desc <args> =
    let b = Buffer.create 128 in
    let emit = Buffer.add_string b in
    fprintf emit desc <args>;
    Buffer.contents b
   *)

  (* Sugar. *)

  module Sugar = struct
    let nil = Nil
    let lit s desc = Lit (s, desc)
    let d desc = Hole (string_of_int, desc)
    let s desc = Hole (Fun.id, desc)
  end

  (* This example prints "2 * 12 = 24\n". *)

  open Sugar

  let desc =
    d @@ lit " * " @@ s @@ lit " = " @@ d @@ lit "\n" @@ nil

  let () =
    print_endline "Simple:";
    printf desc 2 "12" 24;
    flush stdout

end

(* Second attempt. [fprintf] gains a new parameter, a function [finished],
   which is invoked after we are done evaluating the descriptor. The result
   of the call [finished()] becomes the result of [fprintf]. This explains
   why in the [Nil] case we need the type equality [r = a]. *)

module Rich = struct

  type (_, _) desc =
    | Nil  : ('r, 'r) desc
    | Lit  : string * ('a, 'r) desc -> ('a, 'r) desc
    | Hole : ('data -> string) * ('a, 'r) desc -> ('data -> 'a, 'r) desc

  let fprintf (type a r) emit (finished : unit -> r) (desc : (a, r) desc) : a =
    let rec eval : type a . (a, r) desc -> a =
      fun desc ->
        match desc with
        | Nil ->
            finished()
        | Lit (s, desc) ->
            emit s;
            eval desc
        | Hole (to_string, desc) ->
            fun x ->
              emit (to_string x);
              eval desc
    in
    eval desc

  let printf desc =
    let emit = print_string
    and finished () = () in
    fprintf emit finished desc

  let bprintf b desc =
    let emit = Buffer.add_string b
    and finished () = () in
    fprintf emit finished desc

  let sprintf desc =
    let b = Buffer.create 128 in
    let emit = Buffer.add_string b
    and finished () = Buffer.contents b in
    fprintf emit finished desc

  let kprintf k desc =
    let b = Buffer.create 128 in
    let emit = Buffer.add_string b
    and finished () = k (Buffer.contents b) in
    fprintf emit finished desc

  (* Sugar. *)

  module Sugar = struct
    let nil = Nil
    let lit s desc = Lit (s, desc)
    let d desc = Hole (string_of_int, desc)
    let s desc = Hole (Fun.id, desc)
  end

  (* This example prints "2 * 12 = 24\n". *)

  (* Our examples use [desc] several times, and pass it as an argument to
     several [*printf] functions that have distinct eventual return types.
     Therefore, we need [desc] to have a polymorphic type. Unfortunately,
     when the above sugar is used in the definition of [desc], it receives
     a monomorphic type. Indeed, because [lit], [d], and [s] are functions,
     as opposed to data constructors, the value restriction forbids
     generalization. So, one must either abandon the sugar or define
     several copies of [desc] (which we do below). *)

  (* Assuming a working Merlin, typing Ctrl-C Ctrl-T shows the type of the
     identifier under the cursor. Do this to see the type of [desc]. *)

  (* [desc] without sugar receives a polymorphic type: *)
  let desc =
    Hole (string_of_int,
    Lit (" * ",
    Hole (Fun.id,
    Lit (" = ",
    Hole (string_of_int,
    Lit ("\n",
    Nil))))))

  (* [desc] with sugar receives a monomorphic type: *)
  open Sugar
  let desc =
    d @@ lit " * " @@ s @@ lit " = " @@ d @@ lit "\n" @@ nil

  let () =
    print_endline "Rich:";
    (* Test [printf]: *)
    printf desc 2 "12" 24;
    (* Test [bprintf]: *)
    let b = Buffer.create 128 in
    bprintf b desc 2 "12" 24;
    print_string (Buffer.contents b)

  (* [desc] with sugar receives a monomorphic type: *)
  let desc =
    d @@ lit " * " @@ s @@ lit " = " @@ d @@ lit "\n" @@ nil

  let () =
    (* Test [sprintf]: *)
    let s = sprintf desc 2 "12" 24 in
    print_string s

  (* [desc] with sugar receives a monomorphic type: *)
  let desc =
    d @@ lit " * " @@ s @@ lit " = " @@ d @@ lit "\n" @@ nil

  let () =
    (* Test [kprintf]: *)
    let k = print_string in
    kprintf k desc 2 "12" 24

  let () =
    (* Done. *)
    flush stdout

end

(* Third attempt, adapted from the paper by Danvy, Keller and Puech (2014).
   The type [(a, r) desc] still has two parameters, and they have the same
   meaning as above. However, instead of viewing descriptors as lists with
   a [Nil] constructor and several [Cons] constructors ([Lit] and [Hole]),
   this time we view [Lit] and [Hole] as leaves and we use a binary descriptor
   concatenation constructor [Seq]. *)

module DanvyKellerPuech = struct

  type (_, _) desc =
    | Lit  :                        string ->          ('a, 'a) desc
    | Hole :             ('data -> string) -> ('data -> 'a, 'a) desc
    | Seq  : ('a, 'b) desc * ('b, 'c) desc ->          ('a, 'c) desc

  let rec kprintf : type a r . (a, r) desc -> (string -> r) -> a =
    fun desc k ->
      match desc with
      | Lit s ->
          k s
      | Hole to_string ->
          fun x -> k (to_string x)
      | Seq (desc1, desc2) ->
          kprintf desc1 @@ fun s1 ->
          kprintf desc2 @@ fun s2 ->
          k (s1 ^ s2)

  (* In OCaml's standard library, [kprintf] expects [k] first, then [desc]. *)
  let kprintf k desc =
    kprintf desc k

  let printf desc =
    let k = print_string in
    kprintf k desc

  let bprintf b desc =
    let k = Buffer.add_string b in
    kprintf k desc

  let sprintf desc =
    let k = Fun.id in
    kprintf k desc

  let fprintf =
    kprintf
    (* In our code, [fprintf] and [kprintf] have the same type, but they have
       different specs: [fprintf emit desc] may call [emit] many times in
       succession to emit its output in several pieces, whereas [kprintf k
       desc] is expected to invoke the continuation [k] exactly once.
       So, [let fprintf = kprintf] is a correct (suboptimal) implementation. *)

  (* The following is a more efficient implementation of [fprintf] which
     does not use string concatenation, calls [emit] many times, and
     allocates at most one [Seq] block (instead of two closures) when
     evaluating a [Seq] node. *)

  let fprintf : type a . (string -> unit) -> (a, unit) desc -> a =
  fun emit desc ->

    let rec eval : type a . (a, unit) desc -> a =
      fun desc ->
        match desc with
        | Lit s ->
            emit s
        | Hole to_string ->
            fun x ->
              emit (to_string x)
        | Seq (desc1, desc2) ->
            eval_seq desc1 desc2

    (* [eval_seq] can be viewed as a specialized version of [eval] for
       the case where its argument is [Seq (_, _)]. *)

    and eval_seq : type a b . (a, b) desc -> (b, unit) desc -> a =
      fun desc1 desc2 ->
        match desc1 with
        | Lit s ->
            emit s;
            eval desc2
        | Hole to_string ->
            fun x ->
              emit (to_string x);
              eval desc2
        | Seq (desc1a, desc1b) ->
            (* Re-associate the two [Seq] nodes on the fly. *)
            eval_seq desc1a (Seq (desc1b, desc2))

    in eval desc

  (* Sugar. *)

  module Sugar = struct
    let lit s = Lit s
    let d = Hole string_of_int
    let s = Hole Fun.id
    let (^) desc1 desc2 = Seq (desc1, desc2)
  end

  (* This example prints "2 * 12 = 24\n". *)

  open Sugar
  let desc =
    d ^ lit " * " ^ s ^ lit " = " ^ d ^ lit "\n"

  let () =
    print_endline "Danvy-Keller-Puech:";
    (* Test [printf]: *)
    printf desc 2 "12" 24;
    (* Test [bprintf]: *)
    let b = Buffer.create 128 in
    bprintf b desc 2 "12" 24;
    print_string (Buffer.contents b)

  let desc =
    d ^ lit " * " ^ s ^ lit " = " ^ d ^ lit "\n"

  let () =
    (* Test [sprintf]: *)
    let s = sprintf desc 2 "12" 24 in
    print_string s

  let desc =
    d ^ lit " * " ^ s ^ lit " = " ^ d ^ lit "\n"

  let () =
    (* Test [kprintf]: *)
    let k = print_string in
    kprintf k desc 2 "12" 24

  let () =
    (* Done. *)
    flush stdout

end
