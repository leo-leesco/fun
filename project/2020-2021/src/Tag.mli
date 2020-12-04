open Eq

(**A tag of type ['a tag] is a runtime representation of the type ['a]. *)
type _ tag

(**[new_tag()] extends the type [tag] with a new inhabitant and returns it. *)
val new_tag : unit -> 'a tag

(**[equal tag1 tag2] compares the tags [tag1] and [tag2]. If they are equal,
   then [Some Eq] is returned, providing a runtime witness of the equality of
   the types ['a1] and ['a2]. Otherwise, [None] is returned. *)
val equal : 'a1 tag -> 'a2 tag -> ('a1, 'a2) eq option
