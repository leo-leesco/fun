(**A value of type [('a, 'b) eq] is a runtime witness of the equality of the
   types ['a] and ['b]. *)
type ('a, 'b) eq =
  | Eq : ('a, 'a) eq
