type 'a t = (Syntax.Name.t * 'a) list

let empty = []

let bind x v env = (x, v) :: env

exception UnboundIdentifier of Syntax.Name.t

let lookup x env =
  let rec aux = function
    | [] -> raise (UnboundIdentifier x)
    | (y, v) :: env -> if Syntax.Name.compare x y = 0 then v else aux env
  in
  aux env

let fold f = List.fold_left (fun a (x, v) -> f a x v)

let map f = List.map (fun (x, y) -> (x, f y))
