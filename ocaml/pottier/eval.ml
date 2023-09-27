(* -------------------------------------------------------------------------- *)

(* A naive interpreter for a tiny language of expressions. *)

module Raw = struct

(* Expressions include integer constants, pairs, and projection. *)

type expr =
| EInt  of int
| EPair of expr * expr
| EFst  of expr
| ESnd  of expr

(* Values are tagged: there is a type [value] of all values. It is
   an algebraic data type with several branches. *)

type value =
| VInt  of int
| VPair of value * value

(* [as_pair v] checks (at runtime) that the value [v] is an object-level pair
   value and returns a meta-level pair of its components. *)

let as_pair (v : value) : value * value =
  match v with
  | VPair (v1, v2) ->
      v1, v2
  | _ ->
      assert false (* runtime error! *)

(* The naive interpreter. *)

let rec eval (e : expr) : value =
  match e with
  | EInt x ->
      VInt x
  | EPair (e1, e2) ->
      VPair (eval e1, eval e2)
  | EFst e ->
      fst (as_pair (eval e))
  | ESnd e ->
      snd (as_pair (eval e))

end (* Raw *)

(* -------------------------------------------------------------------------- *)

(* Play it again, Sam. This time, with GADTs. *)

module Typed = struct

(* Expressions are now statically typed. It is impossible to construct
   an ill-typed expression. *)

type _ expr =
| EInt  :               int ->       int expr
| EPair : 'a expr * 'b expr -> ('a * 'b) expr
| EFst  :    ('a * 'b) expr ->        'a expr
| ESnd  :    ('a * 'b) expr ->        'b expr

(* Similarly, values are statically typed. *)

type _ value =
| VInt  :                 int ->       int value
| VPair : 'a value * 'b value -> ('a * 'b) value

(* The auxiliary function [as_pair] now cannot fail: no runtime check is
   needed any more. *)

let as_pair : type a b . (a * b) value -> a value * b value
= function
  | VPair (v1, v2) ->
      v1, v2
  (* In this branch, we would learn [a * b = int], *)
  (* which is contradictory. *)
  (* | _ -> . *)

(* The interpreter now involves no runtime check. *)

(* The type of the interpreter, [a expr -> a value], reflects the fact that
   the type system that we have invented for expressions is sound:
   evaluating an expression of type [a] produces a value of type [a]. *)

let rec eval : type a . a expr -> a value
= function
  | EInt x ->
      (* We learn [a = int] so returning [VInt _] is OK. *)
      VInt x
  | EPair (e1, e2) ->
      (* For some types [a1] and [a2], we learn [a = a1 * a2] *)
      (* and we can assume [e1 : a1 expr] and [e2 : a2 expr]. *)
      VPair (eval e1, eval e2)
  | EFst e ->
      fst (as_pair (eval e))
  | ESnd e ->
      snd (as_pair (eval e))

end (* Typed *)

(* -------------------------------------------------------------------------- *)

(* Play it again, Sam. This time, with GADTs and with untagged values. *)

module Untagged = struct

(* The type of expressions is the same as above. *)

type _ expr =
| EInt  :               int ->       int expr
| EPair : 'a expr * 'b expr -> ('a * 'b) expr
| EFst  :    ('a * 'b) expr ->        'a expr
| ESnd  :    ('a * 'b) expr ->        'b expr

(* Values are no longer tagged. The type [value] disappears: there is no
   longer a need for a type of all values. Instead, evaluating an expression
   of type ['a expr] produces a value of type ['a]. *)

(* The auxiliary function [as_pair] disappears. *)

(* The type of the interpreter, [a expr -> a], reflects the fact that the
   type system that we have invented for expressions is sound: evaluating
   an expression of type [a] produces a value of type [a]. *)

let rec eval : type a . a expr -> a
= function
  | EInt x ->
      (* We learn [a = int] so returning an integer is OK. *)
      x                  (* no tagging! *)
  | EPair (e1, e2) ->
      (* For some types [a1] and [a2], we learn [a = a1 * a2] *)
      (* and we can assume [e1 : a1 expr] and [e2 : a2 expr]. *)
      (eval e1, eval e2) (* no tagging! *)
  | EFst e ->
      fst (eval e)       (* no untagging! *)
  | ESnd e ->
      snd (eval e)       (* no untagging! *)

end (* Untagged *)

(* -------------------------------------------------------------------------- *)

(* Runtime descriptions of types. *)

open Either
type ('a, 'b) sum = ('a, 'b) t

(* A value of type ['a ty] is a runtime representation of the type ['a]. *)

type 'a ty =
| TyInt  :                           int ty
| TySum  : 'a ty * 'b ty -> ('a, 'b) sum ty
| TyPair : 'a ty * 'b ty ->    ('a * 'b) ty

(* [show] is a generic (polymorphic, type-directed) function. *)

let rec show : type a . a ty -> a -> string =
  fun ty x ->
    match ty with
    | TyInt ->
        string_of_int x
    | TySum (ty1, ty2) ->
        begin match x with
        | Left x1  -> "left("  ^ show ty1 x1 ^ ")"
        | Right x2 -> "right(" ^ show ty2 x2 ^ ")"
        end
    | TyPair (ty1, ty2) ->
        let (x1, x2) = x in
        "(" ^ show ty1 x1 ^ ", " ^ show ty2 x2 ^ ")"

(* We can also analyze both arguments at once. *)

let rec show : type a . a ty -> a -> string =
  fun ty x ->
    match ty, x with
    | TyInt, x ->
        string_of_int x
    | TySum (ty1, _), Left x1 ->
        "left("  ^ show ty1 x1 ^ ")"
    | TySum (_, ty2), Right x2 ->
        "right(" ^ show ty2 x2 ^ ")"
    | TyPair (ty1, ty2), (x1, x2) ->
        "(" ^ show ty1 x1 ^ ", " ^ show ty2 x2 ^ ")"

(* [equal] is a generic (polymorphic, type-directed) equality test. *)

let rec equal : type a . a ty -> a -> a -> bool =
  fun ty x y ->
    match ty, x, y with
    | TyInt, x, y ->
        Int.equal x y
    | TySum (ty1, _), Left x1, Left y1 ->
        equal ty1 x1 y1
    | TySum (_, ty2), Right x2, Right y2 ->
        equal ty2 x2 y2
    | TySum _, Left _, Right _
    | TySum _, Right _, Left _ ->
        false
    | TyPair (ty1, ty2), (x1, x2), (y1, y2) ->
        equal ty1 x1 y1 && equal ty2 x2 y2

(* -------------------------------------------------------------------------- *)

(* A value of type [typed_expr] is a package of a runtime description
   of some type ['a] and an expression of type ['a]. The type ['a] is
   existentially quantified; outside of the package, it is unknown.
   In other words, [typed_expr] is an existential type. *)

open Untagged

type typed_expr =
| Pack   : 'a ty * 'a expr -> typed_expr

(* A bottom-up type inference algorithm. *)

exception IllTyped

let rec infer : Raw.expr -> typed_expr =
  function
  | Raw.EInt i ->
      Pack (TyInt, EInt i)
  | Raw.EPair (e1, e2)  ->
      let Pack (ty1, e1) = infer e1 in
      let Pack (ty2, e2) = infer e2 in
      let ty = TyPair (ty1, ty2) in
      Pack (ty, EPair (e1, e2))
  | Raw.EFst e ->
      let Pack (ty, e) = infer e in
      begin match ty with
      | TyPair (ty1, ty2) -> Pack (ty1, EFst e)
      | _                 -> raise IllTyped
      end
  | Raw.ESnd e ->
      let Pack (ty, e) = infer e in
      begin match ty with
      | TyPair (ty1, ty2) -> Pack (ty2, ESnd e)
      | _                 -> raise IllTyped
      end

(* -------------------------------------------------------------------------- *)

(* A value of type [('a, 'b) eq] is a runtime witness of the equality of the
   types ['a] and ['b]. *)

(* The type [eq] has appeared in OCaml 5.1 in the module [Type]. *)

type (_, _) eq =
| Equal: ('a, 'a) eq

(* A runtime equality check on type descriptors. *)

let rec equal : type a b . a ty -> b ty -> (a, b) eq =
  fun ty1 ty2 ->
    match ty1, ty2 with
    | TyInt, TyInt ->
        Equal
    | TyPair (ty1a, ty1b), TyPair (ty2a, ty2b) ->
        let Equal = equal ty1a ty2a in
        let Equal = equal ty1b ty2b in
        Equal
    | TySum (ty1a, ty1b), TySum (ty2a, ty2b) ->
        let Equal = equal ty1a ty2a in
        let Equal = equal ty1b ty2b in
        Equal
    | _, _ ->
        raise IllTyped

(* This type-checker checks that the type inferred for [e] is the expected
   type. This type is represented at runtime by the value [expected] and
   is named [a] at the type level. If this check succeeds then a copy of
   [e] at type [a expr] is returned. This expression is guaranteed to have
   type [a] and can therefore be evaluated without further runtime checks. *)

let check (type a) (e : Raw.expr) (expected : a ty) : a expr =
  let Pack (inferred, e) = infer e in
  let Equal = equal inferred expected in
  e

(* -------------------------------------------------------------------------- *)

(* Putting everything together, we can construct a raw expression;
   type-check it at a fixed expected type, such as [int]; run it;
   and print its value, which we know must be an integer value. *)

let () =
  Raw.(EFst (EPair (EInt 42, EInt 0)))
  |> (fun e -> check e TyInt)
  |> eval
  |> Printf.printf "%d\n%!"

(* We can also construct a raw expression; infer its type; run it;
   and print its value, whatever its type may be. *)

let () =
  let e = Raw.(EPair (EInt 42, EInt 0)) in
  let Pack (ty, e) = infer e in
  let v = eval e in
  Printf.printf "%s\n%!" (show ty v)
