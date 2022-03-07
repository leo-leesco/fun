# Applicative functors

Reminder: monoidal categories (C, ⊗) with
  - an object 1{C}
  - a functor ⊗ : C×C → C

An *applicative functor* T is a functor (C → C) equipped with:
  - unit : 1{C} → T(1{C})
  - pair : T(A) ⊗ T(B) → T(A ⊗ B)
    (natural in A, B)

with a strength: A ⊗ T(B) → T(A ⊗ B)



On the programming side:
  - map : ('a -> 'b) -> 'a t -> 'b t
  - unit : unit t
  - pair : 'a t -> 'b t -> ('a * 'b) t

Exercises:
  - pure : A → T(A)
  - pure : 'a -> 'a t

    ≃     A⊗unit       strength    T(≃)
  A → A⊗1{C} → A⊗T(1{C}) → T(A⊗1{C}) → T(A)

  let pure v =
    map (fun () -> v) unit


Binding operators:

  let ( let+ ) (t : 'a t) (f : 'a -> 'b) : 'b t = map f t
  let ( and+ ) = pair 

Example:
  let pure v =
    let+ () = unit in v

Exercise:

  Implement
    val traverse : 'a t list -> 'a list t
  In two versions:
    1. using the monadic interface
         return / let*  (/ let+ )
    2. using the applicative interface
         unit|pure / let+ / and+

let rec traverse : 'a m list -> 'a list m =
  function
  | [] -> return []
  | m :: ms ->
    let* x = m in
    let* xs = traverse ms in
    return (x :: xs)

let rec traverse : 'a t list -> 'a list t =
  function
  | [] -> pure []
  | t :: ts ->
    let+ x = t
    and+ xs = traverse ts
    in x :: xs


### Minor digression on the applicative syntax

pure : 'a -> 'a t
ap : ('a -> 'b) t -> 'a t -> 'b t
( <$> ) = ap

f : 'a -> 'b -> 'c
ta : 'a t
tb : 'b t

pure f <$> ta <$> tb
let+ a = ta and+ b = tb in f a b
let+ ta and+ tb in f ta tb


### Back to applicative functors

All monads are also applicative functors.

  let+ + let* -> and+

Applicative functors are a more restricted (weaker) notion of effects:
- there are more applicative functors than monads
- applicative functors offer a more limited programming
  interface (for users)
- applicative functors offer more freedom to implementors

With
  bind : 'a m -> ('a -> 'b m) -> 'b m
the effects in the ('b m) parts depend on the value 'a 
With
  pair : 'a t -> 'b t -> ('a * 'b) t
  ap : ('a -> 'b) t -> 'a t -> 'b t
the effects on both arguments are independent.

Intuitive example: parsing combinator libraries
- a parsing library using applicative functors
    may be more efficient in general
- but it cannot implement "dynamic" grammar rules
  (reading the precedence of an operator from the
   parsed input)

Another example: random generators.

  'a m: a generator of values of type 'a

Here `bind` lets you generate a value, and then from the result decide how to generate the rest.

  let gen_typed_value : (ty * term) m =
    let* ty = gen_type in
    let* term = gen_term_at_type ty in
    return (ty, term)


## An example of applicative functor that is not a monad

Inferno: a type inference library by François Pottier

Constraint-based type inference:
- generate a constraint from the input program
- the solution of the constraint tells you how
  to annotate it with types

  type 'a co = constraint * (solution -> 'a)
  val unify : ty co -> ty co -> unit co
  val exist : (tyvar -> 'a co) -> (ty * 'a) co

      constraint * _        solution -> _
Co = Writer{constraint} ∘ Reader{solution}

This is the composition of two monads,
but it is not a monad!

  bind : 'a co -> ('a -> 'b co) -> 'b co


## Bad compsition of monads

M, N : monads (C -> C)

join{M∘N} : (M∘N) ∘ (M∘N) → M∘N
            M∘N∘M∘N → M∘N

can be expressed if we have an operation

  dist : N∘M → M∘N

M∘N∘M∘N → M∘M∘N∘N → M∘N

      constraint * _        solution -> _
Co = Writer{constraint} ∘ Reader{solution}


dist : Reader{solution}∘Writer{constraint}
     → Writer{constraint}∘Reader{solution}

dist : (solution -> (constraint * 'a))
     → (constraint * (solution -> 'a))


m : * -> *
a : *
b : a -> *
bind : (t : m a) -> ((x:a) -> m (b x)) -> m (bind' t b)

Dijkstra Monads for Free
2017/2018

1 + perform Read

