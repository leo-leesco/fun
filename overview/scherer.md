### Effects

In the theory of programming languages, "effects" describe
computational phenomenons that happen "on the side" during the
computation of a program. "While this function runs, it prints
messages / sends emails / displays images / accesses a database / asks
questions to the user, in addition to returning a result." Effects are
of course very important in programs, they are often the main
reason why humans execute programs in the first place!

There is an active research area studying effects: how to model them
mathematically, how to reason about programs containing effects, how
to implement them. Over time researchers realized that we can reuse
the theoretical analysis of effects to provide general mechanisms
letting programmers *implement* effects as libraries, instead of
having only a fixed set of effects supported by the programming
language definition. It is sometimes possible, through careful
refactoring, to take a complex program that computes various things
"directly", turn some of these things into "effects done on the side",
to obtain an equivalent program that looks simpler, is easier to write
and to understand -- with more complex effects on the side.

In this section of the course we will study:

- Algebraic structures that capture notions of effects in
  theory and in practice: monads and applicative functors.

- Effect handlers, a new programming construct that provides another,
  flexible approach to user-defined effects.
