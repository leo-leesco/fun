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

### Paper discussions

This course will include in-course discussion of research
articles/papers. We will read three papers during the semester. You
will be told about each one several weeks in advance; you have to read
it before the corresponding class, and we will discuss it together
during class. This should give you a glimpse of current topics in the
area, and more generally train you to read research papers and engage
with them.

In class, we will discuss the following questions:
- what are the authors presenting?
- what is the contribution of the paper?
- how did the authors evaluate their work?
- what did you think of the paper (content and presentation)?
