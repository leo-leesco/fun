# Programming exercises about ML and type inference

First, have a look at `miniml.ml` and at the `mli` files to understand
the global structure of this program. Then complete the following two
tasks.

## Algorithm W

1. Complete `Elaboration.algorithm_w`.

2. Complete `Typechecker.check`.

3. Check that `make check` is succeeding.

## Constraint-based type inference

1. Read [François Pottier's paper about type inference](http://gallium.inria.fr/~fpottier/publis/fpottier-elaboration.pdf).

2. Complete `ConstraintElaboration.generate_constraint`.

3. Check that `OPT=--constraint make check` still succeeds.

