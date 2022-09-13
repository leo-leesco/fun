### Interpretation, Compilation, and Program Transformations

In the first lecture, we discuss several presentations of the *operational
semantics* of a (call-by-value) functional programming language. We explain
why each of these presentations exists and in what sense these presentations
are equivalent. One of these presentations is in fact executable: it is an
interpreter. This interpreter can be implemented in Coq and can be *verified*,
that is, can be proved correct with respect to the other presentations of the
operational semantics. As far as time permits, we will review how lambda-terms
and their operational semantics can be defined in Coq, using a representation
of names as de Bruijn indices. Although Coq is not a prerequisite of the
course, we will at least try to *read and understand Coq definitions and
statements*.

In the next three lectures, we present several classic *program
transformations*, including closure conversion, defunctionalization, the
transformation into continuation-passing style (CPS), and stream fusion. These
program transformations are interesting from two points of view. First, they
are *useful programming techniques*, which can help write or understand
programs. Second, they are used in the *compilation* of functional programming
languages, so they help understand what happens when the machine executes a
program. We discuss how to *prove* that the meaning of programs is preserved
by these transformations, based on an operational semantics. We suggest how
these definitions and theorems can be expressed in a form that a machine can
check (that is, in Coq).
