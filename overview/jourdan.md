### Rust

In this part, we propose to give both a practical and a theoretical
view of the Rust programming language. This new language, developed
during the last decade, aims at modernizing systems programming by
providing a new balance between performance and control on the one
hand, and safety and ease of use on the other hand.

We will first give an overview of the language, from a user's
perspective. Rust got inspiration from many other programming
languages and adapted many well-known mechanisms to its contexts. We
will hence discuss features such as algebraic data types,
polymorphism, type traits (i.e., Rusts' type classes), closures and
subtyping. But Rust also introduced concepts which were only used in
experimental languages, such as ownership and aliasing
control. Finally, we will show how the type system of Rust allows
escaping from the safe fragment and encapsulating these uses of unsafe
features behind safe interfaces. We will study the important example
of interior mutability.

Next, we will focus on two recent research subjects on Rust. First, it
is possible to translate programs written in the safe fragment of Rust
into a functional language, thus completely erasing state. This makes
it possible to ease verification of Rust programs. Second, we will
give an overview of one proof of soundness of the type system of Rust,
which also proves that many libraries written in the unsafe fragment
are, in fact, safe.
