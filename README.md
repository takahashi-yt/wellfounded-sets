# Wellfounded-Sets Repository

This is an Agda formalization of the category of well-founded sets and strictly monotone functions. Its background is the notion of type-theoretic ordinal developed in homotopy type theory (see, e.g. the HoTT book). Our formalization is based on the [agda/cubical library](https://github.com/agda/cubical), and the formalized proofs can be typechecked with Agda version 2.8.0 and the agda/cubical library version 0.9.

## Outline

`Base.agda`:
We define the wild category Ord of type-theoretic ordinals (in short, ordinals) and strictly monotone functions. We then formulate its slight generalization obtained by dropping the extensionality of an ordering relation: the wild category of well-founded sets and strictly monotone functions. It is shown that if two well-founded sets are isomorphic then they are propositionally equal.

`FiniteSet.agda`:
We define the family Fin of types of finite ordinals with the ordering relations satisfying linearity. Each type Fin n turns out to be an ordinal.

`Diagram.agda`:
For each ordinal, we define a diagram for which the ordinal is shown to be a colimit. The diagram is a functor whose domain is essentially the preorder of finite subsets of a given ordinal.

`Quotient.agda`:
By using set-quotients as higher inductive types, we equip a given ordinal with a quotient of the dependent sum of its finite subsets. This quotient is shown to be propositionally equal to the given ordinal.

`Colimit.agda`:
We verify that each ordinal is a colimit for the corresponding diagram which was defined in `Diagram.agda`.

`Functor.agda`:
We show that the outputs of a colimit preserving functor on WF for ordinals are determined by its behaviour on finite subsets of ordinals and the morphisms between them.