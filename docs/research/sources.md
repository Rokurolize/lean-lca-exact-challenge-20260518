# Sources Used

## Lean/mathlib

- Local mathlib `Mathlib/Topology/Category/TopCat/Basic.lean`: checked `TopCat`, `TopCat.Hom`, continuous maps, and the topological-space category.
- Local mathlib `Mathlib/Algebra/Category/Grp/Basic.lean` and `Preadditive.lean`: checked `AddCommGrpCat`, bundled additive commutative groups, and zero morphisms.
- Local mathlib `Mathlib/Topology/Algebra/ContinuousMonoidHom.lean`: supports continuous additive homomorphisms used for `MetrizableLCA.Hom`.
- Local mathlib `Mathlib/Topology/Metrizable/Basic.lean`: supports `TopologicalSpace.MetrizableSpace`.
- Local mathlib `Mathlib/Algebra/Homology/ShortComplex/Basic.lean`, `Exact.lean`, and `ShortExact.lean`: supports `ShortComplex`, `ShortComplex.Exact`, and `ShortComplex.ShortExact`.
- Local mathlib `Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean`: supports the pushout and pullback names used in the Quillen exact-category interface.
- Local mathlib `Mathlib/Algebra/Homology/DerivedCategory/Basic.lean`: supports the checked abelian-category derived category frontier.
- Local mathlib `Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean`: supports `CategoryTheory.Abelian.Ext`, degree-zero hom equivalence, Baer addition through the additive group instance, and Ext composition.
- Local checked anchors: `LeanLCAExactChallenge/MathlibSurvey.lean`.

## Mathematics

- Daniel Quillen, "Higher Algebraic K-Theory I", source for the exact-category target notion.
- Theo Buehler, "Exact Categories", arXiv:0811.1480, https://arxiv.org/abs/0811.1480. Used for the Quillen exact-category framing and derived categories of exact categories.
- Norbert Hoffmann and Markus Spitzweck, "Homological algebra with locally compact abelian groups", arXiv:math/0510345, https://arxiv.org/abs/math/0510345. Used for the target claim that locally compact abelian groups are treated via quasi-abelian methods.
- Jean-Pierre Schneiders, "Quasi-Abelian Categories and Sheaves", SMF, https://smf.emath.fr/publications/categories-et-faisceaux-quasi-abeliens. Used for the quasi-abelian background named by Hoffmann-Spitzweck.

## Local Formal Artifacts

- `LeanLCAExactChallenge/ExactCategory/Basic.lean`: checked local interface for a Quillen exact category.
- `LeanLCAExactChallenge/LCA/Basic.lean`: checked bundled category and morphism layer for metrizable LCA groups.
- `LeanLCAExactChallenge/LCA/StrictExact.lean`: checked strict-sequence predicate and algebraic kernel/cokernel accessors.
- `LeanLCAExactChallenge/LCA/ExactCategory.lean`: checked source-patch assumption boundary for the missing strict LCA exact-category theorem.
- `LeanLCAExactChallenge/Ext/Yoneda.lean`: checked abelian-category Ext frontier.
- `LeanLCAExactChallenge/Derived/Bounded.lean`: checked construction interface for the missing exact-category bounded derived infinity-category.
