# Sources

This note lists durable sources used by the repository. It is intentionally not a route history or worker ledger.

## Mathlib And Local Lean APIs

- `Mathlib/CategoryTheory/Localization/CalculusOfFractions.lean` and related localization files: calculus-of-fractions direction, localized categories, and comparison functors.
- `Mathlib/CategoryTheory/Localization/Predicate.lean`: universal-property and localization predicate APIs.
- `Mathlib/Algebra/Homology/ShortComplex/*.lean`: short complexes, exactness, and strict exact sequence support.
- `Mathlib/Algebra/Homology/DerivedCategory/*.lean`: abelian derived-category and Ext references, used as a comparison point rather than as a direct exact-category solution.
- `Mathlib/Algebra/Homology/HomotopyCategory/*.lean`: homotopy category, mapping cone, triangulated, and shift APIs.
- `Mathlib/AlgebraicTopology/SimplicialSet/Nerve*.lean` and `Mathlib/AlgebraicTopology/Quasicategory/*.lean`: ordinary nerve and quasicategory APIs. These are useful but are not by themselves stable infinity-category evidence.
- `Mathlib/Topology/Category/TopCat/Basic.lean`, `Mathlib/Topology/Constructions/SumProd.lean`, and quotient/closed-map topology files: local metrizable LCA constructions.

## Mathematical References

- Daniel Quillen, "Higher Algebraic K-Theory I": source terminology for exact categories.
- Theo Buhler, "Exact Categories", arXiv:0811.1480: exact-category framework and derived-category direction.
- Norbert Hoffmann and Markus Spitzweck, "Homological algebra with locally compact abelian groups", arXiv:math/0510345: quasi-abelian LCA background.
- Jean-Pierre Schneiders, "Quasi-Abelian Categories and Sheaves": quasi-abelian category background behind the LCA direction.

## Local Formalization Surface

- `LeanLCAExactChallenge/ExactCategory/Basic.lean`: local Quillen exact-category interface.
- `LeanLCAExactChallenge/LCA/*.lean`: metrizable LCA category, strict exactness, pullbacks, quotients, pushouts, cokernels, and the exact-category instance.
- `LeanLCAExactChallenge/Ext/Yoneda.lean`: local Yoneda Ext construction over the exact-category interface.
- `LeanLCAExactChallenge/Derived/Bounded.lean` and the `ExactAcyclicWithCycles` modules: bounded complex localization and the corrected ordinary derived-category foundation.
- `LeanLCAExactChallenge/Infinity/`: the mapping-quasicategory localization, coherent DG carrier, comparison, and stability construction surface.
