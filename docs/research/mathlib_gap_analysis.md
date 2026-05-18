# Mathlib Gap Analysis

## Terminal Assessment

The full four-part theorem is not completed. The strongest checked frontier in this repository is a source-patch-needed handoff:

- a local `QuillenExactCategory` interface compiles;
- `MetrizableLCA` compiles as a bundled category with continuous additive homomorphisms;
- strict short exact sequences compile as closed inclusions, open surjections, and algebraic exactness after forgetting topology;
- the intended exact-category instance is exposed only from explicit `StrictExactQuillenAxioms`;
- Ext and derived-category declarations are checked only at the abelian-category or construction-interface frontier.

## Missing Exact-Category API

Local source search found no mathlib module named `ExactCategory` and no existing Quillen exact-category class. The local interface in `LeanLCAExactChallenge/ExactCategory/Basic.lean` therefore records the needed shape:

- conflations as short complexes;
- inflations and deflations as the first and second maps of conflations;
- stability of inflations under pushout;
- stability of deflations under pullback.

Minimal checked reproduction:

- `audit/blockers/quasi_abelian_exact_category_api.lean`

## Missing Strict LCA Stability Theorem

The project defines `MetrizableLCA.strictShortExact`, but the theorem that these strict sequences satisfy the Quillen exact-category axioms is not available from current mathlib. The handoff boundary is:

```lean
LeanLCAExactChallenge.MetrizableLCA.StrictExactQuillenAxioms
LeanLCAExactChallenge.MetrizableLCA.quillenExactCategory
```

The latter requires the former as an explicit argument, so it does not package an unproved product theorem as a completed instance.

Local evidence:

- `LeanLCAExactChallenge/LCA/Basic.lean`
- `LeanLCAExactChallenge/LCA/StrictExact.lean`
- `LeanLCAExactChallenge/LCA/ExactCategory.lean`

## Missing Yoneda Ext for Exact Categories

Mathlib provides `CategoryTheory.Abelian.Ext` for abelian categories through the derived category API. This repository exposes that checked frontier as `LeanLCAExactChallenge.YonedaExt`.

What remains missing is a Yoneda Ext construction for a general Quillen exact category, specialized to strict metrizable LCA conflations.

Minimal checked reproduction:

- `audit/blockers/yoneda_ext_exact_category_api.lean`

## Missing Bounded Derived Infinity-Category

Mathlib provides `DerivedCategory C` for abelian categories. The requested bounded derived infinity-category `D^b(C,E)` for an exact category is not available as a direct construction in the checked local API.

This repository exposes:

- `LeanLCAExactChallenge.BoundedDerivedInfinityCategory`, a construction interface requiring an exact category;
- `LeanLCAExactChallenge.Dbounded`, the underlying type of a chosen construction;
- `LeanLCAExactChallenge.abelianDerivedCategory`, the checked abelian-category comparison target.

Minimal checked reproduction:

- `audit/blockers/derived_infinity_exact_category_api.lean`

## Product-Completion Boundary

`terminal_outcome/terminal_outcome.json` must keep `product_complete=false`. A later product-success goal would need to replace the explicit LCA source-patch assumptions with proved Lean declarations and then build exact-category Yoneda Ext and bounded derived infinity-category APIs over that exact category.
