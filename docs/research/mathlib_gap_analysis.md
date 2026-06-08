# Mathlib Gap Analysis

The original four-task theorem is still incomplete.

## Completed Local Surface

- The repository has a compiling local `QuillenExactCategory` interface.
- `MetrizableLCA` is implemented as a bundled category of metrizable locally compact abelian groups with continuous additive homomorphisms.
- Strict short exact sequences are represented with closed embeddings, open surjections, and algebraic exactness after forgetting topology.
- Split strict exactness, isomorphism transport, coordinatewise binary biproduct strict exactness, pullback stability, pushout stability, cokernels, finite colimits, and the strict exact-category instance are available locally.
- The local Yoneda Ext construction no longer merely wraps abelian Ext. It uses exact-category conflation chains, generated relations, Baer-sum witnesses, and product-facing APIs.
- Bounded cochain complexes, exact weak equivalences detected by exact-acyclic mapping cones, and the localized `Dbounded` surface are implemented. There are many conditional comparison and stable-route APIs.

## Remaining Gap

Mathlib does not currently provide a direct exact-category bounded derived stable infinity-category construction for this local exact-category interface. The repository has an ordinary localization nerve and many conditional routes, but product success requires more than an ordinary nerve or a named stable certificate.

The missing proof obligation is to build the stable bounded-derived infinity-category evidence from source-level Lean data. In practical terms, future work must supply the finite-limit, finite-colimit, zero-object, shift-additivity, pretriangulated, triangulated, and stable compatibility fields for `Dbounded MetrizableLCA` without relying on route metadata or wrapper assumptions.

## False Leads To Keep Rejected

- Treating `CategoryTheory.nerve (Dbounded ...)` as stable infinity-category evidence.
- Treating a long W-number route name or a provider ledger as proof.
- Treating a comment, string literal, terminal JSON flag, or packet manifest as a Lean witness.
- Claiming product success while the final surface still proves `productSuccessClaimed = false`.

The audit fixtures intentionally reject these failure modes.
