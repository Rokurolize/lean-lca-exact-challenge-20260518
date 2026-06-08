# Reference Route Log

This log preserves durable route decisions. It is not a worker history and should not grow into a W-number ledger.

## Searches And Reused APIs

Source searches with `rg` over `.lake/packages/mathlib/Mathlib` did not find a ready-made Quillen exact-category class matching the local metrizable LCA goal. That false lead is why the repository keeps a local exact-category interface in `LeanLCAExactChallenge/ExactCategory/Basic.lean`.

The useful existing API was elsewhere:

- `ShortComplex`, exactness, and short exact sequence APIs were reused for strict exactness.
- Topological product, quotient, closed embedding, and open map APIs were reused for the metrizable LCA pullback, pushout, quotient, and cokernel constructions.
- `CategoryTheory.Localization` and calculus-of-fractions APIs were reused for the bounded localization surface.
- Homotopy category, mapping cone, shift, and triangulated APIs were reused as ordinary-category comparison tools.
- Simplicial nerve and quasicategory APIs were reused to expose an ordinary quasicategory carrier, while keeping the stable infinity-category gap explicit.
- `CategoryTheory.Abelian.Ext` was useful as a comparison point, but it is not a direct exact-category Yoneda Ext solution for the local interface.

## Mathematical References

Quillen and Buhler justify the exact-category formulation. Hoffmann-Spitzweck and Schneiders motivate the quasi-abelian LCA direction and the focus on strict morphisms. These references support the mathematical target but do not provide a Lean theorem that can be imported directly.

## Local Versus Adapted Work

The local `QuillenExactCategory` interface and the metrizable LCA strict exact-category instance are custom Lean work. The local Yoneda Ext construction is also custom because the available abelian Ext API does not solve the exact-category version directly.

The bounded derived surface is adapted from existing mathlib localization, homotopy, mapping-cone, shift, and nerve APIs. The adaptation is intentionally guarded: ordinary localization and ordinary nerve evidence are useful route data but not product-success evidence.

## Current Shortcut And Remaining Risk

The best shortcut remains to expose concrete structural fields in Lean and consume them through small projection lemmas and constructors. This is better than growing more provider wrappers or W-number ledgers because the remaining obligations are visible in types.

The remaining risk is overclaiming. A route that merely packages assumptions can be useful for reducing a future proof, but it is not a completed original four-task witness. The audits reject that overclaim by checking for positive Lean declarations and by rejecting known false-positive patterns.
