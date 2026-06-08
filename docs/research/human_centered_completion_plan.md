# Human-Centered Completion Plan

This plan keeps the final proof surface readable.

The repository should not keep growing final-facing names that encode an entire proof route in one identifier. New product-facing APIs should be small structures, projection lemmas, and constructors whose mathematical role is clear from their type.

## Current Noncompletion Point

The repository still lacks a positive Lean witness equivalent to `OriginalFourTaskProductSuccess`. The current final-facing contract keeps product success false. This is intentional and must remain true until the bounded derived infinity-category target is actually constructed.

## Preferred Shape For Future Work

- Keep stable-instance data as compact bundles with clear field names.
- Keep projection lemmas simple and canonical, preferably reducible by `rfl` or `simp`.
- Use route data only when it removes a real mathematical obligation or turns an overstrong statement into a standard one.
- Avoid treating W-number ledgers as proof evidence.
- Prefer homotopy-category and Verdier-style boundaries when raw bounded-complex requirements are mathematically too strong.

## Immediate Proof Directions

1. Close the remaining bounded homotopy/Verdier comparison inputs with source theorems rather than metadata.
2. Supply concrete finite-limit and finite-colimit transfer data for `Dbounded MetrizableLCA`, or prove a direct preservation theorem.
3. Replace raw strictification requirements that are contradicted by contractible-tail examples with controlled representative-selection hypotheses.
4. Package the stable-instance fields into a positive witness only after the fields are real source-level constructions.

Do not repeat the stale provider-wrapper direction that only repackages old route data. If those names still appear in local source, treat them as compatibility or frontier evidence only; new proof work should replace the carried provider assumptions with source-level constructions or a clearly stated missing theorem.
