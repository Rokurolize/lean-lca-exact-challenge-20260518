# W961 Closed-Embedding Closedness Product Surface Checkpoint

Generated UTC: 2026-06-09T13:55:53Z

## Source Patch

- `LeanLCAExactChallenge/BoundedDerived/MetrizableStableBridge.lean` now imports the checked W961 route and exposes `BoundedDerived.Metrizable.ClosedEmbeddingClosednessFieldsInputW961` plus `stablePackageOfClosedEmbeddingClosednessFieldsW961`.
- `LeanLCAExactChallenge/OriginalFourTask/ProductData.lean` now exposes `originalFourTaskProductDataOfClosedEmbeddingClosednessFieldsW961` and rfl guards for its bounded-derived package, exact-category field, and YonedaExt surface.

## Mathematical Meaning

W961 was already a checked source route from the closed-embedding closedness field surface to a bounded-derived stable package: it splits the W725 closed-embedding branch into raw W718 selected-difference closed-embedding components and the W519 mapped explicit cokernel closed-embedding provider before feeding the stable ExactAt route. This checkpoint makes that existing source route visible at the bounded-derived bridge and original-four-task product-data surface.

This is a source-surface improvement, not a product-success witness. The new entrypoint is still parameterized by `ClosedEmbeddingClosednessFieldsInputW961`; it does not construct a nullary W732 route-data provider, a nullary direct-localization boundary input, or `OriginalFourTaskProductSuccess`.

## Verification

- `lake env lean LeanLCAExactChallenge/BoundedDerived/MetrizableStableBridge.lean`: passed.
- Initial `lake env lean LeanLCAExactChallenge/OriginalFourTask/ProductData.lean`: failed because the imported `MetrizableStableBridge` `.olean` did not yet contain the new W961 declarations.
- `lake build LeanLCAExactChallenge.BoundedDerived.MetrizableStableBridge`: passed with existing warnings only and refreshed the imported bridge artifact.
- `lake env lean LeanLCAExactChallenge/OriginalFourTask/ProductData.lean`: passed after rebuilding the bridge; one pre-existing reducibility warning remains at line 149.
- `lake env lean LeanLCAExactChallenge.lean`: passed.
- `git diff --check -- LeanLCAExactChallenge/BoundedDerived/MetrizableStableBridge.lean LeanLCAExactChallenge/OriginalFourTask/ProductData.lean`: passed.
- `scripts/audit_no_forbidden_lean_tokens.sh LeanLCAExactChallenge/BoundedDerived/MetrizableStableBridge.lean LeanLCAExactChallenge/OriginalFourTask/ProductData.lean`: passed.

## Remaining Gap

The product remains nonterminal. The next source API still needs to construct one of the known nullary frontiers, especially a concrete W732 route-data provider, a nullary `Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs`, or an equivalent nullary `BoundedDerived.Metrizable.StablePackage`.
