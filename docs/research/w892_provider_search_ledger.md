# W892 Provider Search Ledger

- Baseline: W891 splits the `Dbounded.MetrizableWalkingParallelPairStrictPreimageData` object-data family into eight explicit fields while leaving the strict preimage map-data family bundled.
- Chosen split: `Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData`, because `BoundedFiniteProducts.lean` exposes its constructor fields directly as `zeroMap`, `oneMap`, `zero_fac`, `one_fac`, `left_naturality`, and `right_naturality`.
- Result: W892 replaces the bundled strict preimage map-data family with six explicit fields while preserving the W891 route and remaining nonterminal under the immutable original four-task contract.
- Remaining explicit inputs after W892: 34.
- Deferred candidates: W725 closedness branch, W716 boundary data, W717 relation data, W715 target compact-surjective data, triangulated/source-side data, endpoint ExactAt facts, fixed-target uniqueness, and bounded homotopy localized right-adjoint data.
