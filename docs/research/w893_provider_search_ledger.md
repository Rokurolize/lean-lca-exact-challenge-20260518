# W893 Provider Search Ledger

- Baseline: W892 splits the `Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData` map-data family into six explicit fields while leaving the W716 WPP boundary-data bundle intact.
- Chosen split: `Dbounded.MetrizableWppLimitBoundaryDataW716`, because `WppOpExactAcyclicProjectionFields.lean` exposes its constructor fields directly as `rightOpenBoundary` and `sourcePiZeroBoundary`.
- Result: W893 replaces the bundled WPP boundary-data input with two explicit fields while preserving the W892 route and remaining nonterminal under the immutable original four-task contract.
- Remaining explicit inputs after W893: 35.
- Deferred candidates: W717 relation data, W715 target compact-surjective data, W725 closedness branch, fixed-target uniqueness, source-image normalization, triangulated/source-side data, endpoint ExactAt facts, and bounded homotopy localized right-adjoint data.
