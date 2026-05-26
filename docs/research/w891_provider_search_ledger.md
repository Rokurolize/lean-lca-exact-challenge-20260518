# W891 Provider Search Ledger

- Baseline: W890 splits `Dbounded.MetrizableWalkingParallelPairLiftBlueprint` into object data, map data, identity coherence, and composition coherence.
- Chosen split: `Dbounded.MetrizableWalkingParallelPairStrictPreimageData`, because `BoundedFiniteProducts.lean` exposes its constructor fields directly as `zeroSrc`, `oneSrc`, `zeroIso`, `oneIso`, `leftSrc`, `rightSrc`, `left_fac`, and `right_fac`.
- Result: W891 replaces the bundled strict preimage object-data family with eight explicit fields while preserving the W890 route and remaining nonterminal under the immutable original four-task contract.
- Remaining explicit inputs after W891: 29.
- Deferred candidates: strict preimage map-data internals, W725 closedness branch, W716 boundary data, W717 relation data, W715 target compact-surjective data, triangulated/source-side data, endpoint ExactAt facts, and bounded homotopy localized right-adjoint data.
