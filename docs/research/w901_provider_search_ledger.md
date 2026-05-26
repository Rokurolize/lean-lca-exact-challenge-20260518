# W901 Provider Search Ledger

- Baseline: W900 bundles W899 endpoint ExactAt facts through `MetrizableWppEndpointTopologyFactsProviderW856` and bounded-homotopy localized-right-adjoint data through `MetrizableWppLocalizedRightAdjointDataProviderW721`, while still exposing the source `Pretriangulated`, source `IsTriangulated`, and source-side triangle-completion fields separately.
- Chosen reduction: `MetrizableWppSourceTriangulationDataProviderW722`, because W722 bundles exactly those three source-side fields and already has projection functions for each component.
- Safety check: W722 does not require W720 endpoint strict topology data, does not reintroduce endpoint forgetful homology preservation, and does not change the closed-map endpoint-homology-free route inherited from W899/W900.
- Result: W901 replaces three W900 explicit leaves with one W722 source-triangulation provider, preserving the W900 stable ExactAt route and remaining nonterminal under the immutable original four-task contract.
- Remaining explicit inputs after W901: 31 for the closed-map source-triangulation endpoint-facts localized-right-adjoint route.
- Deferred candidates: bundled W716 boundary data, W717 relation data, W715 target surjective-compact data, strict preimage object/map concrete fields, fixed-target uniqueness, source-image normalization, W519 mapped-cokernel closed-map data, and the final branch selection/no-argument original-four-task witness.
