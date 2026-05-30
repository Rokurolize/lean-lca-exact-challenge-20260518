# W952 Provider Search Ledger

Generated: 2026-05-27 04:36 JST

Baseline: W951 commit `566c32e`, with product success still false and 2 explicit route inputs remaining.

| Candidate | Reduction | Fit | Decision |
| --- | --- | --- | --- |
| W952 boundary-relation/target-normalized-endpoint full provider | Replace W951's remaining W730 boundary/relation data and W951 target-no-univ-closedness/normalized-source-endpoint-localized-unit data leaves with `BoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW952` | Exact current-type fit: projects directly to W730 and W951 providers, preserving the current boundary/relation, no-univ target, closedness, normalized-source, endpoint, and localized-unit surfaces | Selected for W952. |
| Construct W730 boundary/relation data directly | Remove the boundary/relation assumption rather than package it | More product-closing, but not yet supported by a no-assumption construction of the W716/W717 data in the current route surface | Deferred until Lean evidence identifies the construction path. |
| Construct W951 target/closedness/normalized-source/endpoint data directly | Remove the larger target/normalized/endpoint assumption rather than package it | More product-closing, but this still spans W947 and W950 construction frontiers | Deferred until smaller internal construction paths are available. |
| Reuse older W732/W733 route data or concrete leaves as the main provider | Collapse through an older broad route surface | Rejected for this increment because those providers encode older W715/W724/W720/W721-style assumptions instead of the current W730/W951 provider boundary | Deferred until adapters are justified by Lean evidence. |

Selected W952 outcome: `ClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceTriangulationEndpointLocalizedUnitDataPrimitiveFieldRoute.lean` delegates through W951 after unpacking W952 current full-provider data. Remaining explicit inputs are reduced from 2 to 1. Product success remains false because the W952 full-provider is still an assumption, and no original four-task completion witness or product-success review packet exists.
