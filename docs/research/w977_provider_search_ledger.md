# W977 provider search ledger

Baseline: W976 is the current clean unit mapping-cone data route. It verifies a nonterminal route with 7 explicit provider inputs: W730 boundary/relation data, W944 target no-univ data, W973 closed-embedding closedness data, W974 endpoint kernel/cokernel-top data, W975 localized-adjunction data, W948 normalized-source-triangulation data, and W976 unit mapping-cone kernel/cokernel-top iso data.

Decision: W977 adds `BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977` to package exactly those seven W976 provider leaves into one current full-data provider. The route projects W977 data back to W976, rebuilds W976 leaves, and delegates through the existing W976/W975/W974/W973/W972 stack.

Rejected alternatives:

| Candidate | Effect | Reason deferred |
| --- | --- | --- |
| W947 target-no-univ/closedness provider | Bundle target no-univ data with W725 closedness data | W947 is the older closed-map branch surface; W976 uses W973 closed-embedding closedness data and should not widen back to the W725 closed-map-or-closed-embedding branch. |
| W952 current full-provider | Reuse an older one-provider surface | W952 packages the older closed-map localized-unit route, not the W976 closed-embedding endpoint/localized-adjunction/unit-mapping-cone surface. |
| Direct final product witness | Close the original four-task contract | No no-argument constructions of the seven provider inputs exist yet, so a product-success witness would be unsupported. |

Result: selected for W977. Explicit input names drop from 7 to 1. Product success remains false because the W977 full-data provider is still an explicit assumption and no original four-task completion witness exists.
