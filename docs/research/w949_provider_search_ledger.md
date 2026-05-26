# W949 Provider Search Ledger

Generated: 2026-05-27 04:01 JST

Baseline: W948 commit `b3d5be4`, with product success still false and 5 explicit route inputs remaining.

| Candidate | Reduction | Fit | Decision |
| --- | --- | --- | --- |
| W949 endpoint-localized-unit provider | Replace W948's separate endpoint strict short-exact witness and W945 localized-unit data leaves with `EndpointStrictExactLocalizedUnitDataProviderW949` | Exact current-type fit: projects directly to the W948 endpoint strict-exact field and W945 localized-unit provider, preserving the current W945 surface | Selected for W949. |
| Reuse older W900/W726 endpoint-localized routes | Collapse endpoint and localized data through older endpoint-topology/localized-right-adjoint shapes | Rejected for the immediate step because those routes use W720/W721-style endpoint/localized data rather than W948's current endpoint strictShortExact witness and W945 localized-unit provider | Deferred until adapters are justified by Lean evidence. |
| Bundle W730 boundary/relation with W947 target-no-univ/closedness | Reduce two remaining non-endpoint providers into one larger provider | Plausible but less local than the endpoint/localized frontier and would obscure two separate construction frontiers | Deferred. |
| Bundle all remaining non-endpoint data | Reduce W730, W947, and W948 into one large provider | Too coarse for the next contract-closing increment because it hides three current provider boundaries without constructing them | Rejected for W949. |

Selected W949 outcome: `ClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataPrimitiveFieldRoute.lean` delegates through W948 after unpacking W949 endpoint-localized-unit data. Remaining explicit inputs are reduced from 5 to 4. Product success remains false because all W949 leaves are still assumptions, and no original four-task completion witness or product-success review packet exists.
