# W946 Provider Search Ledger

Generated: 2026-05-27 03:26 JST

Baseline: W945 commit `6e15fd5`, with product success still false and 8 explicit route inputs remaining.

| Candidate | Reduction | Fit | Decision |
| --- | --- | --- | --- |
| Existing W730 boundary/relation provider | Replace W945's separate W716 boundary data and W717 relation data leaves with `MetrizableWppBoundaryRelationDataProviderW730` | Exact type fit: W730 already projects to `MetrizableWppLimitBoundaryDataW716` and `ClosedNatTransOrdinaryRelationDataProviderW717` through checked helpers, with no older endpoint or target assumptions reintroduced | Selected for W946. |
| Older W732 boundary/relation/target/closedness/normalized provider | Collapse several W945 fields through the historical W732 route provider | Rejected as an immediate step because W732/W733 are shaped around older W715 target compactness, W724 source homological triangulation, W720 endpoint strict-topology, and W721 localized-right-adjoint data rather than W944 no-univ target data, W722 source data, endpoint strict exact, and W945 localized-unit data | Deferred until adapters are justified by Lean evidence. |
| New target/closedness-no-univ provider | Bundle W944 target no-univ data with W725 closedness data | Plausible but less direct than W730 because no existing exact provider boundary already matches both current W945 leaves | Deferred. |
| New normalized/source/endpoint/localized-unit provider | Bundle W719, W722, endpoint strict-exact, and W945 localized-unit data | Would reduce more inputs but would be a broad wrapper without a matching existing provider surface | Deferred. |

Selected W946 outcome: `ClosedMapBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataPrimitiveFieldRoute.lean` delegates through W945 after unpacking W730. Remaining explicit inputs are reduced from 8 to 7. Product success remains false because all W946 leaves are still assumptions, and no original four-task completion witness or product-success review packet exists.
