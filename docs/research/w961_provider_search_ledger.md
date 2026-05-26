# W961 Provider Search Ledger

Generated: 2026-05-27 06:17 JST

Baseline: W960 commit `bd05535`, with product success still false and the W725 closed-map constructor route separately verified.

| Candidate | Reduction | Fit | Decision |
| --- | --- | --- | --- |
| Split W725 closed-embedding branch data | Replace the bundled W725 provider with `SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718` and `MappedExplicitCokernelClosedEmbeddingProviderW519` | Exact fit for the W725 `closedEmbedding` constructor and mirrors the W960 closed-map branch without conflating the two branch surfaces | Selected for W961. |
| Continue only from W960 closed-map branch | Treat W960's closed-map branch as the sole closedness route | Too narrow for the original contract: W725 is branch-shaped and the closed-embedding constructor remains a real route surface. | Rejected. |
| Split endpoint strict-exact witnesses | Expose internal closed-embedding, open-map, and outgoing-epi strict-exact proofs | Useful, but the parallel W725 closed-embedding branch is the smallest remaining closedness-provider increment after W960. | Deferred. |
| Split W939 unit component witnesses | Replace the bundled unit-component witness with lower-level component fields | Larger surface and better handled after closing the W725 branch split. | Deferred. |

Selected W961 outcome: `ClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedEmbeddingClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldsRoute.lean` constructs the W725 `closedEmbedding` branch from raw selected-difference closed-embedding diagram components and the mapped explicit cokernel closed-embedding provider, then delegates through W959/W958/W957/W956/W955/W954/W953/W952. Product success remains false because the resulting W961 field surface still contains explicit assumptions for raw W716 boundary fields, raw W717 relation fields, raw W719 normalized fixed-target fields, raw W722 source-triangulation fields, target primitives, endpoint strict-exact witnesses, bounded-homotopy localized adjunction data, and W939 unit component witnesses; the W725 closed-map constructor remains separately represented by W960.
