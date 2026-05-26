# W966 Provider Search Ledger

Timestamp: 2026-05-27 07:20 JST.

Baseline: W965 commit `f6cb87890955e5d2b89f81e7732602cff1177075`, with product success still false and 26 explicit route inputs remaining on the W965 endpoint-kernel/cokernel-top and unit mapping-cone component surface.

| Candidate | Action | Evidence | Decision |
| --- | --- | --- | --- |
| Unit mapping-cone cokernel-top split | Replace W965's unit mapping-cone surjectivity field with unit mapping-cone cokernel top, deriving surjectivity from the existing unit open-map field | `MetrizableLCA.surjective_of_cokernelSubgroup_eq_top_of_isOpenMap` is already used by W964 for the endpoint branch and applies to the unit mapping-cone component morphism | Selected for W966. |
| Unit mapping-cone kernel-equality split | Replace unit mapping-cone algebraic exactness with a unit mapping-cone kernel-equality field | Same local shape as W965, but W966 first removes the adjacent surjectivity leaf using the already checked cokernel/open-map bridge | Deferred. |
| Direct unit strict-exact reconstruction | Reconstruct unit mapping-cone strict short exactness directly from unit closed embedding, open map, cokernel top, and kernel equality | Requires the unit kernel-equality field, which is not yet exposed in W966 | Deferred. |
| Localized right adjoint and adjunction | Construct or split bounded-homotopy localized right-adjoint/adjunction fields | Larger categorical existence surface than the local component bridge | Deferred. |
| Raw W716/W717/W719/W722 fields or target primitives | Attack boundary, relation, normalized fixed-target, source-triangulation, or target primitive leaves directly | These remain broader topological/categorical obligations; no smaller no-argument provider was found in this inspection pass | Deferred. |

Selected W966 outcome: `ClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedEmbeddingClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointKernelCokernelTopAndUnitCokernelTopComponentFieldsRoute.lean` replaces W965's unit mapping-cone degreewise surjectivity assumption with unit mapping-cone cokernel-top data, derives surjectivity from the unit open-map field, and delegates through W965, W964, W963, W962, W961, W959, W958, W957, W956, W955, W954, W953, and W952. Product success remains false because the W966 field surface still contains explicit assumptions for raw W716 boundary fields, raw W717 relation fields, raw W719 normalized fixed-target fields, raw W722 source-triangulation fields, W961 closed-embedding closedness fields, target primitives, endpoint closed-embedding/open-map/cokernel-top/kernel-equality fields, bounded-homotopy localized right-adjoint/adjunction data, and unit mapping-cone model/closed-embedding/open-map/cokernel-top/algebraic-exactness/isomorphism fields.
