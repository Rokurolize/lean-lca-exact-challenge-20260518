# W964 Provider Search Ledger

Timestamp: 2026-05-27 07:00 JST.

Baseline: W963 commit `0818434a398da6ad9fb29671c45829d44a59bbe5`, with product success still false and 26 explicit route inputs remaining on the W963 endpoint-strict and unit mapping-cone component surface.

| Candidate | Action | Evidence | Decision |
| --- | --- | --- | --- |
| Endpoint cokernel-top split | Replace W963's endpoint degreewise surjectivity field with endpoint `MetrizableLCA.cokernelSubgroup (K.sc i).g = ⊤`, deriving surjectivity from the existing endpoint open-map field | `MetrizableLCA.surjective_of_cokernelSubgroup_eq_top_of_isOpenMap` directly bridges cokernel top plus open map to surjectivity, matching the algebraic cokernel side of strict exactness | Selected for W964. |
| Endpoint algebraic exactness split | Replace endpoint algebraic exactness with a kernel equality or AddCommGrp-forgetting exactness field | Plausible next, but W964's cokernel-top bridge is a smaller one-field replacement with an existing local lemma | Deferred. |
| Unit mapping-cone cokernel-top split | Apply the same cokernel-top bridge to the unit mapping-cone surjectivity component | Similar shape, but endpoint strict-exact was just opened by W963 and is the more immediate target leaf | Deferred. |
| Localized right adjoint and adjunction | Construct or split bounded-homotopy localized right-adjoint/adjunction fields | Still a larger categorical existence surface than a local strict-exact component bridge | Deferred. |
| Raw W716/W717/W719/W722 fields or target primitives | Attack boundary, relation, normalized fixed-target, source-triangulation, or target primitive leaves directly | These remain broader topological/categorical obligations; no smaller no-argument provider was found in the W963 inspection pass | Deferred. |

Selected W964 outcome: `ClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedEmbeddingClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointCokernelTopAndUnitWitnessComponentFieldsRoute.lean` replaces W963's endpoint surjectivity assumption with an endpoint cokernel-subgroup-top assumption and derives surjectivity from that field plus endpoint open maps. It then reconstructs W963 leaves and delegates through W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/W952. Product success remains false because the W964 field surface still contains explicit assumptions for raw W716 boundary fields, raw W717 relation fields, raw W719 normalized fixed-target fields, raw W722 source-triangulation fields, W961 closed-embedding closedness fields, target primitives, endpoint closed-embedding/open-map/cokernel-top/algebraic-exactness fields, bounded-homotopy localized right-adjoint/adjunction data, and unit mapping-cone model/component/isomorphism fields.
