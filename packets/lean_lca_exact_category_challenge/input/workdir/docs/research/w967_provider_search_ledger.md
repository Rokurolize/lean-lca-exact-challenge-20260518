# W967 Provider Search Ledger

Timestamp: 2026-05-27 07:30 JST.

Baseline: W966 commit `c46302a3d3c79a7901318bc460bfd24a39dd5813`, with product success still false and 26 explicit route inputs remaining on the W966 endpoint-kernel/cokernel-top and unit-cokernel-top component surface.

| Candidate | Action | Evidence | Decision |
| --- | --- | --- | --- |
| Unit mapping-cone kernel-equality split | Replace W966's unit mapping-cone algebraic-exactness field with unit mapping-cone kernel equality, deriving algebraic exactness from the forward direction | This is the direct analogue of W965 on the unit mapping-cone branch and pairs with W966's unit cokernel-top split | Selected for W967. |
| Direct unit strict-exact reconstruction | Check that unit closed embedding, open map, cokernel top, and kernel equality reconstruct unit strict short exactness | `MetrizableLCA.strictShortExact_of_kernel_open_closed_cokernelSubgroup_eq_top` applies to the unit mapping-cone component short complex after the kernel field is exposed | Included as a W967 proof check. |
| Localized right adjoint and adjunction | Construct or split bounded-homotopy localized right-adjoint/adjunction fields | Larger categorical existence surface than the local unit strict-exact component bridge | Deferred. |
| Raw W716/W717/W719/W722 fields or target primitives | Attack boundary, relation, normalized fixed-target, source-triangulation, or target primitive leaves directly | These remain broader topological/categorical obligations; no smaller no-argument provider was found in this inspection pass | Deferred. |
| Unit mapping-cone model/isomorphism construction | Construct the unit mapping-cone model or adjunction-unit mapping-cone isomorphism directly | This depends on the localized adjunction surface and is larger than the current component-field split | Deferred. |

Selected W967 outcome: `ClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedEmbeddingClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointKernelCokernelTopAndUnitKernelCokernelTopComponentFieldsRoute.lean` replaces W966's unit mapping-cone degreewise algebraic-exactness assumption with unit mapping-cone kernel equality, derives algebraic exactness from the forward implication, directly checks unit strict short exactness from kernel/cokernel data, and delegates through W966, W965, W964, W963, W962, W961, W959, W958, W957, W956, W955, W954, W953, and W952. Product success remains false because the W967 field surface still contains explicit assumptions for raw W716 boundary fields, raw W717 relation fields, raw W719 normalized fixed-target fields, raw W722 source-triangulation fields, W961 closed-embedding closedness fields, target primitives, endpoint closed-embedding/open-map/cokernel-top/kernel-equality fields, bounded-homotopy localized right-adjoint/adjunction data, and unit mapping-cone model/closed-embedding/open-map/cokernel-top/kernel-equality/isomorphism fields.
