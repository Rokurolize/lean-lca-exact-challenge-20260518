# W958 Provider Search Ledger

Generated: 2026-05-27 05:41 JST

Baseline: W957 commit `57be66d`, with product success still false and raw W717 relation fields feeding the W956 provider constructor.

| Candidate | Reduction | Fit | Decision |
| --- | --- | --- | --- |
| Split W719 normalized fixed-target data | Replace the W719 bundled normalized fixed-target provider with normalized lift blueprint, target fixed-target uniqueness, and localization-model fixed-target uniqueness fields | Exact fit: `MetrizableWppNormalizedFixedTargetDataProviderW719` is a three-field structure over those obligations, so W958 can construct W719 data and reuse W957 | Selected for W958. |
| Split W722 source triangulation data | Replace W722 with source pretriangulated, source triangulated, and triangle-completion fields | Also exact, but W719 appeared first in the W957 field surface and has the same low-risk constructor profile. | Deferred. |
| Split W725 closedness data | Expose selected-difference and mapped-cokernel closedness branch internals | Larger branch-surface change and better handled after simple provider splits. | Deferred. |

Selected W958 outcome: `ClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsRoute.lean` constructs W719 normalized fixed-target data from raw normalized-lift blueprint, target fixed-target uniqueness, and localization-model fixed-target uniqueness fields, then delegates through W957/W956/W955/W954/W953/W952. Product success remains false because the resulting W958 field surface still contains explicit assumptions for raw W716 boundary fields, raw W717 relation fields, target primitives, closedness data, source data, endpoint strict-exact witnesses, and raw unit-component fields.
