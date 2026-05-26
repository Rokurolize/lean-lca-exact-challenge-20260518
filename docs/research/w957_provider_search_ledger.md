# W957 Provider Search Ledger

Generated: 2026-05-27 05:33 JST

Baseline: W956 commit `6455dc5`, with product success still false and raw W716 boundary fields feeding the W955 provider constructor.

| Candidate | Reduction | Fit | Decision |
| --- | --- | --- | --- |
| Split W717 relation data | Replace the W717 bundled relation-data provider with `ClosedNatTransOrdinaryRelationPullbackProviderW712` and `ClosedNatTransOrdinaryTargetRelationLiftsProviderW712` | Exact fit: `ClosedNatTransOrdinaryRelationDataProviderW717` is a two-field structure over those providers, so W957 can construct W717 data and reuse W956 | Selected for W957. |
| Split W725 closedness data | Expose the selected-difference and mapped-cokernel closedness branch internals | Larger branch-surface change and better handled after the simple W717 field split. | Deferred. |
| Split W719 normalized fixed-target data | Replace W719 with normalized-lift blueprint and two uniqueness obligations | Exact future direction, but W957 isolates one provider split. | Deferred. |

Selected W957 outcome: `ClosedMapRawBoundaryRelationFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsRoute.lean` constructs W717 relation data from raw relation-pullback and target-relation-lift fields and delegates through W956/W955/W954/W953/W952. Product success remains false because the resulting W957 field surface still contains explicit assumptions for raw W716 boundary fields, target primitives, closedness data, normalized fixed-target data, source data, endpoint strict-exact witnesses, and raw unit-component fields.
