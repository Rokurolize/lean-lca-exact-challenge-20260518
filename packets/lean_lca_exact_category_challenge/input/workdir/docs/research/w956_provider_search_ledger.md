# W956 Provider Search Ledger

Generated: 2026-05-27 05:22 JST

Baseline: W955 commit `660da5e`, with product success still false and split target primitives feeding the W954 provider constructor.

| Candidate | Reduction | Fit | Decision |
| --- | --- | --- | --- |
| Split W716 boundary data | Replace the W716 bundled boundary provider with the raw right-open closed-quotient-cover boundary and raw source-difference cokernel-pi-zero boundary fields | Exact fit: `MetrizableWppLimitBoundaryDataW716` is a two-field structure over those propositions, so W956 can construct W716 data and then reuse W955 | Selected for W956. |
| Split W717 relation data | Replace W717 with relation-pullback and target-relation-lift fields | Also an exact future direction, but W956 isolates one provider split and leaves relation data unchanged for easier audit. |
| Open W725 closedness data first | Split selected-difference and mapped-cokernel closedness data | Valid future direction, but it exposes more fields at once than the W716 split. |

Selected W956 outcome: `ClosedMapRawBoundarySplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsRoute.lean` constructs W716 boundary data from raw boundary fields and delegates through W955/W954/W953/W952. Product success remains false because the resulting W956 field surface still contains explicit assumptions for relation data, target primitives, closedness data, normalized fixed-target data, source data, endpoint strict-exact witnesses, and raw unit-component fields.
