# W970 provider search ledger

Baseline: W969 is the current clean source-triangulation-data route. It verifies a nonterminal route with 24 explicit inputs, including separate W719 normalized fixed-target projections and one W722 source-triangulation data provider.

Decision: W970 uses `NormalizedFixedTargetSourceTriangulationDataProviderW948` to replace the W969 `normalizedLiftBlueprint`, `targetFixedTargetUniq`, `localizationModelFixedTargetUniq`, and `sourceTriangulationData` fields with one normalized-source-triangulation provider. The route projects W948 back to W719 and W722, then delegates through W969.

Rejected alternatives:

| Candidate | Effect | Reason deferred |
| --- | --- | --- |
| W730 boundary/relation data | Replace raw W716/W717 boundary and relation leaves | Useful next step, but W970 targets the already adjacent W719/W722 provider boundary first. |
| W945 localized-unit data | Bundle right adjoint, adjunction, and unit component strictness | W970's current unit surface is stronger and includes model/component/isomorphism fields not covered by W945 alone. |
| Endpoint strict-exact provider | Bundle endpoint closed/open/cokernel/kernel fields | Endpoint kernel/cokernel-top fields are not just the older endpoint strict topology provider surface, so this needs a separate compatibility step. |

Result: selected for W970. Explicit input names drop from 24 to 21. Product success remains false because the W970 field surface still consists of explicit assumptions and does not construct the original four-task completion witness.
