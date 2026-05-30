# W971 provider search ledger

Baseline: W970 is the current clean normalized-source-triangulation route. It verifies a nonterminal route with 21 explicit inputs, including raw W716 boundary propositions and raw W717 relation providers.

Decision: W971 uses `MetrizableWppBoundaryRelationDataProviderW730` to replace the W970 `rightOpenBoundary`, `sourcePiZeroBoundary`, `relationPullbackProvider`, and `targetRelationLiftsProvider` fields with one boundary/relation data provider. The route projects W730 back to W716 and W717, then delegates through W970.

Rejected alternatives:

| Candidate | Effect | Reason deferred |
| --- | --- | --- |
| Split target provider | Bundle the two target primitives | Useful next step, but W730 directly targets the oldest raw boundary/relation field group in W970. |
| Closedness branch data | Bundle W718 and W519 closed-embedding fields | Needs a closed-embedding-specific branch provider check, so it is better handled separately. |
| Localized unit data | Bundle right adjoint, adjunction, and unit strictness | W971 does not yet target the unit mapping-cone model/component/isomorphism surface. |

Result: selected for W971. Explicit input names drop from 21 to 18. Product success remains false because the W971 field surface still consists of explicit assumptions and does not construct the original four-task completion witness.
