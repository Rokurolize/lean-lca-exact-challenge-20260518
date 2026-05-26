# W955 Provider Search Ledger

Generated: 2026-05-27 05:11 JST

Baseline: W954 commit `c0afff8`, with product success still false and W944 unit-component leaves feeding the W953 provider constructor.

| Candidate | Reduction | Fit | Decision |
| --- | --- | --- | --- |
| Split W944 target no-univ data | Replace the W944 bundled `TargetSurjectiveNoUnivMembershipForTargetProviderW944` with the two target primitives already exposed by W943: `targetDifferenceSurjectivePrimitiveW923` and `targetCodomainCompactNoUnivMembershipPrimitiveW930` | Exact fit: W944 target no-univ data is definitionally a pointwise conjunction of those two fields, so W955 can construct W944 leaves and then reuse W954 | Selected for W955. |
| Rebundle W954 through a larger provider | Combine boundary, relation, target, closedness, source, endpoint, and unit fields into a new provider | Rejected for this increment: it would hide more obligations behind one input and move away from the immutable contract's ban on final provider wrappers. |
| Attack W716/W717 boundary-relation data first | Open the boundary/relation provider pair before target data | Valid future direction, but W955 targets the weakest W954 leaf whose exact split is already present in nearby verified W943 declarations. |

Selected W955 outcome: `ClosedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsRoute.lean` constructs W944 target no-univ data from split target primitives and delegates through W954/W953/W952. Product success remains false because the resulting W955 field surface still contains explicit assumptions for boundary data, relation data, closedness data, normalized fixed-target data, source data, endpoint strict-exact witnesses, and raw unit-component fields.
