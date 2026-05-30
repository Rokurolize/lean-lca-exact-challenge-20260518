# W986 provider search ledger

Baseline: W985 supplied W948 normalized-source-triangulation data and W949 endpoint-localized-unit data from the existing W950 provider. Product success remained false because three provider-level inputs were still explicit: W730 boundary/relation data, W984 target/closed-embedding closedness data, and W950 normalized-source/endpoint-localized-unit data.

Decision: W986 mirrors the earlier W951 target/closedness/normalized-source/endpoint pattern while preserving the current branch-specific closed-embedding surface. It introduces `TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986`, packaging W984 target/closed-embedding closedness data with W950 normalized-source/endpoint-localized-unit data, then projects both fields back into W985.

Rejected alternatives:

| Candidate | Effect | Reason deferred |
| --- | --- | --- |
| Reuse W951 directly | Bundle target/closedness with normalized-source/endpoint-localized-unit data through an existing provider | Rejected for the current route because W951 depends on W947/W725 closedness, while W986 must preserve W984's W973 branch-specific closed-embedding surface. |
| Construct W730 boundary/relation data directly | Remove the boundary/relation assumption | More product-closing, but W730 is still a package of W716 boundary data and W717 relation data, and no no-argument constructor was identified in the current route surface. |
| Bundle W730 with W984 target/closed-embedding closedness | Reduce the front two providers | Plausible, but less adjacent than the W984/W950 boundary and would leave normalized-source/endpoint data separate. |

Result: selected for W986. The route verifies that W984 target/closed-embedding closedness data and W950 normalized-source/endpoint-localized-unit data can be supplied by one branch-specific provider while preserving the current W985 route. The current full-data surface drops from three provider-level inputs to two. Product success remains false because W986 still assumes W730 boundary/relation data and W986 target/closed-embedding-closedness/normalized-source/endpoint-localized data, and no original four-task completion witness exists.
