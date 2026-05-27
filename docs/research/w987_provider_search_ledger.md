# W987 provider search ledger

Baseline: W986 supplied W984 target/closed-embedding closedness data and W950 normalized-source/endpoint-localized-unit data from one branch-specific W986 provider. Product success remained false because two provider-level inputs were still explicit: W730 boundary/relation data and W986 target/closed-embedding-closedness/normalized-source/endpoint-localized data.

Decision: W987 mirrors the earlier W952 one-provider consolidation pattern while preserving the current W973 closed-embedding branch. It introduces `BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987`, packaging W730 boundary/relation data with W986 target/closed-embedding-closedness/normalized-source/endpoint-localized data, then projects both fields back into W986.

Rejected alternatives:

| Candidate | Effect | Reason deferred |
| --- | --- | --- |
| Construct W730 boundary/relation data directly | Remove the boundary/relation assumption rather than package it | W730 still packages W716 boundary data and W717 relation data; no no-argument constructor was identified in the live route surface. |
| Construct the W986 target/normalized/endpoint provider directly | Remove the target/normalized/endpoint assumption | W986 contains W984 target/closed-embedding closedness data and W950 normalized-source/endpoint-localized data; no current no-argument constructor was identified for that pair. |
| Reuse older W952 full provider | Collapse to one older full-provider surface | Rejected because W952 uses the older W947/W725 closedness route, while W987 preserves the W984/W973 branch-specific closed-embedding surface. |

Result: selected for W987. The route verifies that the remaining W986 surface can be supplied by one branch-specific full-data provider while preserving the current W986/W985/W984 route. The current full-data surface drops from two provider-level inputs to one. Product success remains false because W987 still assumes the full-data provider itself, and no original four-task completion witness exists.
