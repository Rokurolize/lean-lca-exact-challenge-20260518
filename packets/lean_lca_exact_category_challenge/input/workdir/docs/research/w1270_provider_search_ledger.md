# W1270 Provider Search Ledger

Date: 2026-05-29

W1270 follows W1269 by inspecting the existing W987 route. The relevant constructor is `w986FullDataOfFullDataW987`, which constructs `BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986` from `BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987`.

The W1270 bridge composes:

1. `w986FullDataOfFullDataW987`
2. `currentFullDataPayloadOfTargetNormalizedEndpointW1269`
3. the W1008 wrapper field `currentFullData`

Input result: `fullDataInputNamesW987_count` proves the W987 replacement surface has one explicit input. W1270 records this as a reduction from W1269's two W986 inputs, but not as product success because the W987 branch-full-data provider remains external.
