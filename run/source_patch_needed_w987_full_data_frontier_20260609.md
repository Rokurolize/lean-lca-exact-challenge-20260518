# Source Patch Needed: W987 Full-Data Frontier

Generated UTC: 2026-06-09T19:44:54Z

## Outcome

- `terminal_outcome`: `source_patch_needed_handoff`
- `product_success`: false
- `product_complete`: false
- `update_goal_allowed`: false
- Source head inspected: `12e536e26c2c5bb1a3706007433cfce4a4d4c952`
- Latest source checkpoint: `run/w1625_full_data_closed_embedding_closedness_direct_localization_boundary_checkpoint_20260609.md`

This checkpoint does not change product-facing Lean source. W1625 already removed the W1007 wrapper obligation and made the direct-localization boundary depend on the underlying W987 full-data provider itself. The next honest source patch is therefore a nullary W987 provider, or a stronger canonical theorem that eliminates that W987 provider without reopening an already-checked larger surface.

## Files Inspected

- `LeanLCAExactChallenge/Derived/ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataRoute.lean`
- `LeanLCAExactChallenge/Derived/ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataRoute.lean`
- `LeanLCAExactChallenge/Derived/WppOpExactAcyclicProjectionFields.lean`
- `LeanLCAExactChallenge/Derived/ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataCurrentFullDataPayloadFromBranchFullDataW1270.lean`
- `LeanLCAExactChallenge/Derived/ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosedMapBranchFullDataOneInputCycleGuardW1437.lean`
- `LeanLCAExactChallenge/Derived/ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataPrimitiveUnitAndBranchWrapperGuardW1278.lean`
- `LeanLCAExactChallenge/Derived/ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderBoundaryUnpackGuardW1298.lean`
- `LeanLCAExactChallenge/Derived/ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataInnerProviderBoundaryUnpackGuardW1299.lean`
- `LeanLCAExactChallenge/Derived/ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataBoundaryRelationBoundaryUnpackGuardW1305.lean`
- `LeanLCAExactChallenge/Derived/ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987FieldDataConstructionGuardW1450.lean`

## What Current Source Proves

- W987 is one caller-supplied provider:

```lean
BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987
```

- W987 packages exactly these two fields:

```lean
boundaryRelationData :
  MetrizableWppBoundaryRelationDataProviderW730

targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitData :
  TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986
```

- W1270 proves the one-input W987 surface reduces the older W1269 two-input target-normalized endpoint surface.
- W1298 proves unpacking W987 exposes the two-input W730/W986 surface and expands the current one-input frontier.
- W1299 proves unpacking W986 exposes the three-input W730/W984/W950 surface and expands the current one-input frontier.
- W1305 proves unpacking W730 exposes W716/W717 and that the W730, W716, and W717 routes expand beyond the current one-input frontier.
- W1450 proves W987 can be built from W716/W717/W984/W950, but also proves that this four-field construction surface expands the current W987 provider frontier.

## Declaration-Shape Search

The following tighter scans found no no-argument constructor for W987, W730, W986, or the W1450 field-data record:

```bash
rg -nUP "(?s)(noncomputable\s+)?def\s+\S+\s*:\s*\n\s*BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987\s*(:=|where)" LeanLCAExactChallenge audit -g '*.lean'
rg -nUP "(?s)(noncomputable\s+)?def\s+\S+\s*:\s*\n\s*MetrizableWppBoundaryRelationDataProviderW730\s*(:=|where)" LeanLCAExactChallenge audit -g '*.lean'
rg -nUP "(?s)(noncomputable\s+)?def\s+\S+\s*:\s*\n\s*TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986\s*(:=|where)" LeanLCAExactChallenge audit -g '*.lean'
rg -nUP "(?s)(noncomputable\s+)?def\s+\S+\s*:\s*\n\s*W987FieldDataConstructionInputW1450\s*(:=|where)" LeanLCAExactChallenge audit -g '*.lean'
```

All four scans returned no matches.

## Lean Probe

Probe file:

```text
run/w987_full_data_frontier_probe_20260609.lean
```

Expected-failure log:

```text
run/verify_w987_full_data_frontier_probe_20260609.log
```

The probe checks the W987 frontier declarations and then attempts the smallest available construction:

```lean
noncomputable def attemptedNullaryW987FullDataProvider :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 := by
  exact fullDataOfW987FieldDataW1450 ?fieldData
```

The resulting unsolved placeholder is exactly:

```lean
?fieldData : W987FieldDataConstructionInputW1450
```

This confirms that current source can assemble W987 from W1450 data, but does not provide that data nullarily.

## Exact Missing Source API

The smallest useful source patch is one of these, proved without assumptions, arbitrary `Prop` fields, semantic adapters, or caller-supplied records:

```lean
noncomputable def Dbounded.nullaryW987FieldDataConstructionInput :
    W987FieldDataConstructionInputW1450
```

or directly:

```lean
noncomputable def Dbounded.nullaryBoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProvider :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987
```

The W1450 version must honestly provide:

```lean
boundaryData :
  MetrizableWppLimitBoundaryDataW716

relationData :
  ClosedNatTransOrdinaryRelationDataProviderW717

targetClosedEmbeddingClosednessData :
  TargetNoUnivClosedEmbeddingClosednessDataProviderW984

normalizedSourceEndpointLocalizedUnitData :
  NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950
```

## Why This Blocks Product Success

The W1625 direct-localization boundary can now consume W987 directly, but W987 is still a caller-supplied provider. Expanding it into W730/W986, W730/W984/W950, W716/W717/W984/W950, W990's primitive-unit surface, or later W1497/W1498-style field surfaces only increases the remaining input count. Product success remains false because no nullary original four-task witness exists.

## Next Safe Action

Construct the W1450 field-data input from actual mathematical source declarations, or bypass it with a stronger canonical theorem that supplies the same W987 full data without caller input. Do not add another W987 wrapper or unpack route unless it constructs one of the missing fields above or eliminates the W987 provider entirely.
