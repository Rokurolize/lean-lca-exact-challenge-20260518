# Source Patch Needed: W1450 Provider Leaf Reassessment

Generated UTC: 2026-06-10T08:38:47Z

## Outcome

- `terminal_outcome`: `source_patch_needed_handoff`
- `product_success`: false
- `product_complete`: false
- `update_goal_allowed`: false
- Source head inspected: `f54abe885afc28ccba7f9d71567a7ba52323699a`
- Latest source checkpoint: `run/source_patch_needed_w1450_nullary_frontier_20260610.md`

This reassessment does not change product-facing Lean source and does not claim the original four-task witness. It checks the next step after the W1450 nullary-frontier handoff: whether one of the four W1450 provider packages can be made nullary by a small existing source construction. Current source still cannot do that.

## Files Inspected

- `LeanLCAExactChallenge/Derived/ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987FieldDataConstructionGuardW1450.lean`
- `LeanLCAExactChallenge/Derived/ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987BoundaryFieldDataConstructionGuardW1451.lean`
- `LeanLCAExactChallenge/Derived/ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987BoundaryRelationFieldDataConstructionGuardW1452.lean`
- `LeanLCAExactChallenge/Derived/WppOpExactAcyclicProjectionFields.lean`
- `LeanLCAExactChallenge/Derived/ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessEndpointLocalizedUnitChoiceDataRoute.lean`
- `LeanLCAExactChallenge/Derived/ClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataPrimitiveFieldRoute.lean`
- `LeanLCAExactChallenge/Derived/ClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataPrimitiveFieldRoute.lean`
- `LeanLCAExactChallenge/Derived/ClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataPrimitiveFieldRoute.lean`
- `LeanLCAExactChallenge/Derived/ClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsPrimitiveFieldRoute.lean`
- `LeanLCAExactChallenge/Derived/ClosedMapBoundaryRelationDataTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopAndUnitKernelCokernelTopIsoComponentFieldsRoute.lean`

## Provider Expansion Result

The four W1450 provider packages are still:

```lean
Dbounded.MetrizableWppLimitBoundaryDataW716
Dbounded.ClosedNatTransOrdinaryRelationDataProviderW717
Dbounded.TargetNoUnivClosedEmbeddingClosednessDataProviderW984
Dbounded.NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950
```

Expanding them through existing constructors exposes eight immediate leaf obligations:

```lean
Dbounded.MetrizableWppLimitRightOpenClosedQuotientCoverBoundary
Dbounded.MetrizableWppLimitSourceDifferenceCokernelPiZeroBoundary
Dbounded.ClosedNatTransOrdinaryRelationPullbackProviderW712
Dbounded.ClosedNatTransOrdinaryTargetRelationLiftsProviderW712
Dbounded.TargetSurjectiveNoUnivMembershipForTargetProviderW944
Dbounded.ClosedEmbeddingClosednessDataProviderW973
Dbounded.NormalizedFixedTargetSourceTriangulationDataProviderW948
Dbounded.EndpointStrictExactLocalizedUnitDataProviderW949
```

This is not a new product frontier. It is the already recorded 2026-06-09 field-component frontier, now rechecked against the pushed W1450 product-data path at `f54abe885afc28ccba7f9d71567a7ba52323699a`.

## Existing Proof Evidence Reused

The existing expected-failure probe remains the precise Lean artifact for the eight-leaf expansion:

```text
run/w1450_field_component_frontier_probe_20260609.lean
run/verify_w1450_field_component_frontier_probe_20260609.log
run/source_patch_needed_w1450_field_component_frontier_20260609.md
```

No duplicate probe was added in this checkpoint. The current W1450 nullary probe remains:

```text
run/source_patch_attempt_w1450_nullary_witness_20260610.lean
run/source_patch_attempt_w1450_nullary_witness_20260610T083900Z.log
```

## Rejected Next Steps

- Expanding W716 via W1451 replaces one W716 input by `MetrizableWppLimitRightOpenClosedQuotientCoverBoundary` and `MetrizableWppLimitSourceDifferenceCokernelPiZeroBoundary`, increasing the W1450 surface from 4 inputs to 5.
- Expanding W717 via W1452 replaces one W717 input by `ClosedNatTransOrdinaryRelationPullbackProviderW712` and `ClosedNatTransOrdinaryTargetRelationLiftsProviderW712`, increasing the W1451 surface from 5 inputs to 6.
- Expanding W984 only splits it into W944 target no-univ data plus W973 closed-embedding closedness data.
- Expanding W950 only splits it into W948 normalized-source-triangulation data plus W949 endpoint-localized-unit data.
- The W949 endpoint/localized-unit package itself includes the broad field `∀ (K : CochainComplex MetrizableLCA ℤ) (i : ℤ), MetrizableLCA.strictShortExact (K.sc i)`, so treating W949 as a small implementation target would still require a substantial mathematical source theorem, not a wrapper.

Therefore another wrapper, unpack route, or route-ledger commit is not justified unless it constructs one of these eight leaves or bypasses W1450 with a real nullary stable package.

## Exact Missing Source API

The next useful source patch should prove at least one of these declarations from current mathematical source, with no caller-supplied record carrying the same obligation:

```lean
noncomputable def Dbounded.nullaryMetrizableWppLimitRightOpenClosedQuotientCoverBoundary :
    Dbounded.MetrizableWppLimitRightOpenClosedQuotientCoverBoundary

noncomputable def Dbounded.nullaryMetrizableWppLimitSourceDifferenceCokernelPiZeroBoundary :
    Dbounded.MetrizableWppLimitSourceDifferenceCokernelPiZeroBoundary

theorem Dbounded.nullaryClosedNatTransOrdinaryRelationPullbackProviderW712 :
    Dbounded.ClosedNatTransOrdinaryRelationPullbackProviderW712

theorem Dbounded.nullaryClosedNatTransOrdinaryTargetRelationLiftsProviderW712 :
    Dbounded.ClosedNatTransOrdinaryTargetRelationLiftsProviderW712

theorem Dbounded.nullaryTargetSurjectiveNoUnivMembershipForTargetProviderW944 :
    Dbounded.TargetSurjectiveNoUnivMembershipForTargetProviderW944

noncomputable def Dbounded.nullaryClosedEmbeddingClosednessDataProviderW973 :
    Dbounded.ClosedEmbeddingClosednessDataProviderW973

noncomputable def Dbounded.nullaryNormalizedFixedTargetSourceTriangulationDataProviderW948 :
    Dbounded.NormalizedFixedTargetSourceTriangulationDataProviderW948

noncomputable def Dbounded.nullaryEndpointStrictExactLocalizedUnitDataProviderW949 :
    Dbounded.EndpointStrictExactLocalizedUnitDataProviderW949
```

The alternative remains a real nullary `BoundedDerived.Metrizable.StablePackage`, beginning with the missing `Preadditive (Dbounded MetrizableLCA)` instance family and the other stable instance families recorded in `Dbounded.metrizableStableInstanceFieldNames`.

## Verification Notes

Fresh resumption and stable v4.30.0 regression logs for this reassessment are saved under:

```text
run/resumption_20260610T083611Z_*
run/stable_v4300_20260610T083611Z_*
```

The `stable_v4300_20260610T083611Z_rc2_scan.exit` file is `1`, which is the expected `rg` no-match status for absent `v4.30.0-rc2` references.

## Next Safe Action

Implement one of the eight immediate leaf APIs above, or replace the W1450 route with a smaller nullary stable-package proof. Do not continue by splitting W716/W717/W984/W950 into larger caller-supplied records unless a split simultaneously proves a leaf inhabitant.
