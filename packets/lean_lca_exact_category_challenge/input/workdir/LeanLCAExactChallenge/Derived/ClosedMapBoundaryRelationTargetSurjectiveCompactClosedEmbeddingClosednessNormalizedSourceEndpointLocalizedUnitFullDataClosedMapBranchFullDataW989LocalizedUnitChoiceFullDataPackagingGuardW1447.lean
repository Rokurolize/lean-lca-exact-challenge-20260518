import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosedMapBranchFullDataW990UnitStrictExactIsoPackagingGuardW1446

/-!
W1447 records the W989-to-W988 packaging step after W1446. The W1007-derived
W981 package builds W982 localized-unit-choice data through W989, then W988
rebuilds W987 full data from the W982 fields while preserving the W730,
W984, and W950 components.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def w1007W989LocalizedUnitChoiceInputNamesW1447 : List String :=
  localizedUnitChoiceInputNamesW988

theorem w1007W989LocalizedUnitChoiceInputNamesW1447_count :
    w1007W989LocalizedUnitChoiceInputNamesW1447.length = 6 :=
  localizedUnitChoiceInputNamesW988_count

/-- W1447 builds W982 localized-unit-choice data from the W1446 W981 package. -/
noncomputable def w1007LocalizedUnitChoiceDataW1447
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfUnitStrictExactIsoW989
    (w1007UnitStrictExactIsoFullDataW1446 branchFullData)

/-- W1447 rebuilds W987 full data through W988 from W989 localized-unit-choice data. -/
noncomputable def w1007FullDataOfLocalizedUnitChoiceW1447
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfLocalizedUnitChoiceW988
    (w1007LocalizedUnitChoiceDataW1447 branchFullData)

/-- The W1447 W982 package keeps W1446's boundary/relation data. -/
theorem w1007W989LocalizedUnitChoiceKeepsBoundaryRelationW1447
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (w1007LocalizedUnitChoiceDataW1447
        branchFullData).boundaryRelationData =
      (w1007UnitStrictExactIsoFullDataW1446
        branchFullData).boundaryRelationData :=
  rfl

/-- The W1447 W982 package keeps W1446's rebuilt localized-unit data. -/
theorem w1007W989LocalizedUnitChoiceKeepsLocalizedUnitDataW1447
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (w1007LocalizedUnitChoiceDataW1447
        branchFullData).localizedUnitData =
      w1007W989LocalizedUnitDataW1446 branchFullData :=
  rfl

/-- The W1447 W982 package keeps W1446's normalized-source data. -/
theorem w1007W989LocalizedUnitChoiceKeepsNormalizedSourceW1447
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (w1007LocalizedUnitChoiceDataW1447
        branchFullData).normalizedSourceTriangulationData =
      (w1007UnitStrictExactIsoFullDataW1446
        branchFullData).normalizedSourceTriangulationData :=
  rfl

/-- W988 rebuilds W984 target/closedness data from W1447's W982 package. -/
theorem w1007W988TargetClosednessRunsThroughLocalizedUnitChoiceW1447
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (w1007FullDataOfLocalizedUnitChoiceW1447
        branchFullData).targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitData.targetClosedEmbeddingClosednessData =
      targetClosedEmbeddingClosednessDataOfLocalizedUnitChoiceW988
        (w1007LocalizedUnitChoiceDataW1447 branchFullData) :=
  rfl

/-- W988 rebuilds W949 endpoint-localized-unit data from W1447's W982 package. -/
theorem w1007W988EndpointLocalizedUnitRunsThroughLocalizedUnitChoiceW1447
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (w1007FullDataOfLocalizedUnitChoiceW1447
        branchFullData).targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitData.normalizedSourceEndpointLocalizedUnitData.endpointLocalizedUnitData =
      endpointLocalizedUnitDataOfLocalizedUnitChoiceW988
        (w1007LocalizedUnitChoiceDataW1447 branchFullData) :=
  rfl

/-- W988 rebuilds W950 normalized-source/endpoint data from W1447's W982 package. -/
theorem w1007W988NormalizedEndpointRunsThroughLocalizedUnitChoiceW1447
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (w1007FullDataOfLocalizedUnitChoiceW1447
        branchFullData).targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitData.normalizedSourceEndpointLocalizedUnitData =
      normalizedSourceEndpointLocalizedUnitDataOfLocalizedUnitChoiceW988
        (w1007LocalizedUnitChoiceDataW1447 branchFullData) :=
  rfl

/-- W988 rebuilds W987 full data from W1447's W982 package. -/
theorem w1007W988FullDataRunsThroughLocalizedUnitChoiceW1447
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    w1007FullDataOfLocalizedUnitChoiceW1447 branchFullData =
      fullDataOfLocalizedUnitChoiceW988
        (w1007LocalizedUnitChoiceDataW1447 branchFullData) :=
  rfl

/-- W1447 keeps W988's six-input localized-unit-choice surface visible. -/
theorem w1447W988LocalizedUnitChoiceInputCount :
    w1007W989LocalizedUnitChoiceInputNamesW1447.length = 6 :=
  w1007W989LocalizedUnitChoiceInputNamesW1447_count

/-- W1447 packages W1446's seven-input W981 package into W988's six-input W982 surface. -/
theorem w1447W989UnitStrictExactIsoPackagesToW988LocalizedUnitChoice :
    w1007W989LocalizedUnitChoiceInputNamesW1447.length <
      w1007W990UnitStrictExactIsoPackagedInputNamesW1446.length := by
  rw [w1007W989LocalizedUnitChoiceInputNamesW1447_count,
    w1007W990UnitStrictExactIsoPackagedInputNamesW1446_count]
  norm_num

/-- Current W1447 nonterminal W989-to-W988 localized-unit-choice packaging state. -/
structure ClosedMapBranchFullDataW989LocalizedUnitChoiceFullDataPackagingStateW1447 :
    Type where
  seed : String
  declarations : List String
  packagingResult : String
  routeResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1447 records W989 localized-unit-choice packaging and W988 full-data reconstruction. -/
def currentClosedMapBranchFullDataW989LocalizedUnitChoiceFullDataPackagingStateW1447 :
    ClosedMapBranchFullDataW989LocalizedUnitChoiceFullDataPackagingStateW1447 where
  seed := "w1447-closed-map-branch-full-data-w989-localized-unit-choice-full-data-packaging"
  declarations :=
    ["w1007LocalizedUnitChoiceDataW1447",
      "w1007FullDataOfLocalizedUnitChoiceW1447",
      "w1007W989LocalizedUnitChoiceKeepsBoundaryRelationW1447",
      "w1007W989LocalizedUnitChoiceKeepsLocalizedUnitDataW1447",
      "w1007W989LocalizedUnitChoiceKeepsNormalizedSourceW1447",
      "w1007W988TargetClosednessRunsThroughLocalizedUnitChoiceW1447",
      "w1007W988EndpointLocalizedUnitRunsThroughLocalizedUnitChoiceW1447",
      "w1007W988NormalizedEndpointRunsThroughLocalizedUnitChoiceW1447",
      "w1007W988FullDataRunsThroughLocalizedUnitChoiceW1447",
      "w1447W988LocalizedUnitChoiceInputCount",
      "w1447W989UnitStrictExactIsoPackagesToW988LocalizedUnitChoice"]
  packagingResult :=
    "proved: W1446's W981 package forms W982 localized-unit-choice data,\
      preserving boundary/relation data, localized-unit data, and W948 data"
  routeResult :=
    "proved: W988 rebuilds W987 full data from that W982 package while\
      preserving the W984 target/closedness and W950 normalized-endpoint\
      components; product success is still not claimed"
  remainingInputs := w1007W989LocalizedUnitChoiceInputNamesW1447
  productSuccessClaimed := false

theorem currentW1447ClosedMapBranchFullDataW989LocalizedUnitChoiceFullDataPackaging_productSuccess :
    currentClosedMapBranchFullDataW989LocalizedUnitChoiceFullDataPackagingStateW1447.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
