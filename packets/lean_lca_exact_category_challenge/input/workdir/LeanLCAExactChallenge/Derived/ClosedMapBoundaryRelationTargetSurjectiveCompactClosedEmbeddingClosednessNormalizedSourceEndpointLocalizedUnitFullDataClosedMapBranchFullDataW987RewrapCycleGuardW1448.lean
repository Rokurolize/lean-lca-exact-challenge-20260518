import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosedMapBranchFullDataW989LocalizedUnitChoiceFullDataPackagingGuardW1447

/-!
W1448 records the rewrap after W1447. The W987 full data rebuilt by W988 can be
wrapped again as a W1007 branch-full-data provider, and the W1007 projections
recover the W730 boundary/relation data and W986 target/closedness/
normalized-source/endpoint data that W988 built from the W982 fields.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def w1007W987RewrappedInputNamesW1448 : List String :=
  fullDataInputNamesW987

theorem w1007W987RewrappedInputNamesW1448_count :
    w1007W987RewrappedInputNamesW1448.length = 1 :=
  fullDataInputNamesW987_count

/-- W1448 wraps W1447's rebuilt W987 full data as a W1007 provider. -/
noncomputable def w1007BranchFullDataProviderOfW1447
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007
    where
  branchFullData := w1007FullDataOfLocalizedUnitChoiceW1447 branchFullData

/-- The W1448 W1007 wrapper contains exactly W1447's rebuilt W987 full data. -/
theorem w1007RewrappedBranchFullDataInputIsW1447FullDataW1448
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    branchFullDataInputOfBranchFullDataW1007
        (w1007BranchFullDataProviderOfW1447 branchFullData) =
      w1007FullDataOfLocalizedUnitChoiceW1447 branchFullData :=
  rfl

/-- The W1448 wrapper projects the W730 data from W1447's W982 package. -/
theorem w1007RewrappedBoundaryRelationRunsThroughW1447W1448
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    boundaryRelationDataOfBranchFullDataW1007
        (w1007BranchFullDataProviderOfW1447 branchFullData) =
      (w1007LocalizedUnitChoiceDataW1447
        branchFullData).boundaryRelationData :=
  rfl

/-- The W1448 wrapper projects W988's W986 target/normalized-endpoint data. -/
theorem w1007RewrappedTargetNormalizedEndpointRunsThroughW1447W1448
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007
        (w1007BranchFullDataProviderOfW1447 branchFullData) =
      targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfLocalizedUnitChoiceW988
        (w1007LocalizedUnitChoiceDataW1447 branchFullData) :=
  rfl

/-- The W1448 wrapper's W987 unpack sees the W1447 W730 component. -/
theorem w1007RewrappedW986FullDataBoundaryRunsThroughW1447W1448
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (w986FullDataOfFullDataW987
        (branchFullDataInputOfBranchFullDataW1007
          (w1007BranchFullDataProviderOfW1447
            branchFullData))).boundaryRelationData =
      (w1007LocalizedUnitChoiceDataW1447
        branchFullData).boundaryRelationData :=
  rfl

/-- The W1448 wrapper's W987 unpack sees the W1447 W986 component. -/
theorem w1007RewrappedW986FullDataTargetDataRunsThroughW1447W1448
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (w986FullDataOfFullDataW987
        (branchFullDataInputOfBranchFullDataW1007
          (w1007BranchFullDataProviderOfW1447
            branchFullData))).targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitData =
      targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfLocalizedUnitChoiceW988
        (w1007LocalizedUnitChoiceDataW1447 branchFullData) :=
  rfl

/-- The W1438 W987 repack is identity on the W1448 rewrapped provider. -/
theorem w1007RewrappedRepackedW987InputIsW987W1448
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    repackFullDataOfFullDataW1298
        (branchFullDataInputOfBranchFullDataW1007
          (w1007BranchFullDataProviderOfW1447 branchFullData)) =
      branchFullDataInputOfBranchFullDataW1007
        (w1007BranchFullDataProviderOfW1447 branchFullData) :=
  w1007RepackedW987InputIsW987W1438
    (w1007BranchFullDataProviderOfW1447 branchFullData)

/-- W1448 keeps W987's one-input rewrapped full-data surface visible. -/
theorem w1448W987RewrappedInputCount :
    w1007W987RewrappedInputNamesW1448.length = 1 :=
  w1007W987RewrappedInputNamesW1448_count

/-- W1448 repackages W1447's six-input W988 surface as one W987 input. -/
theorem w1448W989LocalizedUnitChoicePackagesToW987FullData :
    w1007W987RewrappedInputNamesW1448.length <
      w1007W989LocalizedUnitChoiceInputNamesW1447.length := by
  rw [w1007W987RewrappedInputNamesW1448_count,
    w1007W989LocalizedUnitChoiceInputNamesW1447_count]
  norm_num

/-- Current W1448 nonterminal W987 rewrap cycle state. -/
structure ClosedMapBranchFullDataW987RewrapCycleStateW1448 : Type where
  seed : String
  declarations : List String
  rewrapResult : String
  cycleResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1448 records the W1447 rebuilt W987 data rewrapped as a W1007 provider. -/
def currentClosedMapBranchFullDataW987RewrapCycleStateW1448 :
    ClosedMapBranchFullDataW987RewrapCycleStateW1448 where
  seed := "w1448-closed-map-branch-full-data-w987-rewrap-cycle"
  declarations :=
    ["w1007BranchFullDataProviderOfW1447",
      "w1007RewrappedBranchFullDataInputIsW1447FullDataW1448",
      "w1007RewrappedBoundaryRelationRunsThroughW1447W1448",
      "w1007RewrappedTargetNormalizedEndpointRunsThroughW1447W1448",
      "w1007RewrappedW986FullDataBoundaryRunsThroughW1447W1448",
      "w1007RewrappedW986FullDataTargetDataRunsThroughW1447W1448",
      "w1007RewrappedRepackedW987InputIsW987W1448",
      "w1448W987RewrappedInputCount",
      "w1448W989LocalizedUnitChoicePackagesToW987FullData"]
  rewrapResult :=
    "proved: W1447's W987 full data rewraps as W1007 branch-full-data while\
      preserving the W730 boundary/relation and W986 target/normalized-endpoint\
      projections"
  cycleResult :=
    "proved: W1438's W987 repack is identity on the W1448 rewrapped provider;\
      this records a nonterminal route cycle rather than product success"
  remainingInputs := w1007W987RewrappedInputNamesW1448
  productSuccessClaimed := false

theorem currentW1448ClosedMapBranchFullDataW987RewrapCycle_productSuccess :
    currentClosedMapBranchFullDataW987RewrapCycleStateW1448.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
