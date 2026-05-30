import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosedMapBranchFullDataOneInputCycleGuardW1437
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderBoundaryUnpackGuardW1298

/-!
W1438 connects the W1437/W1169 branch-full-data surface to the canonical W1298
unpack of W987. W1007's wrapped W987 input projects to W730 boundary/relation
data and W986 target/closedness/normalized-source/endpoint data. Unpacking that
single W987 input exposes the two-input W1298 surface, so this records the next
concrete boundary without claiming product success.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

/-- W1007's W730 projection is the W987 boundary/relation projection. -/
theorem w1007BoundaryRelationProjectionThroughW987W1438
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    boundaryRelationDataOfBranchFullDataW1007 branchFullData =
      boundaryRelationDataOfFullDataW987
        (branchFullDataInputOfBranchFullDataW1007 branchFullData) :=
  rfl

/-- W1007's W986 projection is the W987 target/closedness/normalized-source/endpoint projection. -/
theorem w1007TargetNormalizedEndpointProjectionThroughW987W1438
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007
        branchFullData =
      targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (branchFullDataInputOfBranchFullDataW1007 branchFullData) :=
  rfl

/-- W1007's W986 full-data wrapper uses the W987 W730 projection. -/
theorem w1007W986FullDataBoundaryRelationRunsThroughW987W1438
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (w986FullDataOfFullDataW987
        (branchFullDataInputOfBranchFullDataW1007 branchFullData)).boundaryRelationData =
      boundaryRelationDataOfBranchFullDataW1007 branchFullData :=
  rfl

/-- W1007's W986 full-data wrapper uses the W987 W986 projection. -/
theorem w1007W986FullDataTargetDataRunsThroughW987W1438
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (w986FullDataOfFullDataW987
        (branchFullDataInputOfBranchFullDataW1007
          branchFullData)).targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitData =
      targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007
        branchFullData :=
  rfl

/-- Repacking the W1007 W987 input through W1298 returns the same W987 input. -/
theorem w1007RepackedW987InputIsW987W1438
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    repackFullDataOfFullDataW1298
        (branchFullDataInputOfBranchFullDataW1007 branchFullData) =
      branchFullDataInputOfBranchFullDataW1007 branchFullData :=
  repackFullDataOfFullDataW1298_eq
    (branchFullDataInputOfBranchFullDataW1007 branchFullData)

/-- W1298 exposes the two concrete inputs inside the W987 package. -/
theorem w1438BranchFullDataUnpackedW730W986InputCount :
    canonicalFullDataUnpackedInputNamesW1298.length = 2 :=
  canonicalFullDataUnpackedInputNamesW1298_count

/-- W1007's one W987 input opens to the two-input W1298 surface. -/
theorem w1438W1007UnpackExpandsOneInputSurface :
    branchFullDataInputNamesW1007.length <
      canonicalFullDataUnpackedInputNamesW1298.length := by
  rw [branchFullDataInputNamesW1007_count,
    canonicalFullDataUnpackedInputNamesW1298_count]
  norm_num

/-- W1169's one W1007 input opens to the two-input W1298 surface. -/
theorem w1438W1169UnpackExpandsOneInputSurface :
    branchFullDataInputNamesW1169.length <
      canonicalFullDataUnpackedInputNamesW1298.length := by
  rw [branchFullDataInputNamesW1169_count,
    canonicalFullDataUnpackedInputNamesW1298_count]
  norm_num

/-- Current W1438 nonterminal W987 unpack state. -/
structure ClosedMapBranchFullDataW987UnpackBoundaryStateW1438 : Type where
  seed : String
  declarations : List String
  projectionResult : String
  unpackResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1438 records W1007's concrete W987 unpack boundary after W1437. -/
def currentClosedMapBranchFullDataW987UnpackBoundaryStateW1438 :
    ClosedMapBranchFullDataW987UnpackBoundaryStateW1438 where
  seed := "w1438-closed-map-branch-full-data-w987-unpack-boundary"
  declarations :=
    ["w1007BoundaryRelationProjectionThroughW987W1438",
      "w1007TargetNormalizedEndpointProjectionThroughW987W1438",
      "w1007W986FullDataBoundaryRelationRunsThroughW987W1438",
      "w1007W986FullDataTargetDataRunsThroughW987W1438",
      "w1007RepackedW987InputIsW987W1438",
      "w1438BranchFullDataUnpackedW730W986InputCount",
      "w1438W1007UnpackExpandsOneInputSurface",
      "w1438W1169UnpackExpandsOneInputSurface"]
  projectionResult :=
    "proved: W1007's wrapped W987 input projects to W730 boundary/relation\
      data and W986 target/closedness/normalized-source/endpoint data"
  unpackResult :=
    "proved: unpacking the W1437/W1169 one-input W987 package exposes the\
      W1298 two-input W730/W986 surface, so this is a nonterminal boundary"
  remainingInputs := canonicalFullDataUnpackedInputNamesW1298
  productSuccessClaimed := false

theorem currentW1438ClosedMapBranchFullDataW987UnpackBoundary_productSuccess :
    currentClosedMapBranchFullDataW987UnpackBoundaryStateW1438.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
