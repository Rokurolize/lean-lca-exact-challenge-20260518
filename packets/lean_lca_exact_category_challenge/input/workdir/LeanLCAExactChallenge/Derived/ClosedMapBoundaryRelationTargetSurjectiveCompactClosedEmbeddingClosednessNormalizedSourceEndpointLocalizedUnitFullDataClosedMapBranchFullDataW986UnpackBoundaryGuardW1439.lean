import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosedMapBranchFullDataW987UnpackBoundaryGuardW1438
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataInnerProviderBoundaryUnpackGuardW1299

/-!
W1439 connects the W1438 W986 component to the canonical W1299 unpack. The
W986 component inside W1007's wrapped W987 input projects to W984
target/closedness data and W950 normalized-source/endpoint data, and the W986
wrapper feeds W985 with exactly those projections.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

/-- Repacking W1007's W986 component through W1299 returns the same W986 component. -/
theorem w1007RepackedW986ComponentIsW986W1439
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    repackTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW1299
        (targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007
          branchFullData) =
      targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007
        branchFullData :=
  repackTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW1299_eq
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007
      branchFullData)

/-- The W985 wrapper over W1007's W986 component keeps the W730 boundary/relation projection. -/
theorem w1007W985BoundaryRelationRunsThroughW986W1439
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
        (w986FullDataOfFullDataW987
          (branchFullDataInputOfBranchFullDataW1007 branchFullData))).boundaryRelationData =
      boundaryRelationDataOfBranchFullDataW1007 branchFullData :=
  rfl

/-- The W985 wrapper over W1007's W986 component uses the W984 projection. -/
theorem w1007W985TargetClosednessRunsThroughW986W1439
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
        (w986FullDataOfFullDataW987
          (branchFullDataInputOfBranchFullDataW1007
            branchFullData))).targetClosedEmbeddingClosednessData =
      targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
        (targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007
          branchFullData) :=
  rfl

/-- The W985 wrapper over W1007's W986 component uses the W950 projection. -/
theorem w1007W985NormalizedEndpointRunsThroughW986W1439
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
        (w986FullDataOfFullDataW987
          (branchFullDataInputOfBranchFullDataW1007
            branchFullData))).normalizedSourceEndpointLocalizedUnitData =
      normalizedSourceEndpointLocalizedUnitDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
        (targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007
          branchFullData) :=
  rfl

/-- W1299 exposes the three concrete inputs after unpacking the W986 component. -/
theorem w1439BranchFullDataUnpackedW730W984W950InputCount :
    canonicalW986InnerUnpackedInputNamesW1299.length = 3 :=
  canonicalW986InnerUnpackedInputNamesW1299_count

/-- The W1298 two-input W730/W986 surface opens to W1299's three-input surface. -/
theorem w1439W1298UnpackExpandsToW1299 :
    canonicalFullDataUnpackedInputNamesW1298.length <
      canonicalW986InnerUnpackedInputNamesW1299.length := by
  rw [canonicalFullDataUnpackedInputNamesW1298_count,
    canonicalW986InnerUnpackedInputNamesW1299_count]
  norm_num

/-- W1007's one-input W987 surface opens to W1299's three-input surface. -/
theorem w1439W1007UnpackExpandsToW1299 :
    branchFullDataInputNamesW1007.length <
      canonicalW986InnerUnpackedInputNamesW1299.length := by
  rw [branchFullDataInputNamesW1007_count,
    canonicalW986InnerUnpackedInputNamesW1299_count]
  norm_num

/-- W1169's one-input branch-full-data surface opens to W1299's three-input surface. -/
theorem w1439W1169UnpackExpandsToW1299 :
    branchFullDataInputNamesW1169.length <
      canonicalW986InnerUnpackedInputNamesW1299.length := by
  rw [branchFullDataInputNamesW1169_count,
    canonicalW986InnerUnpackedInputNamesW1299_count]
  norm_num

/-- Current W1439 nonterminal W986 unpack state. -/
structure ClosedMapBranchFullDataW986UnpackBoundaryStateW1439 : Type where
  seed : String
  declarations : List String
  projectionResult : String
  unpackResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1439 records W1007's concrete W986 unpack boundary after W1438. -/
def currentClosedMapBranchFullDataW986UnpackBoundaryStateW1439 :
    ClosedMapBranchFullDataW986UnpackBoundaryStateW1439 where
  seed := "w1439-closed-map-branch-full-data-w986-unpack-boundary"
  declarations :=
    ["w1007RepackedW986ComponentIsW986W1439",
      "w1007W985BoundaryRelationRunsThroughW986W1439",
      "w1007W985TargetClosednessRunsThroughW986W1439",
      "w1007W985NormalizedEndpointRunsThroughW986W1439",
      "w1439BranchFullDataUnpackedW730W984W950InputCount",
      "w1439W1298UnpackExpandsToW1299",
      "w1439W1007UnpackExpandsToW1299",
      "w1439W1169UnpackExpandsToW1299"]
  projectionResult :=
    "proved: W1007's W986 component projects to W984 target/closedness data\
      and W950 normalized-source/endpoint data, and W985 receives those fields"
  unpackResult :=
    "proved: unpacking the W1438 W730/W986 surface exposes the W1299\
      three-input W730/W984/W950 surface, so this remains nonterminal"
  remainingInputs := canonicalW986InnerUnpackedInputNamesW1299
  productSuccessClaimed := false

theorem currentW1439ClosedMapBranchFullDataW986UnpackBoundary_productSuccess :
    currentClosedMapBranchFullDataW986UnpackBoundaryStateW1439.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
