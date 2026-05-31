import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosedMapBranchFullDataW950NormalizedEndpointUnpackBoundaryGuardW1441
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataNormalizedSourceTriangulationBoundaryUnpackGuardW1303

/-!
W1442 connects the W948 normalized-source-triangulation component exposed by
W1441 to the canonical W1303 unpack. The W1007 branch-full-data route therefore
exposes the W730 boundary/relation provider, W944 target no-univ data, W973
closed-embedding closedness data, W719 normalized fixed-target data, W722
source-triangulation data, and W949 endpoint-localized-unit data.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def w1007W948NormalizedSourceUnpackedInputNamesW1442 : List String :=
  ["W730 boundary/relation data provider",
    "W944 target no-univ data provider",
    "W973 closed-embedding closedness data provider",
    "W719 normalized fixed-target data provider",
    "W722 source-triangulation data provider",
    "W949 endpoint-localized-unit data provider"]

theorem w1007W948NormalizedSourceUnpackedInputNamesW1442_count :
    w1007W948NormalizedSourceUnpackedInputNamesW1442.length = 6 :=
  rfl

/-- Repacking W1007's W948 component through W1303 returns the same W948 component. -/
theorem w1007RepackedW948ComponentIsW948W1442
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    repackNormalizedSourceTriangulationDataW1303
        (normalizedSourceTriangulationDataOfNormalizedSourceEndpointLocalizedUnitDataW950
          (normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007 branchFullData)) =
      normalizedSourceTriangulationDataOfNormalizedSourceEndpointLocalizedUnitDataW950
        (normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007 branchFullData) :=
  repackNormalizedSourceTriangulationDataW1303_eq
    (normalizedSourceTriangulationDataOfNormalizedSourceEndpointLocalizedUnitDataW950
      (normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007 branchFullData))

/-- W1007's W985 surface feeds W984 with the W948 normalized-source component. -/
theorem w1007W985NormalizedSourceComponentRunsThroughW948W1442
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (fullDataOfNormalizedSourceEndpointLocalizedUnitW985
        (fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
          (w986FullDataOfFullDataW987
            (branchFullDataInputOfBranchFullDataW1007
              branchFullData)))).normalizedSourceTriangulationData =
      normalizedSourceTriangulationDataOfNormalizedSourceEndpointLocalizedUnitDataW950
        (normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007 branchFullData) :=
  rfl

/-- The W948 component over W1007's W950 data keeps the W719 normalized fixed-target field. -/
theorem w1007W948NormalizedFixedTargetRunsThroughW1442
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    normalizedFixedTargetDataOfNormalizedSourceTriangulationDataW948
        ((fullDataOfNormalizedSourceEndpointLocalizedUnitW985
          (fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
            (w986FullDataOfFullDataW987
              (branchFullDataInputOfBranchFullDataW1007
                branchFullData)))).normalizedSourceTriangulationData) =
      normalizedFixedTargetDataOfNormalizedSourceTriangulationDataW948
        (normalizedSourceTriangulationDataOfNormalizedSourceEndpointLocalizedUnitDataW950
          (normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007 branchFullData)) :=
  rfl

/-- The W948 component over W1007's W950 data keeps the W722 source-triangulation field. -/
theorem w1007W948SourceTriangulationRunsThroughW1442
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    sourceTriangulationDataOfNormalizedSourceTriangulationDataW948
        ((fullDataOfNormalizedSourceEndpointLocalizedUnitW985
          (fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
            (w986FullDataOfFullDataW987
              (branchFullDataInputOfBranchFullDataW1007
                branchFullData)))).normalizedSourceTriangulationData) =
      sourceTriangulationDataOfNormalizedSourceTriangulationDataW948
        (normalizedSourceTriangulationDataOfNormalizedSourceEndpointLocalizedUnitDataW950
          (normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007 branchFullData)) :=
  rfl

/-- W1442 exposes the six inputs obtained by unpacking W1441's W948 component. -/
theorem w1442BranchFullDataUnpackedW730W944W973W719W722W949InputCount :
    w1007W948NormalizedSourceUnpackedInputNamesW1442.length = 6 :=
  w1007W948NormalizedSourceUnpackedInputNamesW1442_count

/-- W1303 records the two internal W948 normalized-source-triangulation inputs. -/
theorem w1442W948NormalizedSourceInnerInputCount :
    canonicalW948NormalizedSourceTriangulationInnerInputNamesW1303.length = 2 :=
  canonicalW948NormalizedSourceTriangulationInnerInputNamesW1303_count

/-- W1441's five-input W730/W944/W973/W948/W949 surface opens to W1442's six-input surface. -/
theorem w1442W1441UnpackExpandsToW948NormalizedSource :
    w1007W950NormalizedEndpointUnpackedInputNamesW1441.length <
      w1007W948NormalizedSourceUnpackedInputNamesW1442.length := by
  rw [w1007W950NormalizedEndpointUnpackedInputNamesW1441_count,
    w1007W948NormalizedSourceUnpackedInputNamesW1442_count]
  norm_num

/-- W1169's one-input branch-full-data surface opens to W1442's six-input surface. -/
theorem w1442W1169UnpackExpandsToW948NormalizedSource :
    branchFullDataInputNamesW1169.length <
      w1007W948NormalizedSourceUnpackedInputNamesW1442.length := by
  rw [branchFullDataInputNamesW1169_count,
    w1007W948NormalizedSourceUnpackedInputNamesW1442_count]
  norm_num

/-- Current W1442 nonterminal W948 normalized-source unpack state. -/
structure ClosedMapBranchFullDataW948NormalizedSourceUnpackBoundaryStateW1442 : Type where
  seed : String
  declarations : List String
  projectionResult : String
  unpackResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1442 records W1007's concrete W948 normalized-source unpack after W1441. -/
def currentClosedMapBranchFullDataW948NormalizedSourceUnpackBoundaryStateW1442 :
    ClosedMapBranchFullDataW948NormalizedSourceUnpackBoundaryStateW1442 where
  seed := "w1442-closed-map-branch-full-data-w948-normalized-source-unpack-boundary"
  declarations :=
    ["w1007RepackedW948ComponentIsW948W1442",
      "w1007W985NormalizedSourceComponentRunsThroughW948W1442",
      "w1007W948NormalizedFixedTargetRunsThroughW1442",
      "w1007W948SourceTriangulationRunsThroughW1442",
      "w1442BranchFullDataUnpackedW730W944W973W719W722W949InputCount",
      "w1442W948NormalizedSourceInnerInputCount",
      "w1442W1441UnpackExpandsToW948NormalizedSource",
      "w1442W1169UnpackExpandsToW948NormalizedSource"]
  projectionResult :=
    "proved: W1007's W948 component projects to W719 normalized fixed-target\
      data and W722 source-triangulation data, and W985 receives those fields"
  unpackResult :=
    "proved: unpacking the W1441 W730/W944/W973/W948/W949 surface exposes the\
      W1442 six-input W730/W944/W973/W719/W722/W949 surface, so this remains\
      nonterminal"
  remainingInputs := w1007W948NormalizedSourceUnpackedInputNamesW1442
  productSuccessClaimed := false

theorem currentW1442ClosedMapBranchFullDataW948NormalizedSourceUnpackBoundary_productSuccess :
    currentClosedMapBranchFullDataW948NormalizedSourceUnpackBoundaryStateW1442.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
