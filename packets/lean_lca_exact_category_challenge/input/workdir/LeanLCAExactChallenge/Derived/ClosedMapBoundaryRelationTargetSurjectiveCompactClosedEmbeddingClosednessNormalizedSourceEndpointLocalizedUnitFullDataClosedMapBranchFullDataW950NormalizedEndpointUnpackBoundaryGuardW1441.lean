import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosedMapBranchFullDataW984TargetClosednessUnpackBoundaryGuardW1440
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataNormalizedEndpointBoundaryUnpackGuardW1302

/-!
W1441 connects the W950 normalized-source/endpoint component exposed by W1440
to the canonical W1302 unpack. The W1007 branch-full-data route therefore
exposes the W730 boundary/relation provider, W944 target no-univ data, W973
closed-embedding closedness data, W948 normalized-source-triangulation data,
and W949 endpoint-localized-unit data.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def w1007W950NormalizedEndpointUnpackedInputNamesW1441 : List String :=
  ["W730 boundary/relation data provider",
    "W944 target no-univ data provider",
    "W973 closed-embedding closedness data provider",
    "W948 normalized-source-triangulation data provider",
    "W949 endpoint-localized-unit data provider"]

theorem w1007W950NormalizedEndpointUnpackedInputNamesW1441_count :
    w1007W950NormalizedEndpointUnpackedInputNamesW1441.length = 5 :=
  rfl

/-- Repacking W1007's W950 component through W1302 returns the same W950 component. -/
theorem w1007RepackedW950ComponentIsW950W1441
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    repackNormalizedSourceEndpointLocalizedUnitDataW1302
        (normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007
          branchFullData) =
      normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007 branchFullData :=
  repackNormalizedSourceEndpointLocalizedUnitDataW1302_eq
    (normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007 branchFullData)

/-- W1007's W985 surface feeds W984 with the W950 normalized-source/endpoint component. -/
theorem w1007W985NormalizedEndpointComponentRunsThroughW950W1441
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
        (w986FullDataOfFullDataW987
          (branchFullDataInputOfBranchFullDataW1007
            branchFullData))).normalizedSourceEndpointLocalizedUnitData =
      normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007 branchFullData :=
  rfl

/-- The W985 route over W1007's W950 component keeps the W948 normalized-source field. -/
theorem w1007W950NormalizedSourceTriangulationRunsThroughW1441
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

/-- The W985 route over W1007's W950 component keeps the W949 endpoint-localized field. -/
theorem w1007W950EndpointLocalizedUnitRunsThroughW1441
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (fullDataOfNormalizedSourceEndpointLocalizedUnitW985
        (fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
          (w986FullDataOfFullDataW987
            (branchFullDataInputOfBranchFullDataW1007
              branchFullData)))).endpointLocalizedUnitData =
      endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitDataW950
        (normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007 branchFullData) :=
  rfl

/-- W1441 exposes the five inputs obtained by unpacking W1440's W950 component. -/
theorem w1441BranchFullDataUnpackedW730W944W973W948W949InputCount :
    w1007W950NormalizedEndpointUnpackedInputNamesW1441.length = 5 :=
  w1007W950NormalizedEndpointUnpackedInputNamesW1441_count

/-- W1302 records the two internal W950 normalized-source/endpoint inputs. -/
theorem w1441W950NormalizedEndpointInnerInputCount :
    canonicalW950NormalizedEndpointInnerInputNamesW1302.length = 2 :=
  canonicalW950NormalizedEndpointInnerInputNamesW1302_count

/-- W1440's four-input W730/W944/W973/W950 surface opens to W1441's five-input surface. -/
theorem w1441W1440UnpackExpandsToW950NormalizedEndpoint :
    w1007W985TargetClosednessUnpackedInputNamesW1440.length <
      w1007W950NormalizedEndpointUnpackedInputNamesW1441.length := by
  rw [w1007W985TargetClosednessUnpackedInputNamesW1440_count,
    w1007W950NormalizedEndpointUnpackedInputNamesW1441_count]
  norm_num

/-- W1169's one-input branch-full-data surface opens to W1441's five-input surface. -/
theorem w1441W1169UnpackExpandsToW950NormalizedEndpoint :
    branchFullDataInputNamesW1169.length <
      w1007W950NormalizedEndpointUnpackedInputNamesW1441.length := by
  rw [branchFullDataInputNamesW1169_count,
    w1007W950NormalizedEndpointUnpackedInputNamesW1441_count]
  norm_num

/-- Current W1441 nonterminal W950 normalized-source/endpoint unpack state. -/
structure ClosedMapBranchFullDataW950NormalizedEndpointUnpackBoundaryStateW1441 : Type where
  seed : String
  declarations : List String
  projectionResult : String
  unpackResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1441 records W1007's concrete W950 normalized-source/endpoint unpack after W1440. -/
def currentClosedMapBranchFullDataW950NormalizedEndpointUnpackBoundaryStateW1441 :
    ClosedMapBranchFullDataW950NormalizedEndpointUnpackBoundaryStateW1441 where
  seed := "w1441-closed-map-branch-full-data-w950-normalized-endpoint-unpack-boundary"
  declarations :=
    ["w1007RepackedW950ComponentIsW950W1441",
      "w1007W985NormalizedEndpointComponentRunsThroughW950W1441",
      "w1007W950NormalizedSourceTriangulationRunsThroughW1441",
      "w1007W950EndpointLocalizedUnitRunsThroughW1441",
      "w1441BranchFullDataUnpackedW730W944W973W948W949InputCount",
      "w1441W950NormalizedEndpointInnerInputCount",
      "w1441W1440UnpackExpandsToW950NormalizedEndpoint",
      "w1441W1169UnpackExpandsToW950NormalizedEndpoint"]
  projectionResult :=
    "proved: W1007's W950 component projects to W948 normalized-source-\
      triangulation data and W949 endpoint-localized-unit data, and W985\
      receives those fields"
  unpackResult :=
    "proved: unpacking the W1440 W730/W944/W973/W950 surface exposes the W1441\
      five-input W730/W944/W973/W948/W949 surface, so this remains nonterminal"
  remainingInputs := w1007W950NormalizedEndpointUnpackedInputNamesW1441
  productSuccessClaimed := false

theorem currentW1441ClosedMapBranchFullDataW950NormalizedEndpointUnpackBoundary_productSuccess :
    currentClosedMapBranchFullDataW950NormalizedEndpointUnpackBoundaryStateW1441.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
