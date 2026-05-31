import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosedMapBranchFullDataW986UnpackBoundaryGuardW1439
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataTargetClosednessBoundaryUnpackGuardW1300

/-!
W1440 connects the W984 target/closedness component exposed by W1439 to the
canonical W1300 unpack. The W1007 branch-full-data route therefore exposes the
W730 boundary/relation provider, W944 target no-univ data, W973
closed-embedding closedness data, and W950 normalized-source/endpoint data.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def w1007W985TargetClosednessUnpackedInputNamesW1440 : List String :=
  ["W730 boundary/relation data provider",
    "W944 target no-univ data provider",
    "W973 closed-embedding closedness data provider",
    "W950 normalized-source/endpoint-localized-unit data provider"]

theorem w1007W985TargetClosednessUnpackedInputNamesW1440_count :
    w1007W985TargetClosednessUnpackedInputNamesW1440.length = 4 :=
  rfl

/-- Repacking W1007's W984 component through W1300 returns the same W984 component. -/
theorem w1007RepackedW984ComponentIsW984W1440
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    repackTargetClosedEmbeddingClosednessDataW1300
        (targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
          (targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007
            branchFullData)) =
      targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
        (targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007
          branchFullData) :=
  repackTargetClosedEmbeddingClosednessDataW1300_eq
    (targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
      (targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007
        branchFullData))

/-- W1007's W985 surface feeds W984 with the W984 target/closedness component. -/
theorem w1007W985TargetClosednessComponentRunsThroughW984W1440
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (fullDataOfNormalizedSourceEndpointLocalizedUnitW985
        (fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
          (w986FullDataOfFullDataW987
            (branchFullDataInputOfBranchFullDataW1007
              branchFullData)))).targetClosedEmbeddingClosednessData =
      targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
        (targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007
          branchFullData) :=
  rfl

/-- The W984 full-data route over W1007's W985 surface keeps the W944 target field. -/
theorem w1007W984TargetNoUnivRunsThroughW1440
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (fullDataOfTargetClosedEmbeddingClosednessW984
        (fullDataOfNormalizedSourceEndpointLocalizedUnitW985
          (fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
            (w986FullDataOfFullDataW987
              (branchFullDataInputOfBranchFullDataW1007
                branchFullData))))).targetNoUnivData =
      targetNoUnivDataOfTargetClosedEmbeddingClosednessDataW984
        (targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
          (targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007
            branchFullData)) :=
  rfl

/-- The W984 full-data route over W1007's W985 surface keeps the W973 closedness field. -/
theorem w1007W984ClosedEmbeddingClosednessRunsThroughW1440
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (fullDataOfTargetClosedEmbeddingClosednessW984
        (fullDataOfNormalizedSourceEndpointLocalizedUnitW985
          (fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
            (w986FullDataOfFullDataW987
              (branchFullDataInputOfBranchFullDataW1007
                branchFullData))))).closedEmbeddingClosednessData =
      closedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessDataW984
        (targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
          (targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007
            branchFullData)) :=
  rfl

/-- W1440 exposes the four inputs obtained by unpacking W1439's W984 component. -/
theorem w1440BranchFullDataUnpackedW730W944W973W950InputCount :
    w1007W985TargetClosednessUnpackedInputNamesW1440.length = 4 :=
  w1007W985TargetClosednessUnpackedInputNamesW1440_count

/-- W1300 records the two internal W984 target/closedness inputs. -/
theorem w1440W984TargetClosednessInnerInputCount :
    canonicalW984TargetClosednessUnpackedInputNamesW1300.length = 2 :=
  canonicalW984TargetClosednessUnpackedInputNamesW1300_count

/-- W1439's three-input W730/W984/W950 surface opens to W1440's four-input surface. -/
theorem w1440W1299UnpackExpandsToW984TargetClosedness :
    canonicalW986InnerUnpackedInputNamesW1299.length <
      w1007W985TargetClosednessUnpackedInputNamesW1440.length := by
  rw [canonicalW986InnerUnpackedInputNamesW1299_count,
    w1007W985TargetClosednessUnpackedInputNamesW1440_count]
  norm_num

/-- W1169's one-input branch-full-data surface opens to W1440's four-input surface. -/
theorem w1440W1169UnpackExpandsToW984TargetClosedness :
    branchFullDataInputNamesW1169.length <
      w1007W985TargetClosednessUnpackedInputNamesW1440.length := by
  rw [branchFullDataInputNamesW1169_count,
    w1007W985TargetClosednessUnpackedInputNamesW1440_count]
  norm_num

/-- Current W1440 nonterminal W984 target/closedness unpack state. -/
structure ClosedMapBranchFullDataW984TargetClosednessUnpackBoundaryStateW1440 : Type where
  seed : String
  declarations : List String
  projectionResult : String
  unpackResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1440 records W1007's concrete W984 target/closedness unpack after W1439. -/
def currentClosedMapBranchFullDataW984TargetClosednessUnpackBoundaryStateW1440 :
    ClosedMapBranchFullDataW984TargetClosednessUnpackBoundaryStateW1440 where
  seed := "w1440-closed-map-branch-full-data-w984-target-closedness-unpack-boundary"
  declarations :=
    ["w1007RepackedW984ComponentIsW984W1440",
      "w1007W985TargetClosednessComponentRunsThroughW984W1440",
      "w1007W984TargetNoUnivRunsThroughW1440",
      "w1007W984ClosedEmbeddingClosednessRunsThroughW1440",
      "w1440BranchFullDataUnpackedW730W944W973W950InputCount",
      "w1440W984TargetClosednessInnerInputCount",
      "w1440W1299UnpackExpandsToW984TargetClosedness",
      "w1440W1169UnpackExpandsToW984TargetClosedness"]
  projectionResult :=
    "proved: W1007's W984 component projects to W944 target no-univ data and\
      W973 closed-embedding closedness data, and W984 receives those fields"
  unpackResult :=
    "proved: unpacking the W1439 W730/W984/W950 surface exposes the W1440\
      four-input W730/W944/W973/W950 surface, so this remains nonterminal"
  remainingInputs := w1007W985TargetClosednessUnpackedInputNamesW1440
  productSuccessClaimed := false

theorem currentW1440ClosedMapBranchFullDataW984TargetClosednessUnpackBoundary_productSuccess :
    currentClosedMapBranchFullDataW984TargetClosednessUnpackBoundaryStateW1440.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
