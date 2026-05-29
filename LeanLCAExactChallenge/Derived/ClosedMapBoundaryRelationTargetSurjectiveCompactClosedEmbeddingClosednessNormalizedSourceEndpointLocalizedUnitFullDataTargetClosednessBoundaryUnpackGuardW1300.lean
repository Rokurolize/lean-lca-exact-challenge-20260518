import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataInnerProviderBoundaryUnpackGuardW1299

/-!
W1300 records the W984 target/closedness provider boundary reached from W1299.
Unpacking W984 exposes W944 target no-univ data and W973 closed-embedding
closedness data; the surrounding W984 full-data route is the existing four-input
W983 surface and does not close the remaining W987 obligation.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def canonicalW984TargetClosednessUnpackedInputNamesW1300 : List String :=
  targetClosedEmbeddingClosednessDataInputNamesW984

theorem canonicalW984TargetClosednessUnpackedInputNamesW1300_count :
    canonicalW984TargetClosednessUnpackedInputNamesW1300.length = 2 :=
  targetClosedEmbeddingClosednessDataInputNamesW984_count

def canonicalW984FullDataUnpackedInputNamesW1300 : List String :=
  targetClosedEmbeddingClosednessEndpointLocalizedUnitChoiceFullDataInputNamesW984

theorem canonicalW984FullDataUnpackedInputNamesW1300_count :
    canonicalW984FullDataUnpackedInputNamesW1300.length = 4 :=
  targetClosedEmbeddingClosednessEndpointLocalizedUnitChoiceFullDataInputNamesW984_count

theorem canonicalW984TargetClosednessUnpackKeepsW986InnerSizeW1300 :
    canonicalW984TargetClosednessUnpackedInputNamesW1300.length =
      targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitInputNamesW986.length := by
  rw [canonicalW984TargetClosednessUnpackedInputNamesW1300_count,
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitInputNamesW986_count]

theorem canonicalW984FullDataUnpackExpandsW985SurfaceW1300 :
    normalizedSourceEndpointLocalizedUnitChoiceInputNamesW985.length <
      canonicalW984FullDataUnpackedInputNamesW1300.length := by
  rw [normalizedSourceEndpointLocalizedUnitChoiceInputNamesW985_count,
    canonicalW984FullDataUnpackedInputNamesW1300_count]
  norm_num

theorem canonicalW984FullDataUnpackExpandsCurrentSurfaceW1300 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW984FullDataUnpackedInputNamesW1300.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW984FullDataUnpackedInputNamesW1300_count]
  norm_num

def repackTargetClosedEmbeddingClosednessDataW1300
    (targetClosedEmbeddingClosednessData :
      TargetNoUnivClosedEmbeddingClosednessDataProviderW984) :
    TargetNoUnivClosedEmbeddingClosednessDataProviderW984
    where
  targetNoUnivData :=
    targetNoUnivDataOfTargetClosedEmbeddingClosednessDataW984
      targetClosedEmbeddingClosednessData
  closedEmbeddingClosednessData :=
    closedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessDataW984
      targetClosedEmbeddingClosednessData

theorem repackTargetClosedEmbeddingClosednessDataW1300_eq
    (targetClosedEmbeddingClosednessData :
      TargetNoUnivClosedEmbeddingClosednessDataProviderW984) :
    repackTargetClosedEmbeddingClosednessDataW1300
        targetClosedEmbeddingClosednessData =
      targetClosedEmbeddingClosednessData := by
  cases targetClosedEmbeddingClosednessData
  rfl

theorem w983FullDataTargetNoUnivOfW984FullDataW1300
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessEndpointLocalizedUnitChoiceDataProviderW984) :
    (fullDataOfTargetClosedEmbeddingClosednessW984 fullData).targetNoUnivData =
      targetNoUnivDataOfTargetClosedEmbeddingClosednessDataW984
        fullData.targetClosedEmbeddingClosednessData :=
  rfl

theorem w983FullDataClosedEmbeddingClosednessOfW984FullDataW1300
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessEndpointLocalizedUnitChoiceDataProviderW984) :
    (fullDataOfTargetClosedEmbeddingClosednessW984 fullData).closedEmbeddingClosednessData =
      closedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessDataW984
        fullData.targetClosedEmbeddingClosednessData :=
  rfl

structure MetrizableTargetClosednessBoundaryUnpackGuardStateW1300 : Type where
  seed : String
  inspectedBoundary : String
  unpackedSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetClosednessBoundaryUnpackGuardStateW1300 :
    MetrizableTargetClosednessBoundaryUnpackGuardStateW1300 where
  seed := "w1300-target-closedness-boundary-unpack-guard"
  inspectedBoundary :=
    "W984 canonical projections to W944 target no-univ data and W973\
      closed-embedding closedness data"
  unpackedSurfaceCount := canonicalW984FullDataUnpackedInputNamesW1300.length
  providerSearchResult :=
    "proved: canonical W984 target/closedness unpacking exposes the W983\
      four-input full-data surface, while repacking the W984 projections is the\
      same provider, so this boundary does not close the remaining W987\
      obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1300TargetClosednessBoundaryUnpackGuard_productSuccess :
    (let state :=
        currentMetrizableTargetClosednessBoundaryUnpackGuardStateW1300;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
