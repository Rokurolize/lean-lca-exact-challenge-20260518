import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataNormalizedEndpointBoundaryUnpackGuardW1302

/-!
W1303 records the W948 normalized-source-triangulation provider boundary behind
W1302. Unpacking W948 exposes W719 normalized fixed-target data and W722
source-triangulation data, and the primitive W948 route expands to a five-input
surface. Neither closes the remaining W987 obligation.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def canonicalW948NormalizedSourceTriangulationInnerInputNamesW1303 :
    List String :=
  ["W719 normalized fixed-target data provider",
    "W722 source-triangulation data provider"]

theorem canonicalW948NormalizedSourceTriangulationInnerInputNamesW1303_count :
    canonicalW948NormalizedSourceTriangulationInnerInputNamesW1303.length = 2 :=
  rfl

def canonicalW948NormalizedSourceTriangulationPrimitiveInputNamesW1303 :
    List String :=
  closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsInputNamesW948

theorem canonicalW948NormalizedSourceTriangulationPrimitiveInputNamesW1303_count :
    canonicalW948NormalizedSourceTriangulationPrimitiveInputNamesW1303.length = 5 :=
  closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsInputNamesW948_count

theorem canonicalW948NormalizedSourceTriangulationInnerUnpackExpandsCurrentSurfaceW1303 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW948NormalizedSourceTriangulationInnerInputNamesW1303.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW948NormalizedSourceTriangulationInnerInputNamesW1303_count]
  norm_num

theorem canonicalW948NormalizedSourceTriangulationPrimitiveRouteExpandsCurrentSurfaceW1303 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW948NormalizedSourceTriangulationPrimitiveInputNamesW1303.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW948NormalizedSourceTriangulationPrimitiveInputNamesW1303_count]
  norm_num

def repackNormalizedSourceTriangulationDataW1303
    (normalizedSourceTriangulationData :
      NormalizedFixedTargetSourceTriangulationDataProviderW948) :
    NormalizedFixedTargetSourceTriangulationDataProviderW948
    where
  normalizedFixedTargetData :=
    normalizedFixedTargetDataOfNormalizedSourceTriangulationDataW948
      normalizedSourceTriangulationData
  sourceTriangulationData :=
    sourceTriangulationDataOfNormalizedSourceTriangulationDataW948
      normalizedSourceTriangulationData

theorem repackNormalizedSourceTriangulationDataW1303_eq
    (normalizedSourceTriangulationData :
      NormalizedFixedTargetSourceTriangulationDataProviderW948) :
    repackNormalizedSourceTriangulationDataW1303
        normalizedSourceTriangulationData =
      normalizedSourceTriangulationData := by
  cases normalizedSourceTriangulationData
  rfl

theorem w947LeavesNormalizedFixedTargetOfW948LeavesW1303
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldLeavesW948) :
    (w947LeavesOfNormalizedSourceTriangulationDataBoundaryRelationDataTargetNoUnivClosednessDataEndpointStrictExactLocalizedUnitDataFieldsW948
        leaves).normalizedFixedTargetData =
      normalizedFixedTargetDataOfNormalizedSourceTriangulationDataW948
        leaves.normalizedSourceTriangulationData :=
  rfl

theorem w947LeavesSourceTriangulationOfW948LeavesW1303
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldLeavesW948) :
    (w947LeavesOfNormalizedSourceTriangulationDataBoundaryRelationDataTargetNoUnivClosednessDataEndpointStrictExactLocalizedUnitDataFieldsW948
        leaves).sourceTriangulationData =
      sourceTriangulationDataOfNormalizedSourceTriangulationDataW948
        leaves.normalizedSourceTriangulationData :=
  rfl

structure MetrizableNormalizedSourceTriangulationBoundaryUnpackGuardStateW1303 :
    Type where
  seed : String
  inspectedBoundary : String
  innerSurfaceCount : Nat
  primitiveRouteSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableNormalizedSourceTriangulationBoundaryUnpackGuardStateW1303 :
    MetrizableNormalizedSourceTriangulationBoundaryUnpackGuardStateW1303 where
  seed := "w1303-normalized-source-triangulation-boundary-unpack-guard"
  inspectedBoundary :=
    "W948 canonical projections to W719 normalized fixed-target data and W722\
      source-triangulation data"
  innerSurfaceCount :=
    canonicalW948NormalizedSourceTriangulationInnerInputNamesW1303.length
  primitiveRouteSurfaceCount :=
    canonicalW948NormalizedSourceTriangulationPrimitiveInputNamesW1303.length
  providerSearchResult :=
    "proved: canonical W948 normalized-source-triangulation unpacking exposes\
      a two-input provider boundary and a five-input primitive route; repacking\
      the W948 projections is the same provider, so this boundary does not\
      close the remaining W987 obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1303NormalizedSourceTriangulationBoundaryUnpackGuard_productSuccess :
    (let state :=
        currentMetrizableNormalizedSourceTriangulationBoundaryUnpackGuardStateW1303;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
