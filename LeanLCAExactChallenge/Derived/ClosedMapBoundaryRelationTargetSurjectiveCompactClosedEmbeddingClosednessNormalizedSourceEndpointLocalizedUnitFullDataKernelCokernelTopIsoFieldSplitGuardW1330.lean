import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataPrimitiveUnitComponentsFieldSplitGuardW1329
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromKernelCokernelTopIsoComponentFieldsRoute

/-!
W1330 supplements the existing W1319 W991 guard by recording additional
field-split equalities from endpoint kernel/cokernel-top and unit
kernel/cokernel-top/isomorphism component fields into the W990 primitive
unit-components provider. The route still exposes W991's thirteen inputs and
therefore does not close the current one-input W987 obligation.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def canonicalW991KernelCokernelTopIsoFieldSplitInputNamesW1330 :
    List String :=
  kernelCokernelTopIsoComponentFieldsInputNamesW991

theorem canonicalW991KernelCokernelTopIsoFieldSplitInputNamesW1330_count :
    canonicalW991KernelCokernelTopIsoFieldSplitInputNamesW1330.length = 13 :=
  kernelCokernelTopIsoComponentFieldsInputNamesW991_count

theorem canonicalW991KernelCokernelTopIsoFieldSplitExpandsCurrentSurfaceW1330 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW991KernelCokernelTopIsoFieldSplitInputNamesW1330.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW991KernelCokernelTopIsoFieldSplitInputNamesW1330_count]
  norm_num

theorem w991PrimitiveUnitDataKeepsTargetNoUnivW1330
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    (primitiveUnitComponentsDataOfKernelCokernelTopIsoComponentFieldsW991
        leaves).targetNoUnivData =
      leaves.targetNoUnivData :=
  rfl

theorem w991PrimitiveUnitDataKeepsClosednessW1330
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    (primitiveUnitComponentsDataOfKernelCokernelTopIsoComponentFieldsW991
        leaves).closedEmbeddingClosednessData =
      leaves.closedEmbeddingClosednessData :=
  rfl

theorem w991PrimitiveUnitDataKeepsLocalizedRightAdjointW1330
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    (primitiveUnitComponentsDataOfKernelCokernelTopIsoComponentFieldsW991
        leaves).boundedHomotopyLocalizedRightAdjoint =
      leaves.boundedHomotopyLocalizedRightAdjoint :=
  rfl

theorem w991PrimitiveUnitDataKeepsLocalizedAdjunctionW1330
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    (primitiveUnitComponentsDataOfKernelCokernelTopIsoComponentFieldsW991
        leaves).boundedHomotopyLocalizedAdjunction =
      leaves.boundedHomotopyLocalizedAdjunction :=
  rfl

theorem w991PrimitiveUnitDataKeepsNormalizedSourceW1330
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    (primitiveUnitComponentsDataOfKernelCokernelTopIsoComponentFieldsW991
        leaves).normalizedSourceTriangulationData =
      leaves.normalizedSourceTriangulationData :=
  rfl

theorem w991UnitComponentsUseKernelCokernelTopFieldsW1330
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    unitComponentsOfKernelCokernelTopIsoComponentFieldsW991 leaves =
      fun X =>
        ⟨leaves.unitMappingConeModel X,
          leaves.unitMappingConeClosedEmbedding X,
          leaves.unitMappingConeOpenMap X,
          fun i =>
            MetrizableLCA.surjective_of_cokernelSubgroup_eq_top_of_isOpenMap
              (((leaves.unitMappingConeModel X).as.sc i).g)
              (leaves.unitMappingConeCokernelTop X i)
              (leaves.unitMappingConeOpenMap X i),
          fun i x₂ hx₂ => (leaves.unitMappingConeKernelEquality X i x₂).mp hx₂,
          ⟨leaves.unitMappingConeIso X⟩⟩ :=
  rfl

structure MetrizableKernelCokernelTopIsoFieldSplitGuardStateW1330 : Type where
  seed : String
  inspectedBoundary : String
  routeSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableKernelCokernelTopIsoFieldSplitGuardStateW1330 :
    MetrizableKernelCokernelTopIsoFieldSplitGuardStateW1330 where
  seed := "w1330-kernel-cokernel-top-iso-field-split-guard"
  inspectedBoundary :=
    "W991 field split from endpoint kernel/cokernel-top data and unit\
      kernel/cokernel-top/isomorphism component fields into W990 primitive\
      unit-components data"
  routeSurfaceCount :=
    canonicalW991KernelCokernelTopIsoFieldSplitInputNamesW1330.length
  providerSearchResult :=
    "proved: W991 preserves target no-univ, closedness, localized right\
      adjoint, localized adjunction, normalized-source, and the constructed\
      unit component witness while rebuilding W990, but its route surface still\
      has thirteen inputs and expands the current one-input W987 obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1330KernelCokernelTopIsoFieldSplitGuard_productSuccess :
    (let state :=
        currentMetrizableKernelCokernelTopIsoFieldSplitGuardStateW1330;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
