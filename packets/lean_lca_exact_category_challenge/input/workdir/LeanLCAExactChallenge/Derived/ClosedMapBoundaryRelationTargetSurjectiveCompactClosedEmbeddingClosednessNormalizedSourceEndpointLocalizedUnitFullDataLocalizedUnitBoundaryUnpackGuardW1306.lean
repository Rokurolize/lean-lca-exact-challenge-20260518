import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataBoundaryRelationBoundaryUnpackGuardW1305

/-!
W1306 records the W945 localized-unit provider boundary. Unpacking W945 exposes
the localized right adjoint, localized adjunction, and W939 unit-component
witness; the W945 primitive route expands to eight inputs, so this boundary
does not close the remaining W987 obligation.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def canonicalW945LocalizedUnitInnerInputNamesW1306 : List String :=
  ["bounded homotopy localized right adjoint",
    "bounded homotopy localized adjunction",
    "W939 unit mapping-cone strict-exact component witness"]

theorem canonicalW945LocalizedUnitInnerInputNamesW1306_count :
    canonicalW945LocalizedUnitInnerInputNamesW1306.length = 3 :=
  rfl

def canonicalW945LocalizedUnitPrimitiveInputNamesW1306 : List String :=
  closedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsInputNamesW945

theorem canonicalW945LocalizedUnitPrimitiveInputNamesW1306_count :
    canonicalW945LocalizedUnitPrimitiveInputNamesW1306.length = 8 :=
  closedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsInputNamesW945_count

theorem canonicalW945LocalizedUnitInnerUnpackExpandsCurrentSurfaceW1306 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW945LocalizedUnitInnerInputNamesW1306.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW945LocalizedUnitInnerInputNamesW1306_count]
  norm_num

theorem canonicalW945LocalizedUnitPrimitiveRouteExpandsCurrentSurfaceW1306 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW945LocalizedUnitPrimitiveInputNamesW1306.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW945LocalizedUnitPrimitiveInputNamesW1306_count]
  norm_num

def repackLocalizedUnitDataW1306
    (localizedUnitData :
      BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945) :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945
    where
  boundedHomotopyLocalizedRightAdjoint :=
    boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
      localizedUnitData
  boundedHomotopyLocalizedAdjunction :=
    boundedHomotopyLocalizedAdjunctionOfLocalizedUnitDataW945
      localizedUnitData
  boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents :=
    boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponentsOfLocalizedUnitDataW945
      localizedUnitData

theorem repackLocalizedUnitDataW1306_eq
    (localizedUnitData :
      BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945) :
    repackLocalizedUnitDataW1306 localizedUnitData =
      localizedUnitData := by
  cases localizedUnitData
  rfl

theorem w981LocalizedAdjunctionOfW982FullDataW1306
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    (fullDataOfLocalizedUnitChoiceW982 fullData).localizedAdjunctionData =
      localizedAdjunctionDataOfLocalizedUnitDataW982
        fullData.localizedUnitData :=
  rfl

theorem w981UnitStrictExactIsoDataOfW982FullDataW1306
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    (fullDataOfLocalizedUnitChoiceW982 fullData).unitStrictExactIsoData =
      unitStrictExactIsoDataOfLocalizedUnitDataW982
        fullData.localizedUnitData :=
  rfl

theorem w944LeavesLocalizedRightAdjointOfW945LeavesW1306
    (leaves :
      MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW945) :
    (w944LeavesOfLocalizedUnitDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactFieldsW945
        leaves).boundedHomotopyLocalizedRightAdjoint =
      boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
        leaves.localizedUnitData :=
  rfl

theorem w944LeavesLocalizedAdjunctionOfW945LeavesW1306
    (leaves :
      MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW945) :
    (w944LeavesOfLocalizedUnitDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactFieldsW945
        leaves).boundedHomotopyLocalizedAdjunction =
      boundedHomotopyLocalizedAdjunctionOfLocalizedUnitDataW945
        leaves.localizedUnitData :=
  rfl

theorem w944LeavesUnitComponentsOfW945LeavesW1306
    (leaves :
      MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW945) :
    (w944LeavesOfLocalizedUnitDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactFieldsW945
        leaves).boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents =
      boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponentsOfLocalizedUnitDataW945
        leaves.localizedUnitData :=
  rfl

structure MetrizableLocalizedUnitBoundaryUnpackGuardStateW1306 : Type where
  seed : String
  inspectedBoundary : String
  innerSurfaceCount : Nat
  primitiveRouteSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableLocalizedUnitBoundaryUnpackGuardStateW1306 :
    MetrizableLocalizedUnitBoundaryUnpackGuardStateW1306 where
  seed := "w1306-localized-unit-boundary-unpack-guard"
  inspectedBoundary :=
    "W945 canonical projections to localized right adjoint, localized\
      adjunction, and W939 unit-component witness"
  innerSurfaceCount :=
    canonicalW945LocalizedUnitInnerInputNamesW1306.length
  primitiveRouteSurfaceCount :=
    canonicalW945LocalizedUnitPrimitiveInputNamesW1306.length
  providerSearchResult :=
    "proved: canonical W945 localized-unit unpacking exposes a three-input\
      provider boundary and an eight-input primitive route; repacking W945\
      projections is the same provider, so this boundary does not close the\
      remaining W987 obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1306LocalizedUnitBoundaryUnpackGuard_productSuccess :
    (let state :=
        currentMetrizableLocalizedUnitBoundaryUnpackGuardStateW1306;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
