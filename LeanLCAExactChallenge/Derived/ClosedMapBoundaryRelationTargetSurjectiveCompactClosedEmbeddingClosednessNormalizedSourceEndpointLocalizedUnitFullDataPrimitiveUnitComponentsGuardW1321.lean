import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataTargetSurjectiveCompactKernelCokernelTopIsoComponentFieldsGuardW1320
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromPrimitiveUnitComponentsRoute

/-!
W1321 records the W990 primitive unit-components route. W990 constructs the
W975 localized-adjunction data and W981 unit strict-exact/isomorphism data from
explicit localized adjunction fields plus the W939 unit-component witness, but
the route surface has eight inputs and expands the current one-input W987
obligation.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def canonicalW990PrimitiveUnitComponentsInputNamesW1321 : List String :=
  primitiveUnitComponentsInputNamesW990

theorem canonicalW990PrimitiveUnitComponentsInputNamesW1321_count :
    canonicalW990PrimitiveUnitComponentsInputNamesW1321.length = 8 :=
  primitiveUnitComponentsInputNamesW990_count

theorem canonicalW990PrimitiveUnitComponentsRouteExpandsCurrentSurfaceW1321 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW990PrimitiveUnitComponentsInputNamesW1321.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW990PrimitiveUnitComponentsInputNamesW1321_count]
  norm_num

theorem w990LocalizedAdjunctionKeepsRightAdjointW1321
    (primitiveData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactPrimitiveUnitComponentsDataProviderW990) :
    (localizedAdjunctionDataOfPrimitiveUnitComponentsW990
        primitiveData).boundedHomotopyLocalizedRightAdjoint =
      primitiveData.boundedHomotopyLocalizedRightAdjoint :=
  rfl

theorem w990LocalizedAdjunctionKeepsAdjunctionW1321
    (primitiveData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactPrimitiveUnitComponentsDataProviderW990) :
    (localizedAdjunctionDataOfPrimitiveUnitComponentsW990
        primitiveData).boundedHomotopyLocalizedAdjunction =
      primitiveData.boundedHomotopyLocalizedAdjunction :=
  rfl

theorem w990FullDataKeepsBoundaryRelationW1321
    (primitiveData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactPrimitiveUnitComponentsDataProviderW990) :
    (unitStrictExactIsoFullDataOfPrimitiveUnitComponentsW990
        primitiveData).boundaryRelationData =
      primitiveData.boundaryRelationData :=
  rfl

theorem w990FullDataRunsThroughW989W1321
    (primitiveData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactPrimitiveUnitComponentsDataProviderW990) :
    fullDataOfPrimitiveUnitComponentsW990 primitiveData =
      fullDataOfUnitStrictExactIsoW989
        (unitStrictExactIsoFullDataOfPrimitiveUnitComponentsW990
          primitiveData) :=
  rfl

structure MetrizablePrimitiveUnitComponentsGuardStateW1321 : Type where
  seed : String
  inspectedBoundary : String
  routeSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizablePrimitiveUnitComponentsGuardStateW1321 :
    MetrizablePrimitiveUnitComponentsGuardStateW1321 where
  seed := "w1321-primitive-unit-components-guard"
  inspectedBoundary :=
    "W990 construction of W975 localized-adjunction data and W981 unit\
      strict-exact/isomorphism data from explicit primitive unit components"
  routeSurfaceCount := canonicalW990PrimitiveUnitComponentsInputNamesW1321.length
  providerSearchResult :=
    "proved: W990 reconstructs W975 and W981 before delegating through W989,\
      but its route surface has eight inputs and expands the current one-input\
      W987 obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1321PrimitiveUnitComponentsGuard_productSuccess :
    (let state :=
        currentMetrizablePrimitiveUnitComponentsGuardStateW1321;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
