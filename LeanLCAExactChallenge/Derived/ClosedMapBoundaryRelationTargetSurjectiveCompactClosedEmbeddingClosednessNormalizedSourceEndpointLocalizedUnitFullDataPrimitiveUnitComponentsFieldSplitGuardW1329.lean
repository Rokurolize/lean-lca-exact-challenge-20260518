import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataUnitStrictExactIsoFieldSplitGuardW1328
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromPrimitiveUnitComponentsRoute

/-!
W1329 supplements the existing W1321 W990 guard by recording the remaining
field-split equalities from primitive unit components into the W981
unit strict-exact/isomorphism full-data provider. The route still exposes
W990's eight primitive inputs and therefore does not close the current
one-input W987 obligation.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def canonicalW990PrimitiveUnitComponentsFieldSplitInputNamesW1329 :
    List String :=
  primitiveUnitComponentsInputNamesW990

theorem canonicalW990PrimitiveUnitComponentsFieldSplitInputNamesW1329_count :
    canonicalW990PrimitiveUnitComponentsFieldSplitInputNamesW1329.length = 8 :=
  primitiveUnitComponentsInputNamesW990_count

theorem canonicalW990PrimitiveUnitComponentsFieldSplitExpandsCurrentSurfaceW1329 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW990PrimitiveUnitComponentsFieldSplitInputNamesW1329.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW990PrimitiveUnitComponentsFieldSplitInputNamesW1329_count]
  norm_num

theorem w990FullDataKeepsTargetNoUnivW1329
    (primitiveData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactPrimitiveUnitComponentsDataProviderW990) :
    (unitStrictExactIsoFullDataOfPrimitiveUnitComponentsW990
        primitiveData).targetNoUnivData =
      primitiveData.targetNoUnivData :=
  rfl

theorem w990FullDataKeepsClosednessW1329
    (primitiveData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactPrimitiveUnitComponentsDataProviderW990) :
    (unitStrictExactIsoFullDataOfPrimitiveUnitComponentsW990
        primitiveData).closedEmbeddingClosednessData =
      primitiveData.closedEmbeddingClosednessData :=
  rfl

theorem w990FullDataKeepsEndpointStrictExactW1329
    (primitiveData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactPrimitiveUnitComponentsDataProviderW990) :
    (unitStrictExactIsoFullDataOfPrimitiveUnitComponentsW990
        primitiveData).endpointStrictExact =
      primitiveData.endpointStrictExact :=
  rfl

theorem w990FullDataUsesLocalizedAdjunctionDataW1329
    (primitiveData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactPrimitiveUnitComponentsDataProviderW990) :
    (unitStrictExactIsoFullDataOfPrimitiveUnitComponentsW990
        primitiveData).localizedAdjunctionData =
      localizedAdjunctionDataOfPrimitiveUnitComponentsW990 primitiveData :=
  rfl

theorem w990FullDataKeepsNormalizedSourceW1329
    (primitiveData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactPrimitiveUnitComponentsDataProviderW990) :
    (unitStrictExactIsoFullDataOfPrimitiveUnitComponentsW990
        primitiveData).normalizedSourceTriangulationData =
      primitiveData.normalizedSourceTriangulationData :=
  rfl

theorem w990FullDataUsesUnitStrictExactIsoDataW1329
    (primitiveData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactPrimitiveUnitComponentsDataProviderW990) :
    (unitStrictExactIsoFullDataOfPrimitiveUnitComponentsW990
        primitiveData).unitStrictExactIsoData =
      unitStrictExactIsoDataOfPrimitiveUnitComponentsW990 primitiveData :=
  rfl

theorem w990UnitStrictExactIsoModelChoosesPrimitiveWitnessW1329
    (primitiveData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactPrimitiveUnitComponentsDataProviderW990)
    (X : BoundedComplexCategory MetrizableLCA.{0}) :
    (unitStrictExactIsoDataOfPrimitiveUnitComponentsW990
        primitiveData).unitMappingConeModel X =
      Classical.choose
        (primitiveData.boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents
          X) :=
  rfl

structure MetrizablePrimitiveUnitComponentsFieldSplitGuardStateW1329 : Type where
  seed : String
  inspectedBoundary : String
  routeSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizablePrimitiveUnitComponentsFieldSplitGuardStateW1329 :
    MetrizablePrimitiveUnitComponentsFieldSplitGuardStateW1329 where
  seed := "w1329-primitive-unit-components-field-split-guard"
  inspectedBoundary :=
    "W990 field split from primitive unit components into W975 localized\
      adjunction data and W981 unit strict-exact/isomorphism data"
  routeSurfaceCount :=
    canonicalW990PrimitiveUnitComponentsFieldSplitInputNamesW1329.length
  providerSearchResult :=
    "proved: W990 preserves target no-univ, closedness, endpoint strict\
      exactness, localized-adjunction data, normalized-source, unit\
      strict-exact/isomorphism data, and the chosen unit mapping-cone model,\
      but its route surface still has eight inputs and expands the current\
      one-input W987 obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1329PrimitiveUnitComponentsFieldSplitGuard_productSuccess :
    (let state :=
        currentMetrizablePrimitiveUnitComponentsFieldSplitGuardStateW1329;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
