import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataEndpointStrictExactBoundaryGuardW1312
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitFullDataToComponentFieldsRoute

/-!
W1313 records the W979 split/rebuild cycle around the W977 full-data provider.
W979 has the same one-input provider surface as the current W1270 obligation,
and the W978 component-field reconstruction expands to eighteen inputs.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def canonicalW979SplitFullDataInputNamesW1313 : List String :=
  fullDataToComponentFieldsInputNamesW979

theorem canonicalW979SplitFullDataInputNamesW1313_count :
    canonicalW979SplitFullDataInputNamesW1313.length = 1 :=
  fullDataToComponentFieldsInputNamesW979_count

def canonicalW978ComponentFieldRouteInputNamesW1313 : List String :=
  closedEmbeddingEndpointLocalizedUnitFullDataFromComponentFieldsInputNamesW978

theorem canonicalW978ComponentFieldRouteInputNamesW1313_count :
    canonicalW978ComponentFieldRouteInputNamesW1313.length = 18 :=
  closedEmbeddingEndpointLocalizedUnitFullDataFromComponentFieldsInputNamesW978_count

theorem canonicalW979SplitFullDataKeepsCurrentSurfaceW1313 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length =
      canonicalW979SplitFullDataInputNamesW1313.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW979SplitFullDataInputNamesW1313_count]

theorem canonicalW978ComponentFieldRouteExpandsCurrentSurfaceW1313 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW978ComponentFieldRouteInputNamesW1313.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW978ComponentFieldRouteInputNamesW1313_count]
  norm_num

theorem splitFullDataRebuildUsesComponentFieldsW1313
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    fullDataFromSplitComponentFieldsW979 fullData =
      fullDataOfComponentFieldsW978 (componentFieldsOfFullDataW979 fullData) :=
  rfl

theorem splitFullDataLeavesCarryRebuiltProviderW1313
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    (w977LeavesOfSplitFullDataW979 fullData).fullData =
      fullDataFromSplitComponentFieldsW979 fullData :=
  rfl

theorem splitFullDataComponentFieldsBoundaryRelationW1313
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    (componentFieldsOfFullDataW979 fullData).boundaryRelationData =
      boundaryRelationDataOfFullDataW977 fullData :=
  rfl

theorem splitFullDataComponentFieldsUnitModelW1313
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    (componentFieldsOfFullDataW979 fullData).unitMappingConeModel =
      unitMappingConeModelOfUnitKernelCokernelTopIsoDataW976
        (unitKernelCokernelTopIsoDataOfFullDataW977 fullData) :=
  rfl

structure MetrizableSplitFullDataCycleGuardStateW1313 : Type where
  seed : String
  inspectedBoundary : String
  splitSurfaceCount : Nat
  componentRouteCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableSplitFullDataCycleGuardStateW1313 :
    MetrizableSplitFullDataCycleGuardStateW1313 where
  seed := "w1313-split-full-data-cycle-guard"
  inspectedBoundary :=
    "W979 split of W977 full-data provider into W971 component fields and\
      rebuild through W978"
  splitSurfaceCount := canonicalW979SplitFullDataInputNamesW1313.length
  componentRouteCount :=
    canonicalW978ComponentFieldRouteInputNamesW1313.length
  providerSearchResult :=
    "proved: W979 keeps the one-input W977 provider surface and rebuilds it\
      through W978, while W978 expands to the eighteen-input W971 component\
      field surface; this same-size cycle does not close the remaining W987\
      obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1313SplitFullDataCycleGuard_productSuccess :
    (let state :=
        currentMetrizableSplitFullDataCycleGuardStateW1313;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
