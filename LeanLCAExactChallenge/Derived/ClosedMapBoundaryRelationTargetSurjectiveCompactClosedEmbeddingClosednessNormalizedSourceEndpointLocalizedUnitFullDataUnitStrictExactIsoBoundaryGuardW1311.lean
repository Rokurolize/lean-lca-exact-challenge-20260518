import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataUnitMappingConeBoundaryUnpackGuardW1310
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataRoute

/-!
W1311 records the W981 unit strict-exact/isomorphism boundary. W981 replaces
the W976 unit mapping-cone kernel/cokernel-top provider by a model, strict
short exactness, and chosen isomorphism, but this remains a three-input unit
boundary and a seven-input full-data surface.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def canonicalW981UnitStrictExactIsoInnerInputNamesW1311 :
    List String :=
  unitStrictExactIsoDataInputNamesW981

theorem canonicalW981UnitStrictExactIsoInnerInputNamesW1311_count :
    canonicalW981UnitStrictExactIsoInnerInputNamesW1311.length = 3 :=
  unitStrictExactIsoDataInputNamesW981_count

def canonicalW981UnitStrictExactIsoRouteInputNamesW1311 :
    List String :=
  endpointUnitStrictExactLocalizedUnitFullDataInputNamesW981

theorem canonicalW981UnitStrictExactIsoRouteInputNamesW1311_count :
    canonicalW981UnitStrictExactIsoRouteInputNamesW1311.length = 7 :=
  endpointUnitStrictExactLocalizedUnitFullDataInputNamesW981_count

theorem canonicalW981UnitStrictExactIsoInnerExpandsCurrentSurfaceW1311 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW981UnitStrictExactIsoInnerInputNamesW1311.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW981UnitStrictExactIsoInnerInputNamesW1311_count]
  norm_num

theorem canonicalW981UnitStrictExactIsoRouteExpandsCurrentSurfaceW1311 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW981UnitStrictExactIsoRouteInputNamesW1311.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW981UnitStrictExactIsoRouteInputNamesW1311_count]
  norm_num

def repackUnitStrictExactIsoDataW1311
    {localizedAdjunctionData :
      BoundedHomotopyLocalizedAdjunctionDataProviderW975}
    (unitData :
      UnitMappingConeStrictExactIsoDataProviderW981 localizedAdjunctionData) :
    UnitMappingConeStrictExactIsoDataProviderW981 localizedAdjunctionData
    where
  unitMappingConeModel := unitData.unitMappingConeModel
  unitMappingConeStrictExact := unitData.unitMappingConeStrictExact
  unitMappingConeIso := unitData.unitMappingConeIso

theorem repackUnitStrictExactIsoDataW1311_eq
    {localizedAdjunctionData :
      BoundedHomotopyLocalizedAdjunctionDataProviderW975}
    (unitData :
      UnitMappingConeStrictExactIsoDataProviderW981 localizedAdjunctionData) :
    repackUnitStrictExactIsoDataW1311 unitData =
      unitData := by
  cases unitData
  rfl

theorem w976UnitProviderModelOfW981UnitDataW1311
    {localizedAdjunctionData :
      BoundedHomotopyLocalizedAdjunctionDataProviderW975}
    (unitData :
      UnitMappingConeStrictExactIsoDataProviderW981 localizedAdjunctionData) :
    (unitKernelCokernelTopIsoDataOfUnitStrictExactIsoW981
        unitData).unitMappingConeModel =
      unitData.unitMappingConeModel :=
  rfl

theorem w976UnitProviderIsoOfW981UnitDataW1311
    {localizedAdjunctionData :
      BoundedHomotopyLocalizedAdjunctionDataProviderW975}
    (unitData :
      UnitMappingConeStrictExactIsoDataProviderW981 localizedAdjunctionData) :
    (unitKernelCokernelTopIsoDataOfUnitStrictExactIsoW981
        unitData).unitMappingConeIso =
      unitData.unitMappingConeIso :=
  rfl

structure MetrizableUnitStrictExactIsoBoundaryGuardStateW1311 :
    Type where
  seed : String
  inspectedBoundary : String
  innerSurfaceCount : Nat
  routeSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableUnitStrictExactIsoBoundaryGuardStateW1311 :
    MetrizableUnitStrictExactIsoBoundaryGuardStateW1311 where
  seed := "w1311-unit-strict-exact-iso-boundary-guard"
  inspectedBoundary :=
    "W981 unit mapping-cone strict-exact/isomorphism data constructing the W976\
      unit kernel/cokernel-top provider"
  innerSurfaceCount :=
    canonicalW981UnitStrictExactIsoInnerInputNamesW1311.length
  routeSurfaceCount :=
    canonicalW981UnitStrictExactIsoRouteInputNamesW1311.length
  providerSearchResult :=
    "proved: W981 reduces the W976 unit provider presentation to model,\
      strict short exactness, and chosen isomorphism, but this is still a\
      three-input unit boundary and a seven-input full-data route; repacking\
      W981 unit data is the same provider, so this boundary does not close the\
      remaining W987 obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1311UnitStrictExactIsoBoundaryGuard_productSuccess :
    (let state :=
        currentMetrizableUnitStrictExactIsoBoundaryGuardStateW1311;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
