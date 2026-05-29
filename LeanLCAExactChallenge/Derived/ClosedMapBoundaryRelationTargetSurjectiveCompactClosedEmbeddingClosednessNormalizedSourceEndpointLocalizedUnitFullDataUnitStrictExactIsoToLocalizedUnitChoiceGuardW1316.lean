import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataUnitStrictExactIsoBoundaryGuardW1311
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromUnitStrictExactIsoRoute

/-!
W1316 records the W989 constructor from W981 unit strict-exact/isomorphism
data into the W988 localized-unit-choice route. This proves the constructor
surface is the seven-input W981 route, so it expands the current one-input
W987 obligation rather than closing it.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def canonicalW989UnitStrictExactIsoInputNamesW1316 : List String :=
  unitStrictExactIsoInputNamesW989

theorem canonicalW989UnitStrictExactIsoInputNamesW1316_count :
    canonicalW989UnitStrictExactIsoInputNamesW1316.length = 7 :=
  unitStrictExactIsoInputNamesW989_count

theorem canonicalW989UnitStrictExactIsoRouteExpandsCurrentSurfaceW1316 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW989UnitStrictExactIsoInputNamesW1316.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW989UnitStrictExactIsoInputNamesW1316_count]
  norm_num

theorem w989LocalizedUnitChoiceKeepsBoundaryRelationW1316
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    (localizedUnitChoiceDataOfUnitStrictExactIsoW989
        unitStrictExactIsoData).boundaryRelationData =
      unitStrictExactIsoData.boundaryRelationData :=
  rfl

theorem w989LocalizedUnitChoiceBuildsLocalizedUnitDataW1316
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    (localizedUnitChoiceDataOfUnitStrictExactIsoW989
        unitStrictExactIsoData).localizedUnitData =
      localizedUnitDataOfUnitStrictExactIsoW989 unitStrictExactIsoData :=
  rfl

theorem w989FullDataRunsThroughW988W1316
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    fullDataOfUnitStrictExactIsoW989 unitStrictExactIsoData =
      fullDataOfLocalizedUnitChoiceW988
        (localizedUnitChoiceDataOfUnitStrictExactIsoW989
          unitStrictExactIsoData) :=
  rfl

theorem w989ComponentFieldsRunThroughW988W1316
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    componentFieldsOfUnitStrictExactIsoW989 unitStrictExactIsoData =
      componentFieldsOfLocalizedUnitChoiceW988
        (localizedUnitChoiceDataOfUnitStrictExactIsoW989
          unitStrictExactIsoData) :=
  rfl

structure MetrizableUnitStrictExactIsoToLocalizedUnitChoiceGuardStateW1316 :
    Type where
  seed : String
  inspectedBoundary : String
  routeSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableUnitStrictExactIsoToLocalizedUnitChoiceGuardStateW1316 :
    MetrizableUnitStrictExactIsoToLocalizedUnitChoiceGuardStateW1316 where
  seed := "w1316-unit-strict-exact-iso-to-localized-unit-choice-guard"
  inspectedBoundary :=
    "W989 construction of W988 localized-unit-choice data and W987 full data\
      from the W981 unit strict-exact/isomorphism surface"
  routeSurfaceCount := canonicalW989UnitStrictExactIsoInputNamesW1316.length
  providerSearchResult :=
    "proved: W989 routes W981 through W988 by building localized-unit-choice\
      data, but the route surface has seven inputs and therefore expands the\
      current one-input W987 obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1316UnitStrictExactIsoToLocalizedUnitChoiceGuard_productSuccess :
    (let state :=
        currentMetrizableUnitStrictExactIsoToLocalizedUnitChoiceGuardStateW1316;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
