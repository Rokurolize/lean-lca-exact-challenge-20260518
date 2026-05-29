import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataLocalizedUnitChoiceFieldSplitGuardW1327
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromUnitStrictExactIsoRoute

/-!
W1328 supplements the existing W1316 W989 guard by recording the field-split
equalities from W981 unit strict-exact/isomorphism data into W982
localized-unit-choice data and W945 localized-unit data. The route still
exposes W989's seven inputs and therefore does not close the current one-input
W987 obligation.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def canonicalW989UnitStrictExactIsoFieldSplitInputNamesW1328 :
    List String :=
  unitStrictExactIsoInputNamesW989

theorem canonicalW989UnitStrictExactIsoFieldSplitInputNamesW1328_count :
    canonicalW989UnitStrictExactIsoFieldSplitInputNamesW1328.length = 7 :=
  unitStrictExactIsoInputNamesW989_count

theorem canonicalW989UnitStrictExactIsoFieldSplitExpandsCurrentSurfaceW1328 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW989UnitStrictExactIsoFieldSplitInputNamesW1328.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW989UnitStrictExactIsoFieldSplitInputNamesW1328_count]
  norm_num

theorem w989LocalizedUnitChoiceKeepsTargetNoUnivW1328
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    (localizedUnitChoiceDataOfUnitStrictExactIsoW989 data).targetNoUnivData =
      data.targetNoUnivData :=
  rfl

theorem w989LocalizedUnitChoiceKeepsClosednessW1328
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    (localizedUnitChoiceDataOfUnitStrictExactIsoW989
        data).closedEmbeddingClosednessData =
      data.closedEmbeddingClosednessData :=
  rfl

theorem w989LocalizedUnitChoiceKeepsEndpointStrictExactW1328
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    (localizedUnitChoiceDataOfUnitStrictExactIsoW989 data).endpointStrictExact =
      data.endpointStrictExact :=
  rfl

theorem w989LocalizedUnitChoiceKeepsNormalizedSourceW1328
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    (localizedUnitChoiceDataOfUnitStrictExactIsoW989
        data).normalizedSourceTriangulationData =
      data.normalizedSourceTriangulationData :=
  rfl

theorem w989LocalizedUnitUsesLocalizedRightAdjointW1328
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    (localizedUnitDataOfUnitStrictExactIsoW989
        data).boundedHomotopyLocalizedRightAdjoint =
      boundedHomotopyLocalizedRightAdjointOfLocalizedAdjunctionDataW975
        data.localizedAdjunctionData :=
  rfl

theorem w989LocalizedUnitUsesLocalizedAdjunctionW1328
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    (localizedUnitDataOfUnitStrictExactIsoW989
        data).boundedHomotopyLocalizedAdjunction =
      boundedHomotopyLocalizedAdjunctionOfLocalizedAdjunctionDataW975
        data.localizedAdjunctionData :=
  rfl

theorem w989LocalizedUnitComponentsUseUnitStrictExactIsoW1328
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    (localizedUnitDataOfUnitStrictExactIsoW989
        data).boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents =
      fun X =>
        ⟨data.unitStrictExactIsoData.unitMappingConeModel X,
          fun i =>
            (data.unitStrictExactIsoData.unitMappingConeStrictExact
              X i).closed_inclusion,
          fun i =>
            (data.unitStrictExactIsoData.unitMappingConeStrictExact X i).open_map,
          fun i =>
            (data.unitStrictExactIsoData.unitMappingConeStrictExact X i).surjective,
          fun i =>
            (data.unitStrictExactIsoData.unitMappingConeStrictExact
              X i).algebraic_exact,
          ⟨data.unitStrictExactIsoData.unitMappingConeIso X⟩⟩ :=
  rfl

structure MetrizableUnitStrictExactIsoFieldSplitGuardStateW1328 : Type where
  seed : String
  inspectedBoundary : String
  routeSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableUnitStrictExactIsoFieldSplitGuardStateW1328 :
    MetrizableUnitStrictExactIsoFieldSplitGuardStateW1328 where
  seed := "w1328-unit-strict-exact-iso-field-split-guard"
  inspectedBoundary :=
    "W989 field split from W981 unit strict-exact/isomorphism data into W982\
      localized-unit-choice data and W945 localized-unit data"
  routeSurfaceCount :=
    canonicalW989UnitStrictExactIsoFieldSplitInputNamesW1328.length
  providerSearchResult :=
    "proved: W989 preserves target no-univ, closedness, endpoint strict\
      exactness, normalized-source, localized right adjoint, localized\
      adjunction, and unit mapping-cone model fields, but its route surface\
      still has seven inputs and expands the current one-input W987 obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1328UnitStrictExactIsoFieldSplitGuard_productSuccess :
    (let state :=
        currentMetrizableUnitStrictExactIsoFieldSplitGuardStateW1328;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
