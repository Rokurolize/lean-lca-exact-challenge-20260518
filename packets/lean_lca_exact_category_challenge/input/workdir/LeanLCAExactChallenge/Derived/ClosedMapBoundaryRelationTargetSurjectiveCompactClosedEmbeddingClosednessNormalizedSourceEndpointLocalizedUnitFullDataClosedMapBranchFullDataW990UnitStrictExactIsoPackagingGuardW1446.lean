import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosedMapBranchFullDataW990PrimitiveUnitComponentsAlignmentGuardW1445

/-!
W1446 records the next packaging step after W1445. The W1007-derived W990
primitive unit-components provider builds W981 unit strict-exact/isomorphism
full data, and W989 rebuilds localized-unit data from that W981 package while
preserving the localized right adjoint and localized adjunction.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def w1007W990UnitStrictExactIsoPackagedInputNamesW1446 : List String :=
  unitStrictExactIsoInputNamesW989

theorem w1007W990UnitStrictExactIsoPackagedInputNamesW1446_count :
    w1007W990UnitStrictExactIsoPackagedInputNamesW1446.length = 7 :=
  unitStrictExactIsoInputNamesW989_count

/-- W1446 packages the W1445 W990 provider into W981 full data. -/
noncomputable def w1007UnitStrictExactIsoFullDataW1446
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoFullDataOfPrimitiveUnitComponentsW990
    (w1007PrimitiveUnitComponentsDataW1445 branchFullData)

/-- W1446 rebuilds W945 localized-unit data from the W981 package through W989. -/
noncomputable def w1007W989LocalizedUnitDataW1446
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945 :=
  localizedUnitDataOfUnitStrictExactIsoW989
    (w1007UnitStrictExactIsoFullDataW1446 branchFullData)

/-- The W1446 W981 package keeps W1445's boundary/relation data. -/
theorem w1007W990UnitStrictExactIsoFullDataKeepsBoundaryRelationW1446
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (w1007UnitStrictExactIsoFullDataW1446
        branchFullData).boundaryRelationData =
      (w1007PrimitiveUnitComponentsDataW1445
        branchFullData).boundaryRelationData :=
  rfl

/-- The W1446 W981 package keeps W1445's localized-adjunction provider. -/
theorem w1007W990UnitStrictExactIsoFullDataKeepsLocalizedAdjunctionDataW1446
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (w1007UnitStrictExactIsoFullDataW1446
        branchFullData).localizedAdjunctionData =
      localizedAdjunctionDataOfPrimitiveUnitComponentsW990
        (w1007PrimitiveUnitComponentsDataW1445 branchFullData) :=
  rfl

/-- The W1446 W981 package keeps the W948 component produced by W1445. -/
theorem w1007W990UnitStrictExactIsoFullDataKeepsNormalizedSourceW1446
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (w1007UnitStrictExactIsoFullDataW1446
        branchFullData).normalizedSourceTriangulationData =
      (w1007PrimitiveUnitComponentsDataW1445
        branchFullData).normalizedSourceTriangulationData :=
  rfl

/-- W1446's W981 unit data chooses the W939 unit mapping-cone model. -/
theorem w1007W990UnitStrictExactIsoDataChoosesW939ModelW1446
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (w1007UnitStrictExactIsoFullDataW1446
        branchFullData).unitStrictExactIsoData.unitMappingConeModel =
      fun X =>
        Classical.choose
          ((w1007PrimitiveUnitComponentsDataW1445
            branchFullData).boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents
              X) :=
  rfl

/-- W989's rebuilt localized-unit data keeps W1445's localized right adjoint. -/
theorem w1007W989LocalizedUnitKeepsRightAdjointW1446
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
        (w1007W989LocalizedUnitDataW1446 branchFullData) =
      (w1007PrimitiveUnitComponentsDataW1445
        branchFullData).boundedHomotopyLocalizedRightAdjoint :=
  rfl

/-- W989's rebuilt localized-unit data keeps W1445's localized adjunction. -/
theorem w1007W989LocalizedUnitKeepsAdjunctionW1446
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    boundedHomotopyLocalizedAdjunctionOfLocalizedUnitDataW945
        (w1007W989LocalizedUnitDataW1446 branchFullData) =
      (w1007PrimitiveUnitComponentsDataW1445
        branchFullData).boundedHomotopyLocalizedAdjunction :=
  rfl

/-- W989's localized-unit-choice data uses the localized-unit data rebuilt in W1446. -/
theorem w1007W989LocalizedUnitChoiceUsesRebuiltLocalizedUnitW1446
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (localizedUnitChoiceDataOfUnitStrictExactIsoW989
        (w1007UnitStrictExactIsoFullDataW1446
          branchFullData)).localizedUnitData =
      w1007W989LocalizedUnitDataW1446 branchFullData :=
  rfl

/-- W1446 keeps W981's three internal unit strict-exact/isomorphism inputs visible. -/
theorem w1446W981UnitStrictExactIsoDataInputCount :
    unitStrictExactIsoDataInputNamesW981.length = 3 :=
  unitStrictExactIsoDataInputNamesW981_count

/-- W1446 keeps W989's seven-input W981 package surface visible. -/
theorem w1446W989UnitStrictExactIsoInputCount :
    w1007W990UnitStrictExactIsoPackagedInputNamesW1446.length = 7 :=
  w1007W990UnitStrictExactIsoPackagedInputNamesW1446_count

/-- W1446 packages W1445's eight W990 inputs into W989's seven-input W981 surface. -/
theorem w1446W990PrimitiveUnitComponentsPackagesToW989UnitStrictExactIso :
    w1007W990UnitStrictExactIsoPackagedInputNamesW1446.length <
      w1007W990PrimitiveUnitComponentsAlignedInputNamesW1445.length := by
  rw [w1007W990UnitStrictExactIsoPackagedInputNamesW1446_count,
    w1007W990PrimitiveUnitComponentsAlignedInputNamesW1445_count]
  norm_num

/-- Current W1446 nonterminal W990-to-W981/W989 packaging state. -/
structure ClosedMapBranchFullDataW990UnitStrictExactIsoPackagingStateW1446 :
    Type where
  seed : String
  declarations : List String
  packagingResult : String
  routeResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1446 records W990's W981 package and W989 localized-unit reconstruction. -/
def currentClosedMapBranchFullDataW990UnitStrictExactIsoPackagingStateW1446 :
    ClosedMapBranchFullDataW990UnitStrictExactIsoPackagingStateW1446 where
  seed := "w1446-closed-map-branch-full-data-w990-unit-strict-exact-iso-packaging"
  declarations :=
    ["w1007UnitStrictExactIsoFullDataW1446",
      "w1007W989LocalizedUnitDataW1446",
      "w1007W990UnitStrictExactIsoFullDataKeepsBoundaryRelationW1446",
      "w1007W990UnitStrictExactIsoFullDataKeepsLocalizedAdjunctionDataW1446",
      "w1007W990UnitStrictExactIsoFullDataKeepsNormalizedSourceW1446",
      "w1007W990UnitStrictExactIsoDataChoosesW939ModelW1446",
      "w1007W989LocalizedUnitKeepsRightAdjointW1446",
      "w1007W989LocalizedUnitKeepsAdjunctionW1446",
      "w1007W989LocalizedUnitChoiceUsesRebuiltLocalizedUnitW1446",
      "w1446W981UnitStrictExactIsoDataInputCount",
      "w1446W989UnitStrictExactIsoInputCount",
      "w1446W990PrimitiveUnitComponentsPackagesToW989UnitStrictExactIso"]
  packagingResult :=
    "proved: W1445's W990 provider packages into W981 full data, preserving\
      boundary/relation data, localized-adjunction data, and W948 data"
  routeResult :=
    "proved: W989 rebuilds localized-unit data from the W981 package while\
      preserving the localized right adjoint and localized adjunction; product\
      success is still not claimed"
  remainingInputs := w1007W990UnitStrictExactIsoPackagedInputNamesW1446
  productSuccessClaimed := false

theorem currentW1446ClosedMapBranchFullDataW990UnitStrictExactIsoPackaging_productSuccess :
    currentClosedMapBranchFullDataW990UnitStrictExactIsoPackagingStateW1446.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
