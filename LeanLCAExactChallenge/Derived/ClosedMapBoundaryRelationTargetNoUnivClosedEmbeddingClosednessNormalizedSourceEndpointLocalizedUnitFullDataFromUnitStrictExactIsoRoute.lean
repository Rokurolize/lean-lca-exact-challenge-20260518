import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromLocalizedUnitChoiceRoute

/-!
W989 constructs the W988 localized-unit-choice provider from the W981
localized-adjunction plus unit strict-exact/isomorphism surface.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology
open DirectWppLimitFiniteShapeTransfer
open WppOpW426W318LegCompatibilityAlignmentV370SupportW439
open WppOpSelectedW461TransportedPointIsoProviderV370SupportW506
open WppOpClosedNatTransOrdinaryRelationTopologyV370SupportW511
open WppOpClosedNatTransOrdinaryRelationFieldsV370SupportW512
open WppOpW461BridgeComponentwiseClosedRangeProjectionV370SupportW481
open WppOpClosedRangeOnlyComponentwiseProjectionV370SupportW484
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

/-- W989 constructs W945 localized-unit data from W981 unit strict-exact/isomorphism data. -/
noncomputable def localizedUnitDataOfUnitStrictExactIsoW989
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945
    where
  boundedHomotopyLocalizedRightAdjoint :=
    boundedHomotopyLocalizedRightAdjointOfLocalizedAdjunctionDataW975
      unitStrictExactIsoData.localizedAdjunctionData
  boundedHomotopyLocalizedAdjunction :=
    boundedHomotopyLocalizedAdjunctionOfLocalizedAdjunctionDataW975
      unitStrictExactIsoData.localizedAdjunctionData
  boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents :=
    fun X =>
      ⟨unitStrictExactIsoData.unitStrictExactIsoData.unitMappingConeModel X,
        fun i =>
          (unitStrictExactIsoData.unitStrictExactIsoData.unitMappingConeStrictExact
            X i).closed_inclusion,
        fun i =>
          (unitStrictExactIsoData.unitStrictExactIsoData.unitMappingConeStrictExact
            X i).open_map,
        fun i =>
          (unitStrictExactIsoData.unitStrictExactIsoData.unitMappingConeStrictExact
            X i).surjective,
        fun i =>
          (unitStrictExactIsoData.unitStrictExactIsoData.unitMappingConeStrictExact
            X i).algebraic_exact,
        ⟨unitStrictExactIsoData.unitStrictExactIsoData.unitMappingConeIso X⟩⟩

/-- W989 constructs W982 localized-unit-choice data from W981 data. -/
noncomputable def localizedUnitChoiceDataOfUnitStrictExactIsoW989
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982
    where
  boundaryRelationData := unitStrictExactIsoData.boundaryRelationData
  targetNoUnivData := unitStrictExactIsoData.targetNoUnivData
  closedEmbeddingClosednessData :=
    unitStrictExactIsoData.closedEmbeddingClosednessData
  endpointStrictExact := unitStrictExactIsoData.endpointStrictExact
  localizedUnitData :=
    localizedUnitDataOfUnitStrictExactIsoW989 unitStrictExactIsoData
  normalizedSourceTriangulationData :=
    unitStrictExactIsoData.normalizedSourceTriangulationData

/-- W989 constructs W987 full data from W981 unit strict-exact/isomorphism data. -/
noncomputable def fullDataOfUnitStrictExactIsoW989
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfLocalizedUnitChoiceW988
    (localizedUnitChoiceDataOfUnitStrictExactIsoW989 unitStrictExactIsoData)

/- W989 feeds W988 after constructing W982 localized-unit-choice data. -/
noncomputable def w981LeavesOfUnitStrictExactIsoW989
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w981LeavesOfLocalizedUnitChoiceW988
    (localizedUnitChoiceDataOfUnitStrictExactIsoW989 unitStrictExactIsoData)

/- W989 exposes the W971 component-field split obtained through W988. -/
noncomputable def componentFieldsOfUnitStrictExactIsoW989
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfLocalizedUnitChoiceW988
    (localizedUnitChoiceDataOfUnitStrictExactIsoW989 unitStrictExactIsoData)

/-- W989 reconstructs endpoint strict short exactness through W988. -/
noncomputable def endpointStrictExactOfUnitStrictExactIsoW989
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfLocalizedUnitChoiceW988
    (localizedUnitChoiceDataOfUnitStrictExactIsoW989 unitStrictExactIsoData)

/-- W989 derives unit mapping-cone algebraic exactness through W988. -/
noncomputable def unitMappingConeAlgebraicExactOfUnitStrictExactIsoW989
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ :
        (((componentFieldsOfUnitStrictExactIsoW989 unitStrictExactIsoData).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfUnitStrictExactIsoW989 unitStrictExactIsoData).unitMappingConeModel X).as.sc i).g x₂ =
            0 →
          ∃ x₁ :
            (((componentFieldsOfUnitStrictExactIsoW989 unitStrictExactIsoData).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfUnitStrictExactIsoW989 unitStrictExactIsoData).unitMappingConeModel X).as.sc i).f x₁ =
              x₂ :=
  unitMappingConeAlgebraicExactOfLocalizedUnitChoiceW988
    (localizedUnitChoiceDataOfUnitStrictExactIsoW989 unitStrictExactIsoData)

/-- W989 reconstructs unit mapping-cone strict short exactness through W988. -/
noncomputable def unitMappingConeStrictExactOfUnitStrictExactIsoW989
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfUnitStrictExactIsoW989 unitStrictExactIsoData).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfLocalizedUnitChoiceW988
    (localizedUnitChoiceDataOfUnitStrictExactIsoW989 unitStrictExactIsoData)

/-- W989 wraps the unit mapping-cone isomorphism through W988. -/
@[reducible]
noncomputable def unitMappingConeIsoNonemptyOfUnitStrictExactIsoW989
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfUnitStrictExactIsoW989 unitStrictExactIsoData).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfUnitStrictExactIsoW989 unitStrictExactIsoData).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfLocalizedUnitChoiceW988
    (localizedUnitChoiceDataOfUnitStrictExactIsoW989 unitStrictExactIsoData)

theorem directBoundedLeftCalculusOfUnitStrictExactIsoW989
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfLocalizedUnitChoiceW988
    (localizedUnitChoiceDataOfUnitStrictExactIsoW989 unitStrictExactIsoData)

noncomputable def boundedDerivedInfinityCategoryOfUnitStrictExactIsoW989
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfLocalizedUnitChoiceW988
    (localizedUnitChoiceDataOfUnitStrictExactIsoW989 unitStrictExactIsoData)

def unitStrictExactIsoInputNamesW989 : List String :=
  ["W730 boundary/relation data provider",
    "W944 target no-univ data provider",
    "W973 closed-embedding closedness data provider",
    "endpoint strict-exact family",
    "W975 localized-adjunction data provider",
    "W981 unit strict-exact/isomorphism data provider",
    "W948 normalized-source-triangulation data provider"]

theorem unitStrictExactIsoInputNamesW989_count :
    unitStrictExactIsoInputNamesW989.length = 7 :=
  rfl

structure MetrizableUnitStrictExactIsoRouteStateW989 : Type where
  seed : String
  declarations : List String
  localizedUnitConstructionResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableUnitStrictExactIsoRouteStateW989 :
    MetrizableUnitStrictExactIsoRouteStateW989
    where
  seed := "w989-unit-strict-exact-iso-to-w988-localized-unit-choice-route"
  declarations :=
    ["localizedUnitDataOfUnitStrictExactIsoW989",
      "localizedUnitChoiceDataOfUnitStrictExactIsoW989",
      "fullDataOfUnitStrictExactIsoW989",
      "w981LeavesOfUnitStrictExactIsoW989",
      "componentFieldsOfUnitStrictExactIsoW989",
      "endpointStrictExactOfUnitStrictExactIsoW989",
      "unitMappingConeAlgebraicExactOfUnitStrictExactIsoW989",
      "unitMappingConeStrictExactOfUnitStrictExactIsoW989",
      "unitMappingConeIsoNonemptyOfUnitStrictExactIsoW989",
      "directBoundedLeftCalculusOfUnitStrictExactIsoW989",
      "boundedDerivedInfinityCategoryOfUnitStrictExactIsoW989",
      "unitStrictExactIsoInputNamesW989_count"]
  localizedUnitConstructionResult :=
    "proved: W989 constructs W945 localized-unit data from W975\
      localized-adjunction data and W981 unit strict-exact/isomorphism data"
  exactAtResult :=
    "proved: the W989 W981 field surface feeds the W988/W987/W986/W985/W984/\
      W983/W982/W981/W980/W979/W978/W977/W976/W975/W974/W973/W972/W971/W970/\
      W969/W968/W967/W966/W965/W964/W963/W962/W961/W959/W958/W957/W956/W955/\
      W954/W953/W952 stable ExactAt route"
  remainingInputs := unitStrictExactIsoInputNamesW989
  productSuccessClaimed := false

theorem currentW989UnitStrictExactIsoRoute_productSuccess :
    (let state := currentMetrizableUnitStrictExactIsoRouteStateW989;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
