import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataRoute
import LeanLCAExactChallenge.Derived.ClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataPrimitiveFieldRoute

/-!
W982 replaces W981's separate localized-adjunction and unit
strict-exact/isomorphism data providers by the earlier W945 localized-unit
provider.
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

/-- W982 extracts the W975 localized-adjunction provider from W945 data. -/
def localizedAdjunctionDataOfLocalizedUnitDataW982
    (localizedUnitData :
      BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945) :
    BoundedHomotopyLocalizedAdjunctionDataProviderW975
    where
  boundedHomotopyLocalizedRightAdjoint :=
    boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
      localizedUnitData
  boundedHomotopyLocalizedAdjunction :=
    boundedHomotopyLocalizedAdjunctionOfLocalizedUnitDataW945
      localizedUnitData

/--
W982 chooses W981's unit mapping-cone model, strict short exactness, and
mapping-cone isomorphism from W945's W939 component witness.
-/
noncomputable def unitStrictExactIsoDataOfLocalizedUnitDataW982
    (localizedUnitData :
      BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945) :
    UnitMappingConeStrictExactIsoDataProviderW981
      (localizedAdjunctionDataOfLocalizedUnitDataW982 localizedUnitData)
    where
  unitMappingConeModel := fun X =>
    Classical.choose
      (boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponentsOfLocalizedUnitDataW945
        localizedUnitData X)
  unitMappingConeStrictExact := fun X i => by
    classical
    let hX :=
      Classical.choose_spec
        (boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponentsOfLocalizedUnitDataW945
          localizedUnitData X)
    exact
      { closed_inclusion := hX.1 i
        open_map := hX.2.1 i
        surjective := hX.2.2.1 i
        algebraic_exact := hX.2.2.2.1 i }
  unitMappingConeIso := fun X => by
    classical
    let hX :=
      Classical.choose_spec
        (boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponentsOfLocalizedUnitDataW945
          localizedUnitData X)
    exact Classical.choice hX.2.2.2.2

/--
W982 full-data provider: W981's endpoint strict-exact route with localized
adjunction and unit strict-exact/isomorphism supplied by one W945 localized-unit
provider.
-/
structure BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :
    Type 2 where
  boundaryRelationData :
    MetrizableWppBoundaryRelationDataProviderW730
  targetNoUnivData :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944
  closedEmbeddingClosednessData :
    ClosedEmbeddingClosednessDataProviderW973
  endpointStrictExact :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i)
  localizedUnitData :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945
  normalizedSourceTriangulationData :
    NormalizedFixedTargetSourceTriangulationDataProviderW948

/-- W982 constructs the W981 full-data provider from localized-unit data. -/
noncomputable def fullDataOfLocalizedUnitChoiceW982
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981
    where
  boundaryRelationData := fullData.boundaryRelationData
  targetNoUnivData := fullData.targetNoUnivData
  closedEmbeddingClosednessData := fullData.closedEmbeddingClosednessData
  endpointStrictExact := fullData.endpointStrictExact
  localizedAdjunctionData :=
    localizedAdjunctionDataOfLocalizedUnitDataW982
      fullData.localizedUnitData
  normalizedSourceTriangulationData :=
    fullData.normalizedSourceTriangulationData
  unitStrictExactIsoData :=
    unitStrictExactIsoDataOfLocalizedUnitDataW982
      fullData.localizedUnitData

/- W982 feeds W981 after projecting W945 localized-unit data. -/
noncomputable def w981LeavesOfLocalizedUnitChoiceW982
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w980LeavesOfUnitStrictExactIsoW981
    (fullDataOfLocalizedUnitChoiceW982 fullData)

/- W982 exposes the W971 component-field split obtained through W981. -/
noncomputable def componentFieldsOfLocalizedUnitChoiceW982
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfUnitStrictExactIsoW981
    (fullDataOfLocalizedUnitChoiceW982 fullData)

/-- W982 reconstructs endpoint strict short exactness through W981. -/
noncomputable def endpointStrictExactOfLocalizedUnitChoiceW982
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfUnitStrictExactIsoW981
    (fullDataOfLocalizedUnitChoiceW982 fullData)

/-- W982 derives unit mapping-cone algebraic exactness through W981. -/
noncomputable def unitMappingConeAlgebraicExactOfLocalizedUnitChoiceW982
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ :
        (((componentFieldsOfLocalizedUnitChoiceW982 fullData).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfLocalizedUnitChoiceW982 fullData).unitMappingConeModel X).as.sc i).g x₂ =
            0 →
          ∃ x₁ :
            (((componentFieldsOfLocalizedUnitChoiceW982 fullData).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfLocalizedUnitChoiceW982 fullData).unitMappingConeModel X).as.sc i).f x₁ =
              x₂ :=
  unitMappingConeAlgebraicExactOfUnitStrictExactIsoW981
    (fullDataOfLocalizedUnitChoiceW982 fullData)

/-- W982 reconstructs unit mapping-cone strict short exactness through W981. -/
noncomputable def unitMappingConeStrictExactOfLocalizedUnitChoiceW982
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfLocalizedUnitChoiceW982 fullData).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfUnitStrictExactIsoW981
    (fullDataOfLocalizedUnitChoiceW982 fullData)

/-- W982 wraps the unit mapping-cone isomorphism through W981. -/
@[reducible]
noncomputable def unitMappingConeIsoNonemptyOfLocalizedUnitChoiceW982
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfLocalizedUnitChoiceW982 fullData).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfLocalizedUnitChoiceW982 fullData).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfUnitStrictExactIsoW981
    (fullDataOfLocalizedUnitChoiceW982 fullData)

theorem directBoundedLeftCalculusOfLocalizedUnitChoiceW982
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfUnitStrictExactIsoW981
    (fullDataOfLocalizedUnitChoiceW982 fullData)

noncomputable def boundedDerivedInfinityCategoryOfLocalizedUnitChoiceW982
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfUnitStrictExactIsoW981
    (fullDataOfLocalizedUnitChoiceW982 fullData)

def endpointStrictExactLocalizedUnitChoiceFullDataInputNamesW982 : List String :=
  ["W730 boundary/relation data provider",
    "W944 target no-univ data provider",
    "W973 closed-embedding closedness data provider",
    "endpoint strict short-exact family",
    "W945 localized-unit data provider",
    "W948 normalized-source-triangulation data provider"]

theorem endpointStrictExactLocalizedUnitChoiceFullDataInputNamesW982_count :
    endpointStrictExactLocalizedUnitChoiceFullDataInputNamesW982.length = 6 :=
  rfl

structure MetrizableEndpointStrictExactLocalizedUnitChoiceFullDataRouteStateW982 :
    Type where
  seed : String
  declarations : List String
  localizedUnitProjectionResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableEndpointStrictExactLocalizedUnitChoiceFullDataRouteStateW982 :
    MetrizableEndpointStrictExactLocalizedUnitChoiceFullDataRouteStateW982
    where
  seed := "w982-endpoint-strict-exact-localized-unit-choice-full-data-route"
  declarations :=
    ["localizedAdjunctionDataOfLocalizedUnitDataW982",
      "unitStrictExactIsoDataOfLocalizedUnitDataW982",
      "BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982",
      "fullDataOfLocalizedUnitChoiceW982",
      "w981LeavesOfLocalizedUnitChoiceW982",
      "componentFieldsOfLocalizedUnitChoiceW982",
      "endpointStrictExactOfLocalizedUnitChoiceW982",
      "unitMappingConeAlgebraicExactOfLocalizedUnitChoiceW982",
      "unitMappingConeStrictExactOfLocalizedUnitChoiceW982",
      "unitMappingConeIsoNonemptyOfLocalizedUnitChoiceW982",
      "directBoundedLeftCalculusOfLocalizedUnitChoiceW982",
      "boundedDerivedInfinityCategoryOfLocalizedUnitChoiceW982",
      "endpointStrictExactLocalizedUnitChoiceFullDataInputNamesW982_count"]
  localizedUnitProjectionResult :=
    "proved: W982 extracts W975 localized-adjunction data and W981 unit\
      strict-exact/isomorphism data from W945 localized-unit data by choosing\
      the W939 model, component witnesses, and mapping-cone isomorphism"
  exactAtResult :=
    "proved: the W982 localized-unit-choice full-data surface feeds the W981/\
      W980/W979/W978/W977/W976/W975/W974/W973/W972/W971/W970/W969/W968/W967/\
      W966/W965/W964/W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/\
      W952 stable ExactAt route"
  remainingInputs := endpointStrictExactLocalizedUnitChoiceFullDataInputNamesW982
  productSuccessClaimed := false

theorem currentW982EndpointStrictExactLocalizedUnitChoiceFullDataRoute_productSuccess :
    (let state := currentMetrizableEndpointStrictExactLocalizedUnitChoiceFullDataRouteStateW982;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
