import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataPrimitiveFieldRoute

/-!
W983 replaces W982's separate endpoint strict-exact and W945 localized-unit
inputs by the existing W949 endpoint-localized-unit provider.
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

/--
W983 full-data provider: W982's surface with endpoint strict exactness and
localized-unit data supplied by one W949 endpoint-localized-unit provider.
-/
structure BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitChoiceDataProviderW983 :
    Type 2 where
  boundaryRelationData :
    MetrizableWppBoundaryRelationDataProviderW730
  targetNoUnivData :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944
  closedEmbeddingClosednessData :
    ClosedEmbeddingClosednessDataProviderW973
  endpointLocalizedUnitData :
    EndpointStrictExactLocalizedUnitDataProviderW949
  normalizedSourceTriangulationData :
    NormalizedFixedTargetSourceTriangulationDataProviderW948

/-- W983 constructs the W982 full-data provider from endpoint-localized-unit data. -/
noncomputable def fullDataOfEndpointLocalizedUnitChoiceW983
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitChoiceDataProviderW983) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982
    where
  boundaryRelationData := fullData.boundaryRelationData
  targetNoUnivData := fullData.targetNoUnivData
  closedEmbeddingClosednessData := fullData.closedEmbeddingClosednessData
  endpointStrictExact :=
    endpointStrictExactOfEndpointLocalizedUnitDataW949
      fullData.endpointLocalizedUnitData
  localizedUnitData :=
    localizedUnitDataOfEndpointLocalizedUnitDataW949
      fullData.endpointLocalizedUnitData
  normalizedSourceTriangulationData :=
    fullData.normalizedSourceTriangulationData

/- W983 feeds W982 after unpacking W949 endpoint-localized-unit data. -/
noncomputable def w981LeavesOfEndpointLocalizedUnitChoiceW983
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitChoiceDataProviderW983) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w981LeavesOfLocalizedUnitChoiceW982
    (fullDataOfEndpointLocalizedUnitChoiceW983 fullData)

/- W983 exposes the W971 component-field split obtained through W982. -/
noncomputable def componentFieldsOfEndpointLocalizedUnitChoiceW983
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitChoiceDataProviderW983) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfLocalizedUnitChoiceW982
    (fullDataOfEndpointLocalizedUnitChoiceW983 fullData)

/-- W983 reconstructs endpoint strict short exactness through W982. -/
noncomputable def endpointStrictExactOfEndpointLocalizedUnitChoiceW983
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitChoiceDataProviderW983) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfLocalizedUnitChoiceW982
    (fullDataOfEndpointLocalizedUnitChoiceW983 fullData)

/-- W983 derives unit mapping-cone algebraic exactness through W982. -/
noncomputable def unitMappingConeAlgebraicExactOfEndpointLocalizedUnitChoiceW983
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitChoiceDataProviderW983) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ :
        (((componentFieldsOfEndpointLocalizedUnitChoiceW983 fullData).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfEndpointLocalizedUnitChoiceW983 fullData).unitMappingConeModel X).as.sc i).g x₂ =
            0 →
          ∃ x₁ :
            (((componentFieldsOfEndpointLocalizedUnitChoiceW983 fullData).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfEndpointLocalizedUnitChoiceW983 fullData).unitMappingConeModel X).as.sc i).f x₁ =
              x₂ :=
  unitMappingConeAlgebraicExactOfLocalizedUnitChoiceW982
    (fullDataOfEndpointLocalizedUnitChoiceW983 fullData)

/-- W983 reconstructs unit mapping-cone strict short exactness through W982. -/
noncomputable def unitMappingConeStrictExactOfEndpointLocalizedUnitChoiceW983
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitChoiceDataProviderW983) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfEndpointLocalizedUnitChoiceW983 fullData).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfLocalizedUnitChoiceW982
    (fullDataOfEndpointLocalizedUnitChoiceW983 fullData)

/-- W983 wraps the unit mapping-cone isomorphism through W982. -/
@[reducible]
noncomputable def unitMappingConeIsoNonemptyOfEndpointLocalizedUnitChoiceW983
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitChoiceDataProviderW983) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfEndpointLocalizedUnitChoiceW983 fullData).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfEndpointLocalizedUnitChoiceW983 fullData).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfLocalizedUnitChoiceW982
    (fullDataOfEndpointLocalizedUnitChoiceW983 fullData)

theorem directBoundedLeftCalculusOfEndpointLocalizedUnitChoiceW983
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitChoiceDataProviderW983) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfLocalizedUnitChoiceW982
    (fullDataOfEndpointLocalizedUnitChoiceW983 fullData)

noncomputable def boundedDerivedInfinityCategoryOfEndpointLocalizedUnitChoiceW983
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitChoiceDataProviderW983) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfLocalizedUnitChoiceW982
    (fullDataOfEndpointLocalizedUnitChoiceW983 fullData)

def endpointLocalizedUnitChoiceFullDataInputNamesW983 : List String :=
  ["W730 boundary/relation data provider",
    "W944 target no-univ data provider",
    "W973 closed-embedding closedness data provider",
    "W949 endpoint-localized-unit data provider",
    "W948 normalized-source-triangulation data provider"]

theorem endpointLocalizedUnitChoiceFullDataInputNamesW983_count :
    endpointLocalizedUnitChoiceFullDataInputNamesW983.length = 5 :=
  rfl

structure MetrizableEndpointLocalizedUnitChoiceFullDataRouteStateW983 :
    Type where
  seed : String
  declarations : List String
  endpointLocalizedUnitProjectionResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableEndpointLocalizedUnitChoiceFullDataRouteStateW983 :
    MetrizableEndpointLocalizedUnitChoiceFullDataRouteStateW983
    where
  seed := "w983-endpoint-localized-unit-choice-full-data-route"
  declarations :=
    ["BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitChoiceDataProviderW983",
      "fullDataOfEndpointLocalizedUnitChoiceW983",
      "w981LeavesOfEndpointLocalizedUnitChoiceW983",
      "componentFieldsOfEndpointLocalizedUnitChoiceW983",
      "endpointStrictExactOfEndpointLocalizedUnitChoiceW983",
      "unitMappingConeAlgebraicExactOfEndpointLocalizedUnitChoiceW983",
      "unitMappingConeStrictExactOfEndpointLocalizedUnitChoiceW983",
      "unitMappingConeIsoNonemptyOfEndpointLocalizedUnitChoiceW983",
      "directBoundedLeftCalculusOfEndpointLocalizedUnitChoiceW983",
      "boundedDerivedInfinityCategoryOfEndpointLocalizedUnitChoiceW983",
      "endpointLocalizedUnitChoiceFullDataInputNamesW983_count"]
  endpointLocalizedUnitProjectionResult :=
    "proved: W983 extracts endpoint strict exactness and W945 localized-unit\
      data from W949 endpoint-localized-unit data, then feeds W982"
  exactAtResult :=
    "proved: the W983 endpoint-localized-unit full-data surface feeds the\
      W982/W981/W980/W979/W978/W977/W976/W975/W974/W973/W972/W971/W970/\
      W969/W968/W967/W966/W965/W964/W963/W962/W961/W959/W958/W957/W956/\
      W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := endpointLocalizedUnitChoiceFullDataInputNamesW983
  productSuccessClaimed := false

theorem currentW983EndpointLocalizedUnitChoiceFullDataRoute_productSuccess :
    (let state := currentMetrizableEndpointLocalizedUnitChoiceFullDataRouteStateW983;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
