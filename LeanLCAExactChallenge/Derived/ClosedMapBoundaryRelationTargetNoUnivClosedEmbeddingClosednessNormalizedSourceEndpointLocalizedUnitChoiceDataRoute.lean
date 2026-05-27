import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessEndpointLocalizedUnitChoiceDataRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataPrimitiveFieldRoute

/-!
W985 replaces W984's separate normalized-source-triangulation and
endpoint-localized-unit inputs by the existing W950 normalized-source/endpoint
localized-unit provider.
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
W985 full-data provider: W984's surface with normalized-source-triangulation
and endpoint-localized-unit data supplied by one W950 provider.
-/
structure BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitChoiceDataProviderW985 :
    Type 2 where
  boundaryRelationData :
    MetrizableWppBoundaryRelationDataProviderW730
  targetClosedEmbeddingClosednessData :
    TargetNoUnivClosedEmbeddingClosednessDataProviderW984
  normalizedSourceEndpointLocalizedUnitData :
    NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950

/-- W985 constructs the W984 full-data provider from normalized-source/endpoint data. -/
noncomputable def fullDataOfNormalizedSourceEndpointLocalizedUnitW985
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitChoiceDataProviderW985) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessEndpointLocalizedUnitChoiceDataProviderW984
    where
  boundaryRelationData := fullData.boundaryRelationData
  targetClosedEmbeddingClosednessData :=
    fullData.targetClosedEmbeddingClosednessData
  endpointLocalizedUnitData :=
    endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitDataW950
      fullData.normalizedSourceEndpointLocalizedUnitData
  normalizedSourceTriangulationData :=
    normalizedSourceTriangulationDataOfNormalizedSourceEndpointLocalizedUnitDataW950
      fullData.normalizedSourceEndpointLocalizedUnitData

/- W985 feeds W984 after unpacking W950 normalized-source/endpoint data. -/
noncomputable def w981LeavesOfNormalizedSourceEndpointLocalizedUnitW985
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitChoiceDataProviderW985) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w981LeavesOfTargetClosedEmbeddingClosednessW984
    (fullDataOfNormalizedSourceEndpointLocalizedUnitW985 fullData)

/- W985 exposes the W971 component-field split obtained through W984. -/
noncomputable def componentFieldsOfNormalizedSourceEndpointLocalizedUnitW985
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitChoiceDataProviderW985) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfTargetClosedEmbeddingClosednessW984
    (fullDataOfNormalizedSourceEndpointLocalizedUnitW985 fullData)

/-- W985 reconstructs endpoint strict short exactness through W984. -/
noncomputable def endpointStrictExactOfNormalizedSourceEndpointLocalizedUnitW985
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitChoiceDataProviderW985) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfTargetClosedEmbeddingClosednessW984
    (fullDataOfNormalizedSourceEndpointLocalizedUnitW985 fullData)

/-- W985 derives unit mapping-cone algebraic exactness through W984. -/
noncomputable def unitMappingConeAlgebraicExactOfNormalizedSourceEndpointLocalizedUnitW985
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitChoiceDataProviderW985) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ :
        (((componentFieldsOfNormalizedSourceEndpointLocalizedUnitW985 fullData).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfNormalizedSourceEndpointLocalizedUnitW985 fullData).unitMappingConeModel X).as.sc i).g x₂ =
            0 →
          ∃ x₁ :
            (((componentFieldsOfNormalizedSourceEndpointLocalizedUnitW985 fullData).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfNormalizedSourceEndpointLocalizedUnitW985 fullData).unitMappingConeModel X).as.sc i).f x₁ =
              x₂ :=
  unitMappingConeAlgebraicExactOfTargetClosedEmbeddingClosednessW984
    (fullDataOfNormalizedSourceEndpointLocalizedUnitW985 fullData)

/-- W985 reconstructs unit mapping-cone strict short exactness through W984. -/
noncomputable def unitMappingConeStrictExactOfNormalizedSourceEndpointLocalizedUnitW985
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitChoiceDataProviderW985) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfNormalizedSourceEndpointLocalizedUnitW985 fullData).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfTargetClosedEmbeddingClosednessW984
    (fullDataOfNormalizedSourceEndpointLocalizedUnitW985 fullData)

/-- W985 wraps the unit mapping-cone isomorphism through W984. -/
@[reducible]
noncomputable def unitMappingConeIsoNonemptyOfNormalizedSourceEndpointLocalizedUnitW985
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitChoiceDataProviderW985) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfNormalizedSourceEndpointLocalizedUnitW985 fullData).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfNormalizedSourceEndpointLocalizedUnitW985 fullData).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfTargetClosedEmbeddingClosednessW984
    (fullDataOfNormalizedSourceEndpointLocalizedUnitW985 fullData)

theorem directBoundedLeftCalculusOfNormalizedSourceEndpointLocalizedUnitW985
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitChoiceDataProviderW985) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessW984
    (fullDataOfNormalizedSourceEndpointLocalizedUnitW985 fullData)

noncomputable def boundedDerivedInfinityCategoryOfNormalizedSourceEndpointLocalizedUnitW985
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitChoiceDataProviderW985) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessW984
    (fullDataOfNormalizedSourceEndpointLocalizedUnitW985 fullData)

def normalizedSourceEndpointLocalizedUnitChoiceInputNamesW985 : List String :=
  ["W730 boundary/relation data provider",
    "W984 target no-univ plus closed-embedding closedness data provider",
    "W950 normalized-source/endpoint-localized-unit data provider"]

theorem normalizedSourceEndpointLocalizedUnitChoiceInputNamesW985_count :
    normalizedSourceEndpointLocalizedUnitChoiceInputNamesW985.length = 3 :=
  rfl

structure MetrizableNormalizedSourceEndpointLocalizedUnitChoiceFullDataRouteStateW985 :
    Type where
  seed : String
  declarations : List String
  normalizedEndpointProjectionResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableNormalizedSourceEndpointLocalizedUnitChoiceFullDataRouteStateW985 :
    MetrizableNormalizedSourceEndpointLocalizedUnitChoiceFullDataRouteStateW985
    where
  seed := "w985-normalized-source-endpoint-localized-unit-choice-route"
  declarations :=
    ["BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitChoiceDataProviderW985",
      "fullDataOfNormalizedSourceEndpointLocalizedUnitW985",
      "w981LeavesOfNormalizedSourceEndpointLocalizedUnitW985",
      "componentFieldsOfNormalizedSourceEndpointLocalizedUnitW985",
      "endpointStrictExactOfNormalizedSourceEndpointLocalizedUnitW985",
      "unitMappingConeAlgebraicExactOfNormalizedSourceEndpointLocalizedUnitW985",
      "unitMappingConeStrictExactOfNormalizedSourceEndpointLocalizedUnitW985",
      "unitMappingConeIsoNonemptyOfNormalizedSourceEndpointLocalizedUnitW985",
      "directBoundedLeftCalculusOfNormalizedSourceEndpointLocalizedUnitW985",
      "boundedDerivedInfinityCategoryOfNormalizedSourceEndpointLocalizedUnitW985",
      "normalizedSourceEndpointLocalizedUnitChoiceInputNamesW985_count"]
  normalizedEndpointProjectionResult :=
    "proved: W985 extracts W948 normalized-source-triangulation data and W949\
      endpoint-localized-unit data from the existing W950 provider"
  exactAtResult :=
    "proved: the W985 normalized-source/endpoint-localized full-data surface\
      feeds the W984/W983/W982/W981/W980/W979/W978/W977/W976/W975/W974/\
      W973/W972/W971/W970/W969/W968/W967/W966/W965/W964/W963/W962/W961/\
      W959/W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs :=
    normalizedSourceEndpointLocalizedUnitChoiceInputNamesW985
  productSuccessClaimed := false

theorem currentW985NormalizedSourceEndpointLocalizedUnitChoiceFullDataRoute_productSuccess :
    (let state :=
        currentMetrizableNormalizedSourceEndpointLocalizedUnitChoiceFullDataRouteStateW985;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
