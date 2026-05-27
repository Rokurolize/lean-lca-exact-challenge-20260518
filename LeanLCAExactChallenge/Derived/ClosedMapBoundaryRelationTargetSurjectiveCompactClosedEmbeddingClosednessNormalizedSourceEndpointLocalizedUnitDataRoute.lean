import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitChoiceRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataPrimitiveFieldRoute

/-!
W994 feeds W993 using the existing W950 normalized-source/endpoint-localized
provider. This reduces W993's separate W948 normalized-source data, endpoint
strict exactness, and W945 localized-unit data inputs to one W950 input while
preserving W715 target compactness and W973 branch-specific closed-embedding
closedness.
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
W994 data surface: W993 with normalized-source, endpoint strict exactness, and
localized-unit data supplied by the existing W950 provider.
-/
structure BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994 :
    Type 2 where
  boundaryRelationData :
    MetrizableWppBoundaryRelationDataProviderW730
  targetSurjectiveCompactData :
    TargetSurjectiveCompactForTargetProviderW715
  closedEmbeddingClosednessData :
    ClosedEmbeddingClosednessDataProviderW973
  normalizedSourceEndpointLocalizedUnitData :
    NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950

/--
W994 projects W950 to the W949 endpoint-localized-unit data used by W993's
localized-unit-choice surface.
-/
def endpointLocalizedUnitDataOfTargetSurjectiveCompactNormalizedSourceEndpointW994
    (data :
      BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994) :
    EndpointStrictExactLocalizedUnitDataProviderW949 :=
  endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitDataW950
    data.normalizedSourceEndpointLocalizedUnitData

/-- W994 builds the W993 data surface by unpacking W950 through W949. -/
def localizedUnitChoiceDataOfTargetSurjectiveCompactNormalizedSourceEndpointW994
    (data :
      BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994) :
    BoundaryRelationTargetSurjectiveCompactClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW993
    where
  boundaryRelationData := data.boundaryRelationData
  targetSurjectiveCompactData := data.targetSurjectiveCompactData
  closedEmbeddingClosednessData := data.closedEmbeddingClosednessData
  endpointStrictExact :=
    endpointStrictExactOfEndpointLocalizedUnitDataW949
      (endpointLocalizedUnitDataOfTargetSurjectiveCompactNormalizedSourceEndpointW994
        data)
  localizedUnitData :=
    localizedUnitDataOfEndpointLocalizedUnitDataW949
      (endpointLocalizedUnitDataOfTargetSurjectiveCompactNormalizedSourceEndpointW994
        data)
  normalizedSourceTriangulationData :=
    normalizedSourceTriangulationDataOfNormalizedSourceEndpointLocalizedUnitDataW950
      data.normalizedSourceEndpointLocalizedUnitData

/-- W994 constructs W987 full data through W993. -/
def fullDataOfTargetSurjectiveCompactNormalizedSourceEndpointW994
    (data :
      BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfTargetSurjectiveCompactLocalizedUnitChoiceW993
    (localizedUnitChoiceDataOfTargetSurjectiveCompactNormalizedSourceEndpointW994 data)

/- W994 exposes W981 leaves through W993. -/
noncomputable def w981LeavesOfTargetSurjectiveCompactNormalizedSourceEndpointW994
    (data :
      BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w981LeavesOfTargetSurjectiveCompactLocalizedUnitChoiceW993
    (localizedUnitChoiceDataOfTargetSurjectiveCompactNormalizedSourceEndpointW994 data)

/- W994 exposes W971 component fields through W993. -/
noncomputable def componentFieldsOfTargetSurjectiveCompactNormalizedSourceEndpointW994
    (data :
      BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfTargetSurjectiveCompactLocalizedUnitChoiceW993
    (localizedUnitChoiceDataOfTargetSurjectiveCompactNormalizedSourceEndpointW994 data)

/-- W994 reconstructs endpoint strict exactness through W993. -/
noncomputable def endpointStrictExactOfTargetSurjectiveCompactNormalizedSourceEndpointW994
    (data :
      BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfTargetSurjectiveCompactLocalizedUnitChoiceW993
    (localizedUnitChoiceDataOfTargetSurjectiveCompactNormalizedSourceEndpointW994 data)

/-- W994 derives unit mapping-cone algebraic exactness through W993. -/
noncomputable def unitMappingConeAlgebraicExactOfTargetSurjectiveCompactNormalizedSourceEndpointW994
    (data :
      BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ :
        (((componentFieldsOfTargetSurjectiveCompactNormalizedSourceEndpointW994 data).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfTargetSurjectiveCompactNormalizedSourceEndpointW994 data).unitMappingConeModel X).as.sc i).g x₂ =
            0 →
          ∃ x₁ :
            (((componentFieldsOfTargetSurjectiveCompactNormalizedSourceEndpointW994 data).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfTargetSurjectiveCompactNormalizedSourceEndpointW994 data).unitMappingConeModel X).as.sc i).f x₁ =
              x₂ :=
  unitMappingConeAlgebraicExactOfTargetSurjectiveCompactLocalizedUnitChoiceW993
    (localizedUnitChoiceDataOfTargetSurjectiveCompactNormalizedSourceEndpointW994 data)

/-- W994 reconstructs unit mapping-cone strict short exactness through W993. -/
noncomputable def unitMappingConeStrictExactOfTargetSurjectiveCompactNormalizedSourceEndpointW994
    (data :
      BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfTargetSurjectiveCompactNormalizedSourceEndpointW994 data).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfTargetSurjectiveCompactLocalizedUnitChoiceW993
    (localizedUnitChoiceDataOfTargetSurjectiveCompactNormalizedSourceEndpointW994 data)

/-- W994 wraps the unit mapping-cone isomorphism through W993. -/
@[reducible]
noncomputable def unitMappingConeIsoNonemptyOfTargetSurjectiveCompactNormalizedSourceEndpointW994
    (data :
      BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfTargetSurjectiveCompactNormalizedSourceEndpointW994 data).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfTargetSurjectiveCompactNormalizedSourceEndpointW994 data).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfTargetSurjectiveCompactLocalizedUnitChoiceW993
    (localizedUnitChoiceDataOfTargetSurjectiveCompactNormalizedSourceEndpointW994 data)

theorem directBoundedLeftCalculusOfTargetSurjectiveCompactNormalizedSourceEndpointW994
    (data :
      BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfTargetSurjectiveCompactLocalizedUnitChoiceW993
    (localizedUnitChoiceDataOfTargetSurjectiveCompactNormalizedSourceEndpointW994 data)

noncomputable def boundedDerivedInfinityCategoryOfTargetSurjectiveCompactNormalizedSourceEndpointW994
    (data :
      BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfTargetSurjectiveCompactLocalizedUnitChoiceW993
    (localizedUnitChoiceDataOfTargetSurjectiveCompactNormalizedSourceEndpointW994 data)

def targetSurjectiveCompactNormalizedSourceEndpointInputNamesW994 :
    List String :=
  ["W730 boundary/relation data provider",
    "W715 target surjective-compact data provider",
    "W973 closed-embedding closedness data provider",
    "W950 normalized-source/endpoint-localized-unit data provider"]

theorem targetSurjectiveCompactNormalizedSourceEndpointInputNamesW994_count :
    targetSurjectiveCompactNormalizedSourceEndpointInputNamesW994.length = 4 :=
  rfl

structure MetrizableTargetSurjectiveCompactNormalizedSourceEndpointRouteStateW994 :
    Type where
  seed : String
  declarations : List String
  normalizedEndpointProjectionResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetSurjectiveCompactNormalizedSourceEndpointRouteStateW994 :
    MetrizableTargetSurjectiveCompactNormalizedSourceEndpointRouteStateW994
    where
  seed := "w994-target-surjective-compact-normalized-source-endpoint-route"
  declarations :=
    ["BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994",
      "endpointLocalizedUnitDataOfTargetSurjectiveCompactNormalizedSourceEndpointW994",
      "localizedUnitChoiceDataOfTargetSurjectiveCompactNormalizedSourceEndpointW994",
      "fullDataOfTargetSurjectiveCompactNormalizedSourceEndpointW994",
      "w981LeavesOfTargetSurjectiveCompactNormalizedSourceEndpointW994",
      "componentFieldsOfTargetSurjectiveCompactNormalizedSourceEndpointW994",
      "endpointStrictExactOfTargetSurjectiveCompactNormalizedSourceEndpointW994",
      "unitMappingConeAlgebraicExactOfTargetSurjectiveCompactNormalizedSourceEndpointW994",
      "unitMappingConeStrictExactOfTargetSurjectiveCompactNormalizedSourceEndpointW994",
      "unitMappingConeIsoNonemptyOfTargetSurjectiveCompactNormalizedSourceEndpointW994",
      "directBoundedLeftCalculusOfTargetSurjectiveCompactNormalizedSourceEndpointW994",
      "boundedDerivedInfinityCategoryOfTargetSurjectiveCompactNormalizedSourceEndpointW994",
      "targetSurjectiveCompactNormalizedSourceEndpointInputNamesW994_count"]
  normalizedEndpointProjectionResult :=
    "proved: W994 extracts W948 normalized-source-triangulation data, endpoint\
      strict exactness, and W945 localized-unit data from the existing W950\
      normalized-source/endpoint-localized-unit provider"
  exactAtResult :=
    "proved: the W994 target-surjective-compact normalized-source/endpoint\
      surface feeds the W993/W988/W987/W986/W985/W984/W983/W982/W981/W980/\
      W979/W978/W977/W976/W975/W974/W973/W972/W971/W970/W969/W968/W967/\
      W966/W965/W964/W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/\
      W952 stable ExactAt route"
  remainingInputs := targetSurjectiveCompactNormalizedSourceEndpointInputNamesW994
  productSuccessClaimed := false

theorem currentW994TargetSurjectiveCompactNormalizedSourceEndpointRoute_productSuccess :
    (let state :=
        currentMetrizableTargetSurjectiveCompactNormalizedSourceEndpointRouteStateW994;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
