import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromLocalizedUnitChoiceRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataPrimitiveFieldRoute

/-!
W1003 replaces W1002's separate endpoint strict-exact family and W945
localized-unit data by the existing W949 endpoint-localized-unit provider.
It builds the W982 localized-unit-choice surface and feeds W1002.
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
W1003 provider: W982 localized-unit-choice data with endpoint strict exactness
and W945 localized-unit data packaged into one W949 endpoint-localized-unit
provider.
-/
structure BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :
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

/-- W1003 builds W982 localized-unit-choice data from W949 endpoint-localized-unit data. -/
def localizedUnitChoiceDataOfEndpointLocalizedUnitW1003
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982
    where
  boundaryRelationData := data.boundaryRelationData
  targetNoUnivData := data.targetNoUnivData
  closedEmbeddingClosednessData := data.closedEmbeddingClosednessData
  endpointStrictExact :=
    endpointStrictExactOfEndpointLocalizedUnitDataW949
      data.endpointLocalizedUnitData
  localizedUnitData :=
    localizedUnitDataOfEndpointLocalizedUnitDataW949
      data.endpointLocalizedUnitData
  normalizedSourceTriangulationData := data.normalizedSourceTriangulationData

/-- W1003 constructs W987 branch full data through W1002. -/
noncomputable def branchFullDataOfEndpointLocalizedUnitW1003
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfLocalizedUnitChoiceW1002
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1003 data)

/-- W1003 recovers W715 target surjective-compact data through W1002. -/
noncomputable def targetSurjectiveCompactDataOfEndpointLocalizedUnitW1003
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfLocalizedUnitChoiceW1002
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1003 data)

/-- W1003 builds W997's branch-full-data surface from W949 endpoint-localized data. -/
noncomputable def targetSurjectiveCompactBranchFullDataOfEndpointLocalizedUnitW1003
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997
    where
  targetSurjectiveCompactData :=
    targetSurjectiveCompactDataOfEndpointLocalizedUnitW1003 data
  branchFullData := branchFullDataOfEndpointLocalizedUnitW1003 data

/-- W1003 builds the W995 target-provider surface through W1002. -/
noncomputable def targetProviderDataOfEndpointLocalizedUnitW1003
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995 :=
  targetProviderDataOfLocalizedUnitChoiceW1002
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1003 data)

/-- W1003 builds the W994 normalized-source/endpoint route data through W1002. -/
noncomputable def normalizedSourceEndpointDataOfEndpointLocalizedUnitW1003
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994 :=
  normalizedSourceEndpointDataOfLocalizedUnitChoiceW1002
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1003 data)

/-- W1003 returns the constructed W987 branch full data through W1002. -/
noncomputable def fullDataOfEndpointLocalizedUnitW1003
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfLocalizedUnitChoiceW1002
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1003 data)

/- W1003 exposes W977 leaves through W1002. -/
noncomputable def w977LeavesOfEndpointLocalizedUnitW1003
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w977LeavesOfLocalizedUnitChoiceW1002
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1003 data)

/- W1003 exposes W971 component fields through W1002. -/
noncomputable def componentFieldsOfEndpointLocalizedUnitW1003
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfLocalizedUnitChoiceW1002
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1003 data)

/-- W1003 reconstructs endpoint strict exactness through W1002. -/
noncomputable def endpointStrictExactOfEndpointLocalizedUnitW1003
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfLocalizedUnitChoiceW1002
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1003 data)

/-- W1003 derives unit mapping-cone algebraic exactness through W1002. -/
noncomputable def unitMappingConeAlgebraicExactOfEndpointLocalizedUnitW1003
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ :
        (((componentFieldsOfEndpointLocalizedUnitW1003 data).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfEndpointLocalizedUnitW1003 data).unitMappingConeModel X).as.sc i).g x₂ =
            0 →
          ∃ x₁ :
            (((componentFieldsOfEndpointLocalizedUnitW1003 data).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfEndpointLocalizedUnitW1003 data).unitMappingConeModel X).as.sc i).f x₁ =
              x₂ :=
  unitMappingConeAlgebraicExactOfLocalizedUnitChoiceW1002
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1003 data)

/-- W1003 reconstructs unit mapping-cone strict short exactness through W1002. -/
noncomputable def unitMappingConeStrictExactOfEndpointLocalizedUnitW1003
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfEndpointLocalizedUnitW1003 data).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfLocalizedUnitChoiceW1002
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1003 data)

/-- W1003 wraps the unit mapping-cone isomorphism through W1002. -/
@[reducible]
noncomputable def unitMappingConeIsoNonemptyOfEndpointLocalizedUnitW1003
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfEndpointLocalizedUnitW1003 data).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfEndpointLocalizedUnitW1003 data).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfLocalizedUnitChoiceW1002
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1003 data)

theorem directBoundedLeftCalculusOfEndpointLocalizedUnitW1003
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfLocalizedUnitChoiceW1002
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1003 data)

noncomputable def boundedDerivedInfinityCategoryOfEndpointLocalizedUnitW1003
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfLocalizedUnitChoiceW1002
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1003 data)

def endpointLocalizedUnitInputNamesW1003 : List String :=
  ["W730 boundary/relation data provider",
    "W944 target no-univ data provider",
    "W973 closed-embedding closedness data provider",
    "W949 endpoint-localized-unit data provider",
    "W948 normalized-source-triangulation data provider"]

theorem endpointLocalizedUnitInputNamesW1003_count :
    endpointLocalizedUnitInputNamesW1003.length = 5 :=
  rfl

structure MetrizableEndpointLocalizedUnitTargetSurjectiveCompactRouteStateW1003 :
    Type where
  seed : String
  declarations : List String
  endpointLocalizedUnitRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableEndpointLocalizedUnitTargetSurjectiveCompactRouteStateW1003 :
    MetrizableEndpointLocalizedUnitTargetSurjectiveCompactRouteStateW1003
    where
  seed := "w1003-endpoint-localized-unit-to-target-surjective-compact-route"
  declarations :=
    ["BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003",
      "localizedUnitChoiceDataOfEndpointLocalizedUnitW1003",
      "branchFullDataOfEndpointLocalizedUnitW1003",
      "targetSurjectiveCompactDataOfEndpointLocalizedUnitW1003",
      "targetSurjectiveCompactBranchFullDataOfEndpointLocalizedUnitW1003",
      "targetProviderDataOfEndpointLocalizedUnitW1003",
      "normalizedSourceEndpointDataOfEndpointLocalizedUnitW1003",
      "fullDataOfEndpointLocalizedUnitW1003",
      "w977LeavesOfEndpointLocalizedUnitW1003",
      "componentFieldsOfEndpointLocalizedUnitW1003",
      "endpointStrictExactOfEndpointLocalizedUnitW1003",
      "unitMappingConeAlgebraicExactOfEndpointLocalizedUnitW1003",
      "unitMappingConeStrictExactOfEndpointLocalizedUnitW1003",
      "unitMappingConeIsoNonemptyOfEndpointLocalizedUnitW1003",
      "directBoundedLeftCalculusOfEndpointLocalizedUnitW1003",
      "boundedDerivedInfinityCategoryOfEndpointLocalizedUnitW1003",
      "endpointLocalizedUnitInputNamesW1003_count"]
  endpointLocalizedUnitRepackagingResult :=
    "proved: W1003 constructs W982 localized-unit-choice data from W949\
      endpoint-localized-unit data and feeds W1002"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1003 inherits W1002/W998 target surjective-compact recovery\
      after W949 supplies endpoint strict exactness and W945 localized-unit data"
  exactAtResult :=
    "proved: the W1003 W949 endpoint-localized-unit surface feeds W1002/\
      W998/W997/W996/W995/W994/W993/W988/W987/W986/W985/W984/W983/W982/\
      W981/W980/W979/W978/W977/W976/W975/W974/W973/W972/W971/W970/W969/\
      W968/W967/W966/W965/W964/W963/W962/W961/W959/W958/W957/W956/W955/\
      W954/W953/W952 stable ExactAt route"
  remainingInputs := endpointLocalizedUnitInputNamesW1003
  productSuccessClaimed := false

theorem currentW1003EndpointLocalizedUnitRoute_productSuccess :
    (let state :=
        currentMetrizableEndpointLocalizedUnitTargetSurjectiveCompactRouteStateW1003;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
