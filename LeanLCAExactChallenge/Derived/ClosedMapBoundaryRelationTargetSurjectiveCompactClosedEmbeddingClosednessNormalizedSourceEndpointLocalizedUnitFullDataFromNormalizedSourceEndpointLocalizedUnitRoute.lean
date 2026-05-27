import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromEndpointLocalizedUnitRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataPrimitiveFieldRoute

/-!
W1004 replaces W1003's separate W948 normalized-source-triangulation data and
W949 endpoint-localized-unit data by the existing W950 normalized-source/
endpoint-localized-unit provider. It builds the W1003 endpoint-localized-unit
surface and feeds W1003.
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
W1004 provider: W1003 endpoint-localized-unit data with W948
normalized-source-triangulation data and W949 endpoint-localized-unit data
packaged into one W950 normalized-source/endpoint-localized-unit provider.
-/
structure BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :
    Type 2 where
  boundaryRelationData :
    MetrizableWppBoundaryRelationDataProviderW730
  targetNoUnivData :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944
  closedEmbeddingClosednessData :
    ClosedEmbeddingClosednessDataProviderW973
  normalizedSourceEndpointLocalizedUnitData :
    NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950

/-- W1004 projects W949 endpoint-localized-unit data from W950. -/
def endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitW1004
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    EndpointStrictExactLocalizedUnitDataProviderW949 :=
  endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitDataW950
    data.normalizedSourceEndpointLocalizedUnitData

/-- W1004 projects W948 normalized-source-triangulation data from W950. -/
def normalizedSourceTriangulationDataOfNormalizedSourceEndpointLocalizedUnitW1004
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    NormalizedFixedTargetSourceTriangulationDataProviderW948 :=
  normalizedSourceTriangulationDataOfNormalizedSourceEndpointLocalizedUnitDataW950
    data.normalizedSourceEndpointLocalizedUnitData

/-- W1004 builds the W1003 endpoint-localized-unit surface from W950. -/
def endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1004
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003
    where
  boundaryRelationData := data.boundaryRelationData
  targetNoUnivData := data.targetNoUnivData
  closedEmbeddingClosednessData := data.closedEmbeddingClosednessData
  endpointLocalizedUnitData :=
    endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitW1004 data
  normalizedSourceTriangulationData :=
    normalizedSourceTriangulationDataOfNormalizedSourceEndpointLocalizedUnitW1004 data

/-- W1004 constructs W982 localized-unit-choice data through W1003. -/
def localizedUnitChoiceDataOfNormalizedSourceEndpointLocalizedUnitW1004
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfEndpointLocalizedUnitW1003
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1004 data)

/-- W1004 constructs W987 branch full data through W1003. -/
noncomputable def branchFullDataOfNormalizedSourceEndpointLocalizedUnitW1004
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfEndpointLocalizedUnitW1003
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1004 data)

/-- W1004 recovers W715 target surjective-compact data through W1003. -/
noncomputable def targetSurjectiveCompactDataOfNormalizedSourceEndpointLocalizedUnitW1004
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfEndpointLocalizedUnitW1003
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1004 data)

/-- W1004 builds W997's branch-full-data surface through W1003. -/
noncomputable def targetSurjectiveCompactBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1004
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997
    where
  targetSurjectiveCompactData :=
    targetSurjectiveCompactDataOfNormalizedSourceEndpointLocalizedUnitW1004 data
  branchFullData := branchFullDataOfNormalizedSourceEndpointLocalizedUnitW1004 data

/-- W1004 builds the W995 target-provider surface through W1003. -/
noncomputable def targetProviderDataOfNormalizedSourceEndpointLocalizedUnitW1004
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995 :=
  targetProviderDataOfEndpointLocalizedUnitW1003
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1004 data)

/-- W1004 builds the W994 normalized-source/endpoint route data through W1003. -/
noncomputable def normalizedSourceEndpointDataOfNormalizedSourceEndpointLocalizedUnitW1004
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994 :=
  normalizedSourceEndpointDataOfEndpointLocalizedUnitW1003
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1004 data)

/-- W1004 returns the constructed W987 branch full data through W1003. -/
noncomputable def fullDataOfNormalizedSourceEndpointLocalizedUnitW1004
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfEndpointLocalizedUnitW1003
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1004 data)

/- W1004 exposes W977 leaves through W1003. -/
noncomputable def w977LeavesOfNormalizedSourceEndpointLocalizedUnitW1004
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w977LeavesOfEndpointLocalizedUnitW1003
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1004 data)

/- W1004 exposes W971 component fields through W1003. -/
noncomputable def componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1004
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfEndpointLocalizedUnitW1003
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1004 data)

/-- W1004 reconstructs endpoint strict exactness through W1003. -/
noncomputable def endpointStrictExactOfNormalizedSourceEndpointLocalizedUnitW1004
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfEndpointLocalizedUnitW1003
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1004 data)

/-- W1004 derives unit mapping-cone algebraic exactness through W1003. -/
noncomputable def unitMappingConeAlgebraicExactOfNormalizedSourceEndpointLocalizedUnitW1004
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ :
        (((componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1004 data).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1004 data).unitMappingConeModel X).as.sc i).g x₂ =
            0 →
          ∃ x₁ :
            (((componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1004 data).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1004 data).unitMappingConeModel X).as.sc i).f x₁ =
              x₂ :=
  unitMappingConeAlgebraicExactOfEndpointLocalizedUnitW1003
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1004 data)

/-- W1004 reconstructs unit mapping-cone strict short exactness through W1003. -/
noncomputable def unitMappingConeStrictExactOfNormalizedSourceEndpointLocalizedUnitW1004
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1004 data).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfEndpointLocalizedUnitW1003
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1004 data)

/-- W1004 wraps the unit mapping-cone isomorphism through W1003. -/
@[reducible]
noncomputable def unitMappingConeIsoNonemptyOfNormalizedSourceEndpointLocalizedUnitW1004
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1004 data).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1004 data).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfEndpointLocalizedUnitW1003
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1004 data)

theorem directBoundedLeftCalculusOfNormalizedSourceEndpointLocalizedUnitW1004
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfEndpointLocalizedUnitW1003
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1004 data)

noncomputable def boundedDerivedInfinityCategoryOfNormalizedSourceEndpointLocalizedUnitW1004
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfEndpointLocalizedUnitW1003
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1004 data)

def normalizedSourceEndpointLocalizedUnitInputNamesW1004 : List String :=
  ["W730 boundary/relation data provider",
    "W944 target no-univ data provider",
    "W973 closed-embedding closedness data provider",
    "W950 normalized-source/endpoint-localized-unit data provider"]

theorem normalizedSourceEndpointLocalizedUnitInputNamesW1004_count :
    normalizedSourceEndpointLocalizedUnitInputNamesW1004.length = 4 :=
  rfl

structure MetrizableNormalizedSourceEndpointLocalizedUnitTargetSurjectiveCompactRouteStateW1004 :
    Type where
  seed : String
  declarations : List String
  normalizedSourceEndpointRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableNormalizedSourceEndpointLocalizedUnitTargetSurjectiveCompactRouteStateW1004 :
    MetrizableNormalizedSourceEndpointLocalizedUnitTargetSurjectiveCompactRouteStateW1004
    where
  seed := "w1004-normalized-source-endpoint-localized-unit-to-target-surjective-compact-route"
  declarations :=
    ["BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004",
      "endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitW1004",
      "normalizedSourceTriangulationDataOfNormalizedSourceEndpointLocalizedUnitW1004",
      "endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1004",
      "localizedUnitChoiceDataOfNormalizedSourceEndpointLocalizedUnitW1004",
      "branchFullDataOfNormalizedSourceEndpointLocalizedUnitW1004",
      "targetSurjectiveCompactDataOfNormalizedSourceEndpointLocalizedUnitW1004",
      "targetSurjectiveCompactBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1004",
      "targetProviderDataOfNormalizedSourceEndpointLocalizedUnitW1004",
      "normalizedSourceEndpointDataOfNormalizedSourceEndpointLocalizedUnitW1004",
      "fullDataOfNormalizedSourceEndpointLocalizedUnitW1004",
      "w977LeavesOfNormalizedSourceEndpointLocalizedUnitW1004",
      "componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1004",
      "endpointStrictExactOfNormalizedSourceEndpointLocalizedUnitW1004",
      "unitMappingConeAlgebraicExactOfNormalizedSourceEndpointLocalizedUnitW1004",
      "unitMappingConeStrictExactOfNormalizedSourceEndpointLocalizedUnitW1004",
      "unitMappingConeIsoNonemptyOfNormalizedSourceEndpointLocalizedUnitW1004",
      "directBoundedLeftCalculusOfNormalizedSourceEndpointLocalizedUnitW1004",
      "boundedDerivedInfinityCategoryOfNormalizedSourceEndpointLocalizedUnitW1004",
      "normalizedSourceEndpointLocalizedUnitInputNamesW1004_count"]
  normalizedSourceEndpointRepackagingResult :=
    "proved: W1004 constructs the W1003 endpoint-localized-unit surface from\
      W950 normalized-source/endpoint-localized-unit data"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1004 inherits W1003/W1002/W998 target surjective-compact\
      recovery after W950 supplies W948 normalized-source-triangulation data\
      and W949 endpoint-localized-unit data"
  exactAtResult :=
    "proved: the W1004 W950 normalized-source/endpoint-localized-unit surface\
      feeds W1003/W1002/W998/W997/W996/W995/W994/W993/W988/W987/W986/W985/\
      W984/W983/W982/W981/W980/W979/W978/W977/W976/W975/W974/W973/W972/\
      W971/W970/W969/W968/W967/W966/W965/W964/W963/W962/W961/W959/W958/\
      W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := normalizedSourceEndpointLocalizedUnitInputNamesW1004
  productSuccessClaimed := false

theorem currentW1004NormalizedSourceEndpointLocalizedUnitRoute_productSuccess :
    (let state :=
        currentMetrizableNormalizedSourceEndpointLocalizedUnitTargetSurjectiveCompactRouteStateW1004;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
