import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataRoute

/-!
W995 feeds W994 using the existing W986 branch-specific target/closedness/
normalized-source/endpoint provider. This replaces W994's separate W973
closed-embedding closedness data and W950 normalized-source/endpoint-localized
data fields by one W986 input while keeping W715 target surjective-compact data
separate.
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
W995 data surface: W994 with W973 and W950 supplied by the existing W986
branch-specific target/closedness/normalized-source/endpoint provider.
-/
structure BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995 :
    Type 2 where
  boundaryRelationData :
    MetrizableWppBoundaryRelationDataProviderW730
  targetSurjectiveCompactData :
    TargetSurjectiveCompactForTargetProviderW715
  targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitData :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986

/-- W995 projects W986 to its W984 target/closed-embedding-closedness data. -/
def targetClosedEmbeddingClosednessDataOfTargetSurjectiveCompactTargetProviderW995
    (data :
      BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995) :
    TargetNoUnivClosedEmbeddingClosednessDataProviderW984 :=
  targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
    data.targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitData

/-- W995 projects W986/W984 to the W973 closed-embedding closedness provider. -/
def closedEmbeddingClosednessDataOfTargetSurjectiveCompactTargetProviderW995
    (data :
      BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995) :
    ClosedEmbeddingClosednessDataProviderW973 :=
  closedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessDataW984
    (targetClosedEmbeddingClosednessDataOfTargetSurjectiveCompactTargetProviderW995
      data)

/-- W995 projects W986 to the W950 normalized-source/endpoint-localized data. -/
def normalizedSourceEndpointLocalizedUnitDataOfTargetSurjectiveCompactTargetProviderW995
    (data :
      BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995) :
    NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950 :=
  normalizedSourceEndpointLocalizedUnitDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
    data.targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitData

/-- W995 builds the W994 data surface from W730, W715, and W986. -/
def normalizedSourceEndpointDataOfTargetSurjectiveCompactTargetProviderW995
    (data :
      BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995) :
    BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994
    where
  boundaryRelationData := data.boundaryRelationData
  targetSurjectiveCompactData := data.targetSurjectiveCompactData
  closedEmbeddingClosednessData :=
    closedEmbeddingClosednessDataOfTargetSurjectiveCompactTargetProviderW995
      data
  normalizedSourceEndpointLocalizedUnitData :=
    normalizedSourceEndpointLocalizedUnitDataOfTargetSurjectiveCompactTargetProviderW995
      data

/-- W995 constructs W987 full data through W994. -/
def fullDataOfTargetSurjectiveCompactTargetProviderW995
    (data :
      BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfTargetSurjectiveCompactNormalizedSourceEndpointW994
    (normalizedSourceEndpointDataOfTargetSurjectiveCompactTargetProviderW995
      data)

/- W995 exposes W981 leaves through W994. -/
noncomputable def w981LeavesOfTargetSurjectiveCompactTargetProviderW995
    (data :
      BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w981LeavesOfTargetSurjectiveCompactNormalizedSourceEndpointW994
    (normalizedSourceEndpointDataOfTargetSurjectiveCompactTargetProviderW995
      data)

/- W995 exposes W971 component fields through W994. -/
noncomputable def componentFieldsOfTargetSurjectiveCompactTargetProviderW995
    (data :
      BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfTargetSurjectiveCompactNormalizedSourceEndpointW994
    (normalizedSourceEndpointDataOfTargetSurjectiveCompactTargetProviderW995
      data)

/-- W995 reconstructs endpoint strict exactness through W994. -/
noncomputable def endpointStrictExactOfTargetSurjectiveCompactTargetProviderW995
    (data :
      BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfTargetSurjectiveCompactNormalizedSourceEndpointW994
    (normalizedSourceEndpointDataOfTargetSurjectiveCompactTargetProviderW995
      data)

/-- W995 derives unit mapping-cone algebraic exactness through W994. -/
noncomputable def unitMappingConeAlgebraicExactOfTargetSurjectiveCompactTargetProviderW995
    (data :
      BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ :
        (((componentFieldsOfTargetSurjectiveCompactTargetProviderW995 data).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfTargetSurjectiveCompactTargetProviderW995 data).unitMappingConeModel X).as.sc i).g x₂ =
            0 →
          ∃ x₁ :
            (((componentFieldsOfTargetSurjectiveCompactTargetProviderW995 data).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfTargetSurjectiveCompactTargetProviderW995 data).unitMappingConeModel X).as.sc i).f x₁ =
              x₂ :=
  unitMappingConeAlgebraicExactOfTargetSurjectiveCompactNormalizedSourceEndpointW994
    (normalizedSourceEndpointDataOfTargetSurjectiveCompactTargetProviderW995
      data)

/-- W995 reconstructs unit mapping-cone strict short exactness through W994. -/
noncomputable def unitMappingConeStrictExactOfTargetSurjectiveCompactTargetProviderW995
    (data :
      BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfTargetSurjectiveCompactTargetProviderW995 data).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfTargetSurjectiveCompactNormalizedSourceEndpointW994
    (normalizedSourceEndpointDataOfTargetSurjectiveCompactTargetProviderW995
      data)

/-- W995 wraps the unit mapping-cone isomorphism through W994. -/
@[reducible]
noncomputable def unitMappingConeIsoNonemptyOfTargetSurjectiveCompactTargetProviderW995
    (data :
      BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfTargetSurjectiveCompactTargetProviderW995 data).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfTargetSurjectiveCompactTargetProviderW995 data).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfTargetSurjectiveCompactNormalizedSourceEndpointW994
    (normalizedSourceEndpointDataOfTargetSurjectiveCompactTargetProviderW995
      data)

theorem directBoundedLeftCalculusOfTargetSurjectiveCompactTargetProviderW995
    (data :
      BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfTargetSurjectiveCompactNormalizedSourceEndpointW994
    (normalizedSourceEndpointDataOfTargetSurjectiveCompactTargetProviderW995
      data)

noncomputable def boundedDerivedInfinityCategoryOfTargetSurjectiveCompactTargetProviderW995
    (data :
      BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfTargetSurjectiveCompactNormalizedSourceEndpointW994
    (normalizedSourceEndpointDataOfTargetSurjectiveCompactTargetProviderW995
      data)

def targetSurjectiveCompactTargetProviderInputNamesW995 :
    List String :=
  ["W730 boundary/relation data provider",
    "W715 target surjective-compact data provider",
    "W986 target/closed-embedding-closedness/normalized-source/endpoint-localized data provider"]

theorem targetSurjectiveCompactTargetProviderInputNamesW995_count :
    targetSurjectiveCompactTargetProviderInputNamesW995.length = 3 :=
  rfl

structure MetrizableTargetSurjectiveCompactTargetProviderRouteStateW995 :
    Type where
  seed : String
  declarations : List String
  targetProviderProjectionResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetSurjectiveCompactTargetProviderRouteStateW995 :
    MetrizableTargetSurjectiveCompactTargetProviderRouteStateW995
    where
  seed := "w995-target-surjective-compact-target-provider-route"
  declarations :=
    ["BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995",
      "targetClosedEmbeddingClosednessDataOfTargetSurjectiveCompactTargetProviderW995",
      "closedEmbeddingClosednessDataOfTargetSurjectiveCompactTargetProviderW995",
      "normalizedSourceEndpointLocalizedUnitDataOfTargetSurjectiveCompactTargetProviderW995",
      "normalizedSourceEndpointDataOfTargetSurjectiveCompactTargetProviderW995",
      "fullDataOfTargetSurjectiveCompactTargetProviderW995",
      "w981LeavesOfTargetSurjectiveCompactTargetProviderW995",
      "componentFieldsOfTargetSurjectiveCompactTargetProviderW995",
      "endpointStrictExactOfTargetSurjectiveCompactTargetProviderW995",
      "unitMappingConeAlgebraicExactOfTargetSurjectiveCompactTargetProviderW995",
      "unitMappingConeStrictExactOfTargetSurjectiveCompactTargetProviderW995",
      "unitMappingConeIsoNonemptyOfTargetSurjectiveCompactTargetProviderW995",
      "directBoundedLeftCalculusOfTargetSurjectiveCompactTargetProviderW995",
      "boundedDerivedInfinityCategoryOfTargetSurjectiveCompactTargetProviderW995",
      "targetSurjectiveCompactTargetProviderInputNamesW995_count"]
  targetProviderProjectionResult :=
    "proved: W995 extracts W973 closed-embedding closedness data and W950\
      normalized-source/endpoint-localized-unit data from the existing W986\
      branch-specific target/closedness/normalized-source/endpoint provider"
  exactAtResult :=
    "proved: the W995 target-surjective-compact target-provider surface feeds\
      the W994/W993/W988/W987/W986/W985/W984/W983/W982/W981/W980/W979/W978/\
      W977/W976/W975/W974/W973/W972/W971/W970/W969/W968/W967/W966/W965/\
      W964/W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/W952 stable\
      ExactAt route"
  remainingInputs := targetSurjectiveCompactTargetProviderInputNamesW995
  productSuccessClaimed := false

theorem currentW995TargetSurjectiveCompactTargetProviderRoute_productSuccess :
    (let state :=
        currentMetrizableTargetSurjectiveCompactTargetProviderRouteStateW995;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
