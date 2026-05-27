import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataFromTargetProviderRoute

/-!
W996 feeds W995 from W715 target surjective-compact data plus the existing W987
branch-specific full-data provider. This absorbs W995's separate W730 and W986
inputs into one W987 full-data input while keeping W715 as the target-specific
surjective-compact assumption.
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
W996 data surface: W995 with W730 boundary/relation data and W986
target/closedness/normalized-source/endpoint data supplied by W987 full data.
-/
structure BoundaryRelationTargetSurjectiveCompactFullDataProviderW996 :
    Type 2 where
  targetSurjectiveCompactData :
    TargetSurjectiveCompactForTargetProviderW715
  fullData :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987

/-- W996 projects W715 target surjective-compact data. -/
def targetSurjectiveCompactDataOfTargetSurjectiveCompactFullDataW996
    (data : BoundaryRelationTargetSurjectiveCompactFullDataProviderW996) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  data.targetSurjectiveCompactData

/-- W996 projects W730 boundary/relation data through W987. -/
def boundaryRelationDataOfTargetSurjectiveCompactFullDataW996
    (data : BoundaryRelationTargetSurjectiveCompactFullDataProviderW996) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfFullDataW987 data.fullData

/-- W996 projects W986 target/closedness/normalized-source/endpoint data through W987. -/
def targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfTargetSurjectiveCompactFullDataW996
    (data : BoundaryRelationTargetSurjectiveCompactFullDataProviderW996) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
    data.fullData

/-- W996 builds the W995 data surface from W715 and W987. -/
def targetProviderDataOfTargetSurjectiveCompactFullDataW996
    (data : BoundaryRelationTargetSurjectiveCompactFullDataProviderW996) :
    BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995
    where
  boundaryRelationData :=
    boundaryRelationDataOfTargetSurjectiveCompactFullDataW996 data
  targetSurjectiveCompactData :=
    targetSurjectiveCompactDataOfTargetSurjectiveCompactFullDataW996 data
  targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitData :=
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfTargetSurjectiveCompactFullDataW996
      data

/-- W996 constructs the W994 normalized-source/endpoint data through W995. -/
def normalizedSourceEndpointDataOfTargetSurjectiveCompactFullDataW996
    (data : BoundaryRelationTargetSurjectiveCompactFullDataProviderW996) :
    BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994 :=
  normalizedSourceEndpointDataOfTargetSurjectiveCompactTargetProviderW995
    (targetProviderDataOfTargetSurjectiveCompactFullDataW996 data)

/-- W996 constructs W987 full data through W995. -/
def fullDataOfTargetSurjectiveCompactFullDataW996
    (data : BoundaryRelationTargetSurjectiveCompactFullDataProviderW996) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfTargetSurjectiveCompactTargetProviderW995
    (targetProviderDataOfTargetSurjectiveCompactFullDataW996 data)

/- W996 exposes W981 leaves through W995. -/
noncomputable def w981LeavesOfTargetSurjectiveCompactFullDataW996
    (data : BoundaryRelationTargetSurjectiveCompactFullDataProviderW996) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w981LeavesOfTargetSurjectiveCompactTargetProviderW995
    (targetProviderDataOfTargetSurjectiveCompactFullDataW996 data)

/- W996 exposes W971 component fields through W995. -/
noncomputable def componentFieldsOfTargetSurjectiveCompactFullDataW996
    (data : BoundaryRelationTargetSurjectiveCompactFullDataProviderW996) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfTargetSurjectiveCompactTargetProviderW995
    (targetProviderDataOfTargetSurjectiveCompactFullDataW996 data)

/-- W996 reconstructs endpoint strict exactness through W995. -/
noncomputable def endpointStrictExactOfTargetSurjectiveCompactFullDataW996
    (data : BoundaryRelationTargetSurjectiveCompactFullDataProviderW996) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfTargetSurjectiveCompactTargetProviderW995
    (targetProviderDataOfTargetSurjectiveCompactFullDataW996 data)

/-- W996 derives unit mapping-cone algebraic exactness through W995. -/
noncomputable def unitMappingConeAlgebraicExactOfTargetSurjectiveCompactFullDataW996
    (data : BoundaryRelationTargetSurjectiveCompactFullDataProviderW996) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ :
        (((componentFieldsOfTargetSurjectiveCompactFullDataW996 data).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfTargetSurjectiveCompactFullDataW996 data).unitMappingConeModel X).as.sc i).g x₂ =
            0 →
          ∃ x₁ :
            (((componentFieldsOfTargetSurjectiveCompactFullDataW996 data).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfTargetSurjectiveCompactFullDataW996 data).unitMappingConeModel X).as.sc i).f x₁ =
              x₂ :=
  unitMappingConeAlgebraicExactOfTargetSurjectiveCompactTargetProviderW995
    (targetProviderDataOfTargetSurjectiveCompactFullDataW996 data)

/-- W996 reconstructs unit mapping-cone strict short exactness through W995. -/
noncomputable def unitMappingConeStrictExactOfTargetSurjectiveCompactFullDataW996
    (data : BoundaryRelationTargetSurjectiveCompactFullDataProviderW996) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfTargetSurjectiveCompactFullDataW996 data).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfTargetSurjectiveCompactTargetProviderW995
    (targetProviderDataOfTargetSurjectiveCompactFullDataW996 data)

/-- W996 wraps the unit mapping-cone isomorphism through W995. -/
@[reducible]
noncomputable def unitMappingConeIsoNonemptyOfTargetSurjectiveCompactFullDataW996
    (data : BoundaryRelationTargetSurjectiveCompactFullDataProviderW996) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfTargetSurjectiveCompactFullDataW996 data).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfTargetSurjectiveCompactFullDataW996 data).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfTargetSurjectiveCompactTargetProviderW995
    (targetProviderDataOfTargetSurjectiveCompactFullDataW996 data)

theorem directBoundedLeftCalculusOfTargetSurjectiveCompactFullDataW996
    (data : BoundaryRelationTargetSurjectiveCompactFullDataProviderW996) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfTargetSurjectiveCompactTargetProviderW995
    (targetProviderDataOfTargetSurjectiveCompactFullDataW996 data)

noncomputable def boundedDerivedInfinityCategoryOfTargetSurjectiveCompactFullDataW996
    (data : BoundaryRelationTargetSurjectiveCompactFullDataProviderW996) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfTargetSurjectiveCompactTargetProviderW995
    (targetProviderDataOfTargetSurjectiveCompactFullDataW996 data)

def targetSurjectiveCompactFullDataInputNamesW996 :
    List String :=
  ["W715 target surjective-compact data provider",
    "W987 boundary-relation/target-closed-embedding-closedness/normalized-source/endpoint-localized full-data provider"]

theorem targetSurjectiveCompactFullDataInputNamesW996_count :
    targetSurjectiveCompactFullDataInputNamesW996.length = 2 :=
  rfl

structure MetrizableTargetSurjectiveCompactFullDataRouteStateW996 :
    Type where
  seed : String
  declarations : List String
  fullDataProjectionResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetSurjectiveCompactFullDataRouteStateW996 :
    MetrizableTargetSurjectiveCompactFullDataRouteStateW996
    where
  seed := "w996-target-surjective-compact-full-data-route"
  declarations :=
    ["BoundaryRelationTargetSurjectiveCompactFullDataProviderW996",
      "targetSurjectiveCompactDataOfTargetSurjectiveCompactFullDataW996",
      "boundaryRelationDataOfTargetSurjectiveCompactFullDataW996",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfTargetSurjectiveCompactFullDataW996",
      "targetProviderDataOfTargetSurjectiveCompactFullDataW996",
      "normalizedSourceEndpointDataOfTargetSurjectiveCompactFullDataW996",
      "fullDataOfTargetSurjectiveCompactFullDataW996",
      "w981LeavesOfTargetSurjectiveCompactFullDataW996",
      "componentFieldsOfTargetSurjectiveCompactFullDataW996",
      "endpointStrictExactOfTargetSurjectiveCompactFullDataW996",
      "unitMappingConeAlgebraicExactOfTargetSurjectiveCompactFullDataW996",
      "unitMappingConeStrictExactOfTargetSurjectiveCompactFullDataW996",
      "unitMappingConeIsoNonemptyOfTargetSurjectiveCompactFullDataW996",
      "directBoundedLeftCalculusOfTargetSurjectiveCompactFullDataW996",
      "boundedDerivedInfinityCategoryOfTargetSurjectiveCompactFullDataW996",
      "targetSurjectiveCompactFullDataInputNamesW996_count"]
  fullDataProjectionResult :=
    "proved: W996 extracts W730 boundary/relation data and W986\
      target/closed-embedding-closedness/normalized-source/endpoint-localized\
      data from W987 full data, then combines them with W715 target\
      surjective-compact data for W995"
  exactAtResult :=
    "proved: the W996 target-surjective-compact full-data surface feeds the\
      W995/W994/W993/W988/W987/W986/W985/W984/W983/W982/W981/W980/W979/\
      W978/W977/W976/W975/W974/W973/W972/W971/W970/W969/W968/W967/W966/\
      W965/W964/W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/W952\
      stable ExactAt route"
  remainingInputs := targetSurjectiveCompactFullDataInputNamesW996
  productSuccessClaimed := false

theorem currentW996TargetSurjectiveCompactFullDataRoute_productSuccess :
    (let state :=
        currentMetrizableTargetSurjectiveCompactFullDataRouteStateW996;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
