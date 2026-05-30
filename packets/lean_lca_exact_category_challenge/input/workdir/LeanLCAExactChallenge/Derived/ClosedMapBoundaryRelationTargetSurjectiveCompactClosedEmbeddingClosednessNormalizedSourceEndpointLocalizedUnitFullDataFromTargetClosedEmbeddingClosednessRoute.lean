import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromNormalizedSourceEndpointLocalizedUnitRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessEndpointLocalizedUnitChoiceDataRoute

/-!
W1005 replaces W1004's separate W944 target no-univ data and W973
closed-embedding closedness data by the existing W984 target/closed-embedding
closedness provider. It builds the W1004 normalized-source/endpoint-localized
surface and feeds W1004.
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
W1005 provider: W1004 normalized-source/endpoint-localized-unit data with W944
target no-univ data and W973 closed-embedding closedness data packaged into
one W984 target/closed-embedding closedness provider.
-/
structure BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :
    Type 2 where
  boundaryRelationData :
    MetrizableWppBoundaryRelationDataProviderW730
  targetClosedEmbeddingClosednessData :
    TargetNoUnivClosedEmbeddingClosednessDataProviderW984
  normalizedSourceEndpointLocalizedUnitData :
    NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950

/-- W1005 projects W944 target no-univ data from W984. -/
def targetNoUnivDataOfTargetClosedEmbeddingClosednessW1005
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944 :=
  targetNoUnivDataOfTargetClosedEmbeddingClosednessDataW984
    data.targetClosedEmbeddingClosednessData

/-- W1005 projects W973 closed-embedding closedness data from W984. -/
def closedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessW1005
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    ClosedEmbeddingClosednessDataProviderW973 :=
  closedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessDataW984
    data.targetClosedEmbeddingClosednessData

/-- W1005 builds the W1004 normalized-source/endpoint-localized surface from W984. -/
def normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1005
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004
    where
  boundaryRelationData := data.boundaryRelationData
  targetNoUnivData :=
    targetNoUnivDataOfTargetClosedEmbeddingClosednessW1005 data
  closedEmbeddingClosednessData :=
    closedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessW1005 data
  normalizedSourceEndpointLocalizedUnitData :=
    data.normalizedSourceEndpointLocalizedUnitData

/-- W1005 constructs W1003 endpoint-localized-unit data through W1004. -/
def endpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1005
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1004
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1005
      data)

/-- W1005 constructs W982 localized-unit-choice data through W1004. -/
def localizedUnitChoiceDataOfTargetClosedEmbeddingClosednessW1005
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfNormalizedSourceEndpointLocalizedUnitW1004
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1005
      data)

/-- W1005 constructs W987 branch full data through W1004. -/
noncomputable def branchFullDataOfTargetClosedEmbeddingClosednessW1005
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfNormalizedSourceEndpointLocalizedUnitW1004
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1005
      data)

/-- W1005 recovers W715 target surjective-compact data through W1004. -/
noncomputable def targetSurjectiveCompactDataOfTargetClosedEmbeddingClosednessW1005
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfNormalizedSourceEndpointLocalizedUnitW1004
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1005
      data)

/-- W1005 builds W997's branch-full-data surface through W1004. -/
noncomputable def targetSurjectiveCompactBranchFullDataOfTargetClosedEmbeddingClosednessW1005
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997
    where
  targetSurjectiveCompactData :=
    targetSurjectiveCompactDataOfTargetClosedEmbeddingClosednessW1005 data
  branchFullData := branchFullDataOfTargetClosedEmbeddingClosednessW1005 data

/-- W1005 builds the W995 target-provider surface through W1004. -/
noncomputable def targetProviderDataOfTargetClosedEmbeddingClosednessW1005
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995 :=
  targetProviderDataOfNormalizedSourceEndpointLocalizedUnitW1004
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1005
      data)

/-- W1005 builds the W994 normalized-source/endpoint route data through W1004. -/
noncomputable def normalizedSourceEndpointDataOfTargetClosedEmbeddingClosednessW1005
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994 :=
  normalizedSourceEndpointDataOfNormalizedSourceEndpointLocalizedUnitW1004
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1005
      data)

/-- W1005 returns the constructed W987 branch full data through W1004. -/
noncomputable def fullDataOfTargetClosedEmbeddingClosednessW1005
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfNormalizedSourceEndpointLocalizedUnitW1004
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1005
      data)

/- W1005 exposes W977 leaves through W1004. -/
noncomputable def w977LeavesOfTargetClosedEmbeddingClosednessW1005
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w977LeavesOfNormalizedSourceEndpointLocalizedUnitW1004
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1005
      data)

/- W1005 exposes W971 component fields through W1004. -/
noncomputable def componentFieldsOfTargetClosedEmbeddingClosednessW1005
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1004
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1005
      data)

/-- W1005 reconstructs endpoint strict exactness through W1004. -/
noncomputable def endpointStrictExactOfTargetClosedEmbeddingClosednessW1005
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfNormalizedSourceEndpointLocalizedUnitW1004
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1005
      data)

/-- W1005 derives unit mapping-cone algebraic exactness through W1004. -/
noncomputable def unitMappingConeAlgebraicExactOfTargetClosedEmbeddingClosednessW1005
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ :
        (((componentFieldsOfTargetClosedEmbeddingClosednessW1005 data).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfTargetClosedEmbeddingClosednessW1005 data).unitMappingConeModel X).as.sc i).g x₂ =
            0 →
          ∃ x₁ :
            (((componentFieldsOfTargetClosedEmbeddingClosednessW1005 data).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfTargetClosedEmbeddingClosednessW1005 data).unitMappingConeModel X).as.sc i).f x₁ =
              x₂ :=
  unitMappingConeAlgebraicExactOfNormalizedSourceEndpointLocalizedUnitW1004
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1005
      data)

/-- W1005 reconstructs unit mapping-cone strict short exactness through W1004. -/
noncomputable def unitMappingConeStrictExactOfTargetClosedEmbeddingClosednessW1005
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfTargetClosedEmbeddingClosednessW1005 data).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfNormalizedSourceEndpointLocalizedUnitW1004
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1005
      data)

/-- W1005 wraps the unit mapping-cone isomorphism through W1004. -/
@[reducible]
noncomputable def unitMappingConeIsoNonemptyOfTargetClosedEmbeddingClosednessW1005
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfTargetClosedEmbeddingClosednessW1005 data).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfTargetClosedEmbeddingClosednessW1005 data).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfNormalizedSourceEndpointLocalizedUnitW1004
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1005
      data)

theorem directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessW1005
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfNormalizedSourceEndpointLocalizedUnitW1004
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1005
      data)

noncomputable def boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessW1005
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfNormalizedSourceEndpointLocalizedUnitW1004
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1005
      data)

def targetClosedEmbeddingClosednessInputNamesW1005 : List String :=
  ["W730 boundary/relation data provider",
    "W984 target no-univ plus closed-embedding closedness data provider",
    "W950 normalized-source/endpoint-localized-unit data provider"]

theorem targetClosedEmbeddingClosednessInputNamesW1005_count :
    targetClosedEmbeddingClosednessInputNamesW1005.length = 3 :=
  rfl

structure MetrizableTargetClosedEmbeddingClosednessTargetSurjectiveCompactRouteStateW1005 :
    Type where
  seed : String
  declarations : List String
  targetClosednessRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetClosedEmbeddingClosednessTargetSurjectiveCompactRouteStateW1005 :
    MetrizableTargetClosedEmbeddingClosednessTargetSurjectiveCompactRouteStateW1005
    where
  seed := "w1005-target-closed-embedding-closedness-to-target-surjective-compact-route"
  declarations :=
    ["BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005",
      "targetNoUnivDataOfTargetClosedEmbeddingClosednessW1005",
      "closedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessW1005",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1005",
      "endpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1005",
      "localizedUnitChoiceDataOfTargetClosedEmbeddingClosednessW1005",
      "branchFullDataOfTargetClosedEmbeddingClosednessW1005",
      "targetSurjectiveCompactDataOfTargetClosedEmbeddingClosednessW1005",
      "targetSurjectiveCompactBranchFullDataOfTargetClosedEmbeddingClosednessW1005",
      "targetProviderDataOfTargetClosedEmbeddingClosednessW1005",
      "normalizedSourceEndpointDataOfTargetClosedEmbeddingClosednessW1005",
      "fullDataOfTargetClosedEmbeddingClosednessW1005",
      "w977LeavesOfTargetClosedEmbeddingClosednessW1005",
      "componentFieldsOfTargetClosedEmbeddingClosednessW1005",
      "endpointStrictExactOfTargetClosedEmbeddingClosednessW1005",
      "unitMappingConeAlgebraicExactOfTargetClosedEmbeddingClosednessW1005",
      "unitMappingConeStrictExactOfTargetClosedEmbeddingClosednessW1005",
      "unitMappingConeIsoNonemptyOfTargetClosedEmbeddingClosednessW1005",
      "directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessW1005",
      "boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessW1005",
      "targetClosedEmbeddingClosednessInputNamesW1005_count"]
  targetClosednessRepackagingResult :=
    "proved: W1005 constructs the W1004 normalized-source/endpoint-localized\
      surface from W984 target/closed-embedding closedness data"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1005 inherits W1004/W1003/W1002/W998 target surjective-compact\
      recovery after W984 supplies W944 target no-univ data and W973\
      closed-embedding closedness data"
  exactAtResult :=
    "proved: the W1005 W984 target/closed-embedding-closedness surface feeds\
      W1004/W1003/W1002/W998/W997/W996/W995/W994/W993/W988/W987/W986/W985/\
      W984/W983/W982/W981/W980/W979/W978/W977/W976/W975/W974/W973/W972/\
      W971/W970/W969/W968/W967/W966/W965/W964/W963/W962/W961/W959/W958/\
      W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := targetClosedEmbeddingClosednessInputNamesW1005
  productSuccessClaimed := false

theorem currentW1005TargetClosedEmbeddingClosednessRoute_productSuccess :
    (let state :=
        currentMetrizableTargetClosedEmbeddingClosednessTargetSurjectiveCompactRouteStateW1005;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
