import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromTargetClosedEmbeddingClosednessNormalizedSourceEndpointRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataRoute

/-!
W1007 replaces W1006's remaining separate W730 boundary/relation data and W986
target/closed-embedding-closedness/normalized-source/endpoint-localized data by
the existing W987 branch-specific full-data provider. It unpacks W987 into the
W1006 surface and then delegates through W1006.
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
W1007 provider: the branch-specific W987 full-data boundary that packages W730
boundary/relation data together with W986 target/closedness/normalized-source/
endpoint-localized data.
-/
structure BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :
    Type 2 where
  branchFullData :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987

/-- W1007 projects the W987 branch-specific full-data input. -/
def branchFullDataInputOfBranchFullDataW1007
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  data.branchFullData

/-- W1007 projects W730 boundary/relation data from the W987 input. -/
def boundaryRelationDataOfBranchFullDataW1007
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfFullDataW987
    (branchFullDataInputOfBranchFullDataW1007 data)

/--
W1007 projects W986 target/closedness/normalized-source/endpoint-localized data
from the W987 input.
-/
def targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
    (branchFullDataInputOfBranchFullDataW1007 data)

/-- W1007 builds the W1006 provider surface from the W987 input. -/
def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1007
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006
    where
  boundaryRelationData := boundaryRelationDataOfBranchFullDataW1007 data
  targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitData :=
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007
      data

/-- W1007 projects W984 target/closed-embedding closedness data through W1006. -/
def targetClosedEmbeddingClosednessDataOfBranchFullDataW1007
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    TargetNoUnivClosedEmbeddingClosednessDataProviderW984 :=
  targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1007
      data)

/-- W1007 projects W950 normalized-source/endpoint-localized-unit data through W1006. -/
def normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950 :=
  normalizedSourceEndpointLocalizedUnitDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1007
      data)

/-- W1007 projects W944 target no-univ data through W1006/W1005. -/
def targetNoUnivDataOfBranchFullDataW1007
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944 :=
  targetNoUnivDataOfTargetClosedEmbeddingClosednessW1005
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
      (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1007
        data))

/-- W1007 projects W973 closed-embedding closedness data through W1006/W1005. -/
def closedEmbeddingClosednessDataOfBranchFullDataW1007
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    ClosedEmbeddingClosednessDataProviderW973 :=
  closedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessW1005
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
      (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1007
        data))

/-- W1007 constructs W1004 normalized-source/endpoint-localized data through W1006. -/
def normalizedSourceEndpointLocalizedUnitDataProviderOfBranchFullDataW1007
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1007
      data)

/-- W1007 constructs W1003 endpoint-localized-unit data through W1006. -/
def endpointLocalizedUnitDataProviderOfBranchFullDataW1007
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1007
      data)

/-- W1007 constructs W982 localized-unit-choice data through W1006. -/
def localizedUnitChoiceDataOfBranchFullDataW1007
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1007
      data)

/-- W1007 reconstructs W987 branch full data through W1006. -/
noncomputable def branchFullDataOfBranchFullDataW1007
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1007
      data)

/-- W1007 recovers W715 target surjective-compact data through W1006. -/
noncomputable def targetSurjectiveCompactDataOfBranchFullDataW1007
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1007
      data)

/-- W1007 builds W997's branch-full-data surface through W1006. -/
noncomputable def targetSurjectiveCompactBranchFullDataOfBranchFullDataW1007
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997 :=
  targetSurjectiveCompactBranchFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1007
      data)

/-- W1007 builds the W995 target-provider surface through W1006. -/
noncomputable def targetProviderDataOfBranchFullDataW1007
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995 :=
  targetProviderDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1007
      data)

/-- W1007 builds the W994 normalized-source/endpoint route data through W1006. -/
noncomputable def normalizedSourceEndpointDataOfBranchFullDataW1007
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994 :=
  normalizedSourceEndpointDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1007
      data)

/-- W1007 returns the constructed W987 branch full data through W1006. -/
noncomputable def fullDataOfBranchFullDataW1007
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1007
      data)

/- W1007 exposes W977 leaves through W1006. -/
noncomputable def w977LeavesOfBranchFullDataW1007
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w977LeavesOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1007
      data)

/- W1007 exposes W971 component fields through W1006. -/
noncomputable def componentFieldsOfBranchFullDataW1007
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1007
      data)

/-- W1007 reconstructs endpoint strict short exactness through W1006. -/
noncomputable def endpointStrictExactOfBranchFullDataW1007
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1007
      data)

/-- W1007 derives unit mapping-cone algebraic exactness through W1006. -/
noncomputable def unitMappingConeAlgebraicExactOfBranchFullDataW1007
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ :
        (((componentFieldsOfBranchFullDataW1007 data).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfBranchFullDataW1007 data).unitMappingConeModel X).as.sc i).g x₂ =
            0 →
          ∃ x₁ :
            (((componentFieldsOfBranchFullDataW1007 data).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfBranchFullDataW1007 data).unitMappingConeModel X).as.sc i).f x₁ =
              x₂ :=
  unitMappingConeAlgebraicExactOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1007
      data)

/-- W1007 reconstructs unit mapping-cone strict short exactness through W1006. -/
noncomputable def unitMappingConeStrictExactOfBranchFullDataW1007
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfBranchFullDataW1007 data).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1007
      data)

/-- W1007 wraps the unit mapping-cone isomorphism through W1006. -/
@[reducible]
noncomputable def unitMappingConeIsoNonemptyOfBranchFullDataW1007
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfBranchFullDataW1007 data).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfBranchFullDataW1007 data).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1007
      data)

theorem directBoundedLeftCalculusOfBranchFullDataW1007
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1007
      data)

noncomputable def boundedDerivedInfinityCategoryOfBranchFullDataW1007
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1007
      data)

def branchFullDataInputNamesW1007 : List String :=
  ["W987 branch-specific full-data provider"]

theorem branchFullDataInputNamesW1007_count :
    branchFullDataInputNamesW1007.length = 1 :=
  rfl

structure MetrizableBranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointRouteStateW1007 :
    Type where
  seed : String
  declarations : List String
  branchFullDataProjectionResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableBranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointRouteStateW1007 :
    MetrizableBranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointRouteStateW1007
    where
  seed := "w1007-branch-full-data-to-target-closed-embedding-closedness-normalized-source-endpoint-route"
  declarations :=
    ["BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007",
      "branchFullDataInputOfBranchFullDataW1007",
      "boundaryRelationDataOfBranchFullDataW1007",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1007",
      "targetClosedEmbeddingClosednessDataOfBranchFullDataW1007",
      "normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007",
      "targetNoUnivDataOfBranchFullDataW1007",
      "closedEmbeddingClosednessDataOfBranchFullDataW1007",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfBranchFullDataW1007",
      "endpointLocalizedUnitDataProviderOfBranchFullDataW1007",
      "localizedUnitChoiceDataOfBranchFullDataW1007",
      "branchFullDataOfBranchFullDataW1007",
      "targetSurjectiveCompactDataOfBranchFullDataW1007",
      "targetSurjectiveCompactBranchFullDataOfBranchFullDataW1007",
      "targetProviderDataOfBranchFullDataW1007",
      "normalizedSourceEndpointDataOfBranchFullDataW1007",
      "fullDataOfBranchFullDataW1007",
      "w977LeavesOfBranchFullDataW1007",
      "componentFieldsOfBranchFullDataW1007",
      "endpointStrictExactOfBranchFullDataW1007",
      "unitMappingConeAlgebraicExactOfBranchFullDataW1007",
      "unitMappingConeStrictExactOfBranchFullDataW1007",
      "unitMappingConeIsoNonemptyOfBranchFullDataW1007",
      "directBoundedLeftCalculusOfBranchFullDataW1007",
      "boundedDerivedInfinityCategoryOfBranchFullDataW1007",
      "branchFullDataInputNamesW1007_count"]
  branchFullDataProjectionResult :=
    "proved: W1007 projects W730 boundary/relation data and W986\
      target/closed-embedding-closedness/normalized-source/endpoint-localized\
      data from one W987 branch-specific full-data provider"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1007 rebuilds the W1006 surface from W987 and inherits\
      W1006/W1005/W1004/W1003/W1002/W998 target surjective-compact recovery"
  exactAtResult :=
    "proved: the W1007 W987 branch-specific full-data surface feeds\
      W1006/W1005/W1004/W1003/W1002/W998/W997/W996/W995/W994/W993/W988/\
      W987/W986/W985/W984/W983/W982/W981/W980/W979/W978/W977/W976/W975/\
      W974/W973/W972/W971/W970/W969/W968/W967/W966/W965/W964/W963/W962/\
      W961/W959/W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := branchFullDataInputNamesW1007
  productSuccessClaimed := false

theorem currentW1007BranchFullDataDirectRoute_productSuccess :
    (let state :=
        currentMetrizableBranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointRouteStateW1007;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
