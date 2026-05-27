import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromBranchFullDataDirectRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromCurrentFullDataRoute

/-!
W1008 replaces W1007's W987 branch-specific full-data input by the W977
current full-data provider using the existing W999 W977-to-W987 construction,
then delegates through W1007.
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
W1008 provider: the W977 current full-data boundary that can construct the W987
branch-specific full data through W999.
-/
structure BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :
    Type 2 where
  currentFullData :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977

/-- W1008 projects the W977 current full-data input. -/
def currentFullDataInputOfCurrentFullDataW1008
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  data.currentFullData

/-- W1008 constructs W987 branch full data from W977 through W999. -/
noncomputable def branchFullDataOfCurrentFullDataW1008
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfCurrentFullDataW999
    (currentFullDataInputOfCurrentFullDataW1008 data)

/-- W1008 builds the W1007 provider surface from W977 current full data. -/
noncomputable def branchFullDataProviderOfCurrentFullDataW1008
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007
    where
  branchFullData := branchFullDataOfCurrentFullDataW1008 data

/-- W1008 recovers W730 boundary/relation data through W1007. -/
noncomputable def boundaryRelationDataOfCurrentFullDataW1008
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfBranchFullDataW1007
    (branchFullDataProviderOfCurrentFullDataW1008 data)

/--
W1008 recovers W986 target/closedness/normalized-source/endpoint-localized data
through W1007.
-/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfCurrentFullDataW1008
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007
    (branchFullDataProviderOfCurrentFullDataW1008 data)

/-- W1008 builds the W1006 provider surface through W1007. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1008
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1007
    (branchFullDataProviderOfCurrentFullDataW1008 data)

/-- W1008 projects W984 target/closed-embedding closedness data through W1007. -/
noncomputable def targetClosedEmbeddingClosednessDataOfCurrentFullDataW1008
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    TargetNoUnivClosedEmbeddingClosednessDataProviderW984 :=
  targetClosedEmbeddingClosednessDataOfBranchFullDataW1007
    (branchFullDataProviderOfCurrentFullDataW1008 data)

/-- W1008 projects W950 normalized-source/endpoint-localized-unit data through W1007. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataOfCurrentFullDataW1008
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950 :=
  normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007
    (branchFullDataProviderOfCurrentFullDataW1008 data)

/-- W1008 projects W944 target no-univ data through W1007. -/
noncomputable def targetNoUnivDataOfCurrentFullDataW1008
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944 :=
  targetNoUnivDataOfBranchFullDataW1007
    (branchFullDataProviderOfCurrentFullDataW1008 data)

/-- W1008 projects W973 closed-embedding closedness data through W1007. -/
noncomputable def closedEmbeddingClosednessDataOfCurrentFullDataW1008
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    ClosedEmbeddingClosednessDataProviderW973 :=
  closedEmbeddingClosednessDataOfBranchFullDataW1007
    (branchFullDataProviderOfCurrentFullDataW1008 data)

/-- W1008 constructs W1004 normalized-source/endpoint-localized data through W1007. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1008
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfBranchFullDataW1007
    (branchFullDataProviderOfCurrentFullDataW1008 data)

/-- W1008 constructs W1003 endpoint-localized-unit data through W1007. -/
noncomputable def endpointLocalizedUnitDataProviderOfCurrentFullDataW1008
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfBranchFullDataW1007
    (branchFullDataProviderOfCurrentFullDataW1008 data)

/-- W1008 constructs W982 localized-unit-choice data through W1007. -/
noncomputable def localizedUnitChoiceDataOfCurrentFullDataW1008
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfBranchFullDataW1007
    (branchFullDataProviderOfCurrentFullDataW1008 data)

/-- W1008 recovers W715 target surjective-compact data through W1007. -/
noncomputable def targetSurjectiveCompactDataOfCurrentFullDataW1008
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfBranchFullDataW1007
    (branchFullDataProviderOfCurrentFullDataW1008 data)

/-- W1008 builds W997's branch-full-data surface through W1007. -/
noncomputable def targetSurjectiveCompactBranchFullDataOfCurrentFullDataW1008
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997 :=
  targetSurjectiveCompactBranchFullDataOfBranchFullDataW1007
    (branchFullDataProviderOfCurrentFullDataW1008 data)

/-- W1008 builds the W995 target-provider surface through W1007. -/
noncomputable def targetProviderDataOfCurrentFullDataW1008
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995 :=
  targetProviderDataOfBranchFullDataW1007
    (branchFullDataProviderOfCurrentFullDataW1008 data)

/-- W1008 builds the W994 normalized-source/endpoint route data through W1007. -/
noncomputable def normalizedSourceEndpointDataOfCurrentFullDataW1008
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994 :=
  normalizedSourceEndpointDataOfBranchFullDataW1007
    (branchFullDataProviderOfCurrentFullDataW1008 data)

/-- W1008 returns the constructed W987 branch full data through W1007. -/
noncomputable def fullDataOfCurrentFullDataW1008
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfBranchFullDataW1007
    (branchFullDataProviderOfCurrentFullDataW1008 data)

/- W1008 exposes W977 leaves through W1007. -/
noncomputable def w977LeavesOfCurrentFullDataW1008
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w977LeavesOfBranchFullDataW1007
    (branchFullDataProviderOfCurrentFullDataW1008 data)

/- W1008 exposes W971 component fields through W1007. -/
noncomputable def componentFieldsOfCurrentFullDataW1008
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfBranchFullDataW1007
    (branchFullDataProviderOfCurrentFullDataW1008 data)

/-- W1008 reconstructs endpoint strict short exactness through W1007. -/
noncomputable def endpointStrictExactOfCurrentFullDataW1008
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfBranchFullDataW1007
    (branchFullDataProviderOfCurrentFullDataW1008 data)

/-- W1008 derives unit mapping-cone algebraic exactness through W1007. -/
noncomputable def unitMappingConeAlgebraicExactOfCurrentFullDataW1008
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ :
        (((componentFieldsOfCurrentFullDataW1008 data).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfCurrentFullDataW1008 data).unitMappingConeModel X).as.sc i).g x₂ =
            0 →
          ∃ x₁ :
            (((componentFieldsOfCurrentFullDataW1008 data).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfCurrentFullDataW1008 data).unitMappingConeModel X).as.sc i).f x₁ =
              x₂ :=
  unitMappingConeAlgebraicExactOfBranchFullDataW1007
    (branchFullDataProviderOfCurrentFullDataW1008 data)

/-- W1008 reconstructs unit mapping-cone strict short exactness through W1007. -/
noncomputable def unitMappingConeStrictExactOfCurrentFullDataW1008
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfCurrentFullDataW1008 data).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfBranchFullDataW1007
    (branchFullDataProviderOfCurrentFullDataW1008 data)

/-- W1008 wraps the unit mapping-cone isomorphism through W1007. -/
@[reducible]
noncomputable def unitMappingConeIsoNonemptyOfCurrentFullDataW1008
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfCurrentFullDataW1008 data).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfCurrentFullDataW1008 data).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfBranchFullDataW1007
    (branchFullDataProviderOfCurrentFullDataW1008 data)

theorem directBoundedLeftCalculusOfCurrentFullDataW1008
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfBranchFullDataW1007
    (branchFullDataProviderOfCurrentFullDataW1008 data)

noncomputable def boundedDerivedInfinityCategoryOfCurrentFullDataW1008
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfBranchFullDataW1007
    (branchFullDataProviderOfCurrentFullDataW1008 data)

def currentFullDataInputNamesW1008 : List String :=
  ["W977 current full-data provider"]

theorem currentFullDataInputNamesW1008_count :
    currentFullDataInputNamesW1008.length = 1 :=
  rfl

structure MetrizableCurrentFullDataDirectRouteStateW1008 : Type where
  seed : String
  declarations : List String
  currentFullDataRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableCurrentFullDataDirectRouteStateW1008 :
    MetrizableCurrentFullDataDirectRouteStateW1008
    where
  seed := "w1008-current-full-data-to-w1007-branch-full-data-route"
  declarations :=
    ["BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008",
      "currentFullDataInputOfCurrentFullDataW1008",
      "branchFullDataOfCurrentFullDataW1008",
      "branchFullDataProviderOfCurrentFullDataW1008",
      "boundaryRelationDataOfCurrentFullDataW1008",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfCurrentFullDataW1008",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1008",
      "targetClosedEmbeddingClosednessDataOfCurrentFullDataW1008",
      "normalizedSourceEndpointLocalizedUnitDataOfCurrentFullDataW1008",
      "targetNoUnivDataOfCurrentFullDataW1008",
      "closedEmbeddingClosednessDataOfCurrentFullDataW1008",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1008",
      "endpointLocalizedUnitDataProviderOfCurrentFullDataW1008",
      "localizedUnitChoiceDataOfCurrentFullDataW1008",
      "targetSurjectiveCompactDataOfCurrentFullDataW1008",
      "targetSurjectiveCompactBranchFullDataOfCurrentFullDataW1008",
      "targetProviderDataOfCurrentFullDataW1008",
      "normalizedSourceEndpointDataOfCurrentFullDataW1008",
      "fullDataOfCurrentFullDataW1008",
      "w977LeavesOfCurrentFullDataW1008",
      "componentFieldsOfCurrentFullDataW1008",
      "endpointStrictExactOfCurrentFullDataW1008",
      "unitMappingConeAlgebraicExactOfCurrentFullDataW1008",
      "unitMappingConeStrictExactOfCurrentFullDataW1008",
      "unitMappingConeIsoNonemptyOfCurrentFullDataW1008",
      "directBoundedLeftCalculusOfCurrentFullDataW1008",
      "boundedDerivedInfinityCategoryOfCurrentFullDataW1008",
      "currentFullDataInputNamesW1008_count"]
  currentFullDataRepackagingResult :=
    "proved: W1008 constructs the W1007 W987 branch-full-data surface from\
      W977 current full data using the existing W999 W977-to-W987 route"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1008 feeds W1007 after the W977-to-W987 repackaging and\
      inherits W1007/W1006/W1005/W1004/W1003/W1002/W998 target\
      surjective-compact recovery"
  exactAtResult :=
    "proved: the W1008 W977 current-full-data surface feeds W1007/W1006/\
      W1005/W1004/W1003/W1002/W998/W997/W996/W995/W994/W993/W988/W987/\
      W986/W985/W984/W983/W982/W981/W980/W979/W978/W977/W976/W975/W974/\
      W973/W972/W971/W970/W969/W968/W967/W966/W965/W964/W963/W962/W961/\
      W959/W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := currentFullDataInputNamesW1008
  productSuccessClaimed := false

theorem currentW1008CurrentFullDataDirectRoute_productSuccess :
    (let state := currentMetrizableCurrentFullDataDirectRouteStateW1008;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
