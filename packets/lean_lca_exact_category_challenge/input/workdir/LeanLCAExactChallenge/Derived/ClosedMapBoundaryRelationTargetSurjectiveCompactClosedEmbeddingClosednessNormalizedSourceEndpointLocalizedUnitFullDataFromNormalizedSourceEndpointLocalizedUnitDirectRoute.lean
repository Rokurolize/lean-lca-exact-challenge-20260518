import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromEndpointLocalizedUnitDirectRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromNormalizedSourceEndpointLocalizedUnitRoute

/-!
W1013 replaces W1012's W1003 endpoint-localized-unit surface by the existing
W1004 normalized-source/endpoint-localized-unit surface. W1004 already
constructs W1003, and W1013 feeds that provider into W1012.
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

/-- W1013 constructs the W1003 endpoint-localized-unit surface from W1004 data. -/
def endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1004
    normalizedSourceEndpointLocalizedUnitData

/-- W1013 constructs the W982 localized-unit-choice surface from W1004 through W1012. -/
def localizedUnitChoiceDataOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
      normalizedSourceEndpointLocalizedUnitData)

/-- W1013 constructs the W981 provider surface from W1004 through W1012. -/
noncomputable def unitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
      normalizedSourceEndpointLocalizedUnitData)

/-- W1013 constructs the W971 component-field surface from W1004 through W1012. -/
noncomputable def componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
      normalizedSourceEndpointLocalizedUnitData)

/-- W1013 constructs W977 current full data from W1004 through W1012. -/
noncomputable def currentFullDataOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
      normalizedSourceEndpointLocalizedUnitData)

/-- W1013 builds the W1008 provider surface through W1012. -/
noncomputable def currentFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
      normalizedSourceEndpointLocalizedUnitData)

/-- W1013 constructs W987 branch full data through W1012. -/
noncomputable def branchFullDataOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
      normalizedSourceEndpointLocalizedUnitData)

/-- W1013 builds the W1007 provider surface through W1012. -/
noncomputable def branchFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
      normalizedSourceEndpointLocalizedUnitData)

/-- W1013 recovers W730 boundary/relation data through W1012. -/
noncomputable def boundaryRelationDataOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
      normalizedSourceEndpointLocalizedUnitData)

/-!
W1013 recovers W986 target/closedness/normalized-source/endpoint-localized data
through W1012.
-/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
      normalizedSourceEndpointLocalizedUnitData)

/-- W1013 builds the W1006 provider surface through W1012. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
      normalizedSourceEndpointLocalizedUnitData)

/-- W1013 projects W984 target/closed-embedding closedness data through W1012. -/
noncomputable def targetClosedEmbeddingClosednessDataOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    TargetNoUnivClosedEmbeddingClosednessDataProviderW984 :=
  targetClosedEmbeddingClosednessDataOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
      normalizedSourceEndpointLocalizedUnitData)

/-- W1013 projects W950 normalized-source/endpoint-localized-unit data through W1012. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950 :=
  normalizedSourceEndpointLocalizedUnitDataOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
      normalizedSourceEndpointLocalizedUnitData)

/-- W1013 projects W944 target no-univ data through W1012. -/
noncomputable def targetNoUnivDataOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944 :=
  targetNoUnivDataOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
      normalizedSourceEndpointLocalizedUnitData)

/-- W1013 projects W973 closed-embedding closedness data through W1012. -/
noncomputable def closedEmbeddingClosednessDataOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    ClosedEmbeddingClosednessDataProviderW973 :=
  closedEmbeddingClosednessDataOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
      normalizedSourceEndpointLocalizedUnitData)

/-- W1013 returns W1004 normalized-source/endpoint-localized data through W1012. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
      normalizedSourceEndpointLocalizedUnitData)

/-- W1013 constructs W1003 endpoint-localized-unit data through W1012. -/
noncomputable def endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitRouteW1013
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
      normalizedSourceEndpointLocalizedUnitData)

/-- W1013 recovers W715 target surjective-compact data through W1012. -/
noncomputable def targetSurjectiveCompactDataOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
      normalizedSourceEndpointLocalizedUnitData)

/-- W1013 builds W997's branch-full-data surface through W1012. -/
noncomputable def targetSurjectiveCompactBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997 :=
  targetSurjectiveCompactBranchFullDataOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
      normalizedSourceEndpointLocalizedUnitData)

/-- W1013 builds the W995 target-provider surface through W1012. -/
noncomputable def targetProviderDataOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995 :=
  targetProviderDataOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
      normalizedSourceEndpointLocalizedUnitData)

/-- W1013 builds the W994 normalized-source/endpoint route data through W1012. -/
noncomputable def normalizedSourceEndpointDataOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994 :=
  normalizedSourceEndpointDataOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
      normalizedSourceEndpointLocalizedUnitData)

/-- W1013 returns the constructed W987 branch full data through W1012. -/
noncomputable def fullDataOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
      normalizedSourceEndpointLocalizedUnitData)

/- W1013 exposes W977 leaves through W1012. -/
noncomputable def w977LeavesOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w977LeavesOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
      normalizedSourceEndpointLocalizedUnitData)

/- W1013 exposes W971 component fields through W1012. -/
noncomputable def componentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
      normalizedSourceEndpointLocalizedUnitData)

/-- W1013 reconstructs endpoint strict exactness through W1012. -/
noncomputable def endpointStrictExactOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
      normalizedSourceEndpointLocalizedUnitData)

/-- W1013 derives unit mapping-cone algebraic exactness through W1012. -/
noncomputable def unitMappingConeAlgebraicExactOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ :
        (((componentFieldsOfComponentFieldsW1009
            (componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1013
              normalizedSourceEndpointLocalizedUnitData)).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfComponentFieldsW1009
            (componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1013
              normalizedSourceEndpointLocalizedUnitData)).unitMappingConeModel X).as.sc i).g x₂ =
            0 →
          ∃ x₁ :
            (((componentFieldsOfComponentFieldsW1009
                (componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1013
                  normalizedSourceEndpointLocalizedUnitData)).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfComponentFieldsW1009
                (componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1013
                  normalizedSourceEndpointLocalizedUnitData)).unitMappingConeModel X).as.sc i).f x₁ =
              x₂ :=
  unitMappingConeAlgebraicExactOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
      normalizedSourceEndpointLocalizedUnitData)

/-- W1013 reconstructs unit mapping-cone strict short exactness through W1012. -/
noncomputable def unitMappingConeStrictExactOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfComponentFieldsW1009
            (componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1013
              normalizedSourceEndpointLocalizedUnitData)).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
      normalizedSourceEndpointLocalizedUnitData)

/-- W1013 wraps the unit mapping-cone isomorphism through W1012. -/
@[reducible]
noncomputable def unitMappingConeIsoNonemptyOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfComponentFieldsW1009
                    (componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1013
                      normalizedSourceEndpointLocalizedUnitData)).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfComponentFieldsW1009
            (componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1013
              normalizedSourceEndpointLocalizedUnitData)).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
      normalizedSourceEndpointLocalizedUnitData)

theorem directBoundedLeftCalculusOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
      normalizedSourceEndpointLocalizedUnitData)

noncomputable def boundedDerivedInfinityCategoryOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
      normalizedSourceEndpointLocalizedUnitData)

def normalizedSourceEndpointLocalizedUnitInputNamesW1013 : List String :=
  normalizedSourceEndpointLocalizedUnitInputNamesW1004

theorem normalizedSourceEndpointLocalizedUnitInputNamesW1013_count :
    normalizedSourceEndpointLocalizedUnitInputNamesW1013.length = 4 :=
  normalizedSourceEndpointLocalizedUnitInputNamesW1004_count

structure MetrizableNormalizedSourceEndpointLocalizedUnitDirectRouteStateW1013 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableNormalizedSourceEndpointLocalizedUnitDirectRouteStateW1013 :
    MetrizableNormalizedSourceEndpointLocalizedUnitDirectRouteStateW1013
    where
  seed := "w1013-normalized-source-endpoint-localized-unit-to-w1012-endpoint-localized-unit-route"
  declarations :=
    ["endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013",
      "localizedUnitChoiceDataOfNormalizedSourceEndpointLocalizedUnitW1013",
      "unitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1013",
      "componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1013",
      "currentFullDataOfNormalizedSourceEndpointLocalizedUnitW1013",
      "currentFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013",
      "branchFullDataOfNormalizedSourceEndpointLocalizedUnitW1013",
      "branchFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013",
      "boundaryRelationDataOfNormalizedSourceEndpointLocalizedUnitW1013",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitW1013",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013",
      "targetClosedEmbeddingClosednessDataOfNormalizedSourceEndpointLocalizedUnitW1013",
      "normalizedSourceEndpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitW1013",
      "targetNoUnivDataOfNormalizedSourceEndpointLocalizedUnitW1013",
      "closedEmbeddingClosednessDataOfNormalizedSourceEndpointLocalizedUnitW1013",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013",
      "endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitRouteW1013",
      "targetSurjectiveCompactDataOfNormalizedSourceEndpointLocalizedUnitW1013",
      "targetSurjectiveCompactBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1013",
      "targetProviderDataOfNormalizedSourceEndpointLocalizedUnitW1013",
      "normalizedSourceEndpointDataOfNormalizedSourceEndpointLocalizedUnitW1013",
      "fullDataOfNormalizedSourceEndpointLocalizedUnitW1013",
      "w977LeavesOfNormalizedSourceEndpointLocalizedUnitW1013",
      "componentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1013",
      "endpointStrictExactOfNormalizedSourceEndpointLocalizedUnitW1013",
      "unitMappingConeAlgebraicExactOfNormalizedSourceEndpointLocalizedUnitW1013",
      "unitMappingConeStrictExactOfNormalizedSourceEndpointLocalizedUnitW1013",
      "unitMappingConeIsoNonemptyOfNormalizedSourceEndpointLocalizedUnitW1013",
      "directBoundedLeftCalculusOfNormalizedSourceEndpointLocalizedUnitW1013",
      "boundedDerivedInfinityCategoryOfNormalizedSourceEndpointLocalizedUnitW1013",
      "normalizedSourceEndpointLocalizedUnitInputNamesW1013_count"]
  providerRepackagingResult :=
    "proved: W1013 constructs the W1003 endpoint-localized-unit provider\
      surface from W1004 normalized-source/endpoint-localized-unit data and feeds W1012"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1013 inherits W1012/W1011/W1010/W1009/W1008/W1007/W1006/\
      W1005/W1004/W1003/W1002/W998 target surjective-compact recovery after W1004 constructs W1003"
  exactAtResult :=
    "proved: the W1013 W1004 normalized-source/endpoint-localized-unit provider\
      surface feeds W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/W1004/\
      W1003/W1002/W998/W997/W996/W995/W994/W993/W988/W987/W986/W985/W984/\
      W983/W982/W981/W980/W979/W978/W977/W976/W975/W974/W973/W972/W971/\
      W970/W969/W968/W967/W966/W965/W964/W963/W962/W961/W959/W958/W957/\
      W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := normalizedSourceEndpointLocalizedUnitInputNamesW1013
  productSuccessClaimed := false

theorem currentW1013NormalizedSourceEndpointLocalizedUnitDirectRoute_productSuccess :
    (let state :=
        currentMetrizableNormalizedSourceEndpointLocalizedUnitDirectRouteStateW1013;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
