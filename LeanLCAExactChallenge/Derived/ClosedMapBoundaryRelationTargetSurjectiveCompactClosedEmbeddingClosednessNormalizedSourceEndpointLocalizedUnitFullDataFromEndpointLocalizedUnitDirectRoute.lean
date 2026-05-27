import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromLocalizedUnitChoiceDirectRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromEndpointLocalizedUnitRoute

/-!
W1012 replaces W1011's W982 localized-unit-choice surface by the existing W1003
endpoint-localized-unit surface. W1003 already constructs W982, and W1012 feeds
that provider into W1011.
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

/-- W1012 constructs the W982 localized-unit-choice surface from W1003 data. -/
def localizedUnitChoiceDataOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfEndpointLocalizedUnitW1003 endpointLocalizedUnitData

/-- W1012 constructs the W981 provider surface from W1003 through W1011. -/
noncomputable def unitStrictExactIsoDataOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)

/-- W1012 constructs the W971 component-field surface from W1003 through W1011. -/
noncomputable def componentFieldsOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)

/-- W1012 constructs W977 current full data from W1003 through W1011. -/
noncomputable def currentFullDataOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)

/-- W1012 builds the W1008 provider surface through W1011. -/
noncomputable def currentFullDataProviderOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)

/-- W1012 constructs W987 branch full data through W1011. -/
noncomputable def branchFullDataOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)

/-- W1012 builds the W1007 provider surface through W1011. -/
noncomputable def branchFullDataProviderOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)

/-- W1012 recovers W730 boundary/relation data through W1011. -/
noncomputable def boundaryRelationDataOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)

/-!
W1012 recovers W986 target/closedness/normalized-source/endpoint-localized data
through W1011.
-/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)

/-- W1012 builds the W1006 provider surface through W1011. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)

/-- W1012 projects W984 target/closed-embedding closedness data through W1011. -/
noncomputable def targetClosedEmbeddingClosednessDataOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    TargetNoUnivClosedEmbeddingClosednessDataProviderW984 :=
  targetClosedEmbeddingClosednessDataOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)

/-- W1012 projects W950 normalized-source/endpoint-localized-unit data through W1011. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950 :=
  normalizedSourceEndpointLocalizedUnitDataOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)

/-- W1012 projects W944 target no-univ data through W1011. -/
noncomputable def targetNoUnivDataOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944 :=
  targetNoUnivDataOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)

/-- W1012 projects W973 closed-embedding closedness data through W1011. -/
noncomputable def closedEmbeddingClosednessDataOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    ClosedEmbeddingClosednessDataProviderW973 :=
  closedEmbeddingClosednessDataOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)

/-- W1012 constructs W1004 normalized-source/endpoint-localized data through W1011. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)

/-- W1012 returns W1003 endpoint-localized-unit data through W1011. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)

/-- W1012 recovers W715 target surjective-compact data through W1011. -/
noncomputable def targetSurjectiveCompactDataOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)

/-- W1012 builds W997's branch-full-data surface through W1011. -/
noncomputable def targetSurjectiveCompactBranchFullDataOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997 :=
  targetSurjectiveCompactBranchFullDataOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)

/-- W1012 builds the W995 target-provider surface through W1011. -/
noncomputable def targetProviderDataOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995 :=
  targetProviderDataOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)

/-- W1012 builds the W994 normalized-source/endpoint route data through W1011. -/
noncomputable def normalizedSourceEndpointDataOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994 :=
  normalizedSourceEndpointDataOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)

/-- W1012 returns the constructed W987 branch full data through W1011. -/
noncomputable def fullDataOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)

/- W1012 exposes W977 leaves through W1011. -/
noncomputable def w977LeavesOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w977LeavesOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)

/- W1012 exposes W971 component fields through W1011. -/
noncomputable def componentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)

/-- W1012 reconstructs endpoint strict exactness through W1011. -/
noncomputable def endpointStrictExactOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)

/-- W1012 derives unit mapping-cone algebraic exactness through W1011. -/
noncomputable def unitMappingConeAlgebraicExactOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ :
        (((componentFieldsOfComponentFieldsW1009
            (componentFieldsOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfComponentFieldsW1009
            (componentFieldsOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)).unitMappingConeModel X).as.sc i).g x₂ =
            0 →
          ∃ x₁ :
            (((componentFieldsOfComponentFieldsW1009
                (componentFieldsOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfComponentFieldsW1009
                (componentFieldsOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)).unitMappingConeModel X).as.sc i).f x₁ =
              x₂ :=
  unitMappingConeAlgebraicExactOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)

/-- W1012 reconstructs unit mapping-cone strict short exactness through W1011. -/
noncomputable def unitMappingConeStrictExactOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfComponentFieldsW1009
            (componentFieldsOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)

/-- W1012 wraps the unit mapping-cone isomorphism through W1011. -/
@[reducible]
noncomputable def unitMappingConeIsoNonemptyOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfComponentFieldsW1009
                    (componentFieldsOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfComponentFieldsW1009
            (componentFieldsOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)

theorem directBoundedLeftCalculusOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)

noncomputable def boundedDerivedInfinityCategoryOfEndpointLocalizedUnitW1012
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData)

def endpointLocalizedUnitInputNamesW1012 : List String :=
  endpointLocalizedUnitInputNamesW1003

theorem endpointLocalizedUnitInputNamesW1012_count :
    endpointLocalizedUnitInputNamesW1012.length = 5 :=
  endpointLocalizedUnitInputNamesW1003_count

structure MetrizableEndpointLocalizedUnitDirectRouteStateW1012 : Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableEndpointLocalizedUnitDirectRouteStateW1012 :
    MetrizableEndpointLocalizedUnitDirectRouteStateW1012
    where
  seed := "w1012-endpoint-localized-unit-to-w1011-localized-unit-choice-route"
  declarations :=
    ["localizedUnitChoiceDataOfEndpointLocalizedUnitW1012",
      "unitStrictExactIsoDataOfEndpointLocalizedUnitW1012",
      "componentFieldsOfEndpointLocalizedUnitW1012",
      "currentFullDataOfEndpointLocalizedUnitW1012",
      "currentFullDataProviderOfEndpointLocalizedUnitW1012",
      "branchFullDataOfEndpointLocalizedUnitW1012",
      "branchFullDataProviderOfEndpointLocalizedUnitW1012",
      "boundaryRelationDataOfEndpointLocalizedUnitW1012",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfEndpointLocalizedUnitW1012",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfEndpointLocalizedUnitW1012",
      "targetClosedEmbeddingClosednessDataOfEndpointLocalizedUnitW1012",
      "normalizedSourceEndpointLocalizedUnitDataOfEndpointLocalizedUnitW1012",
      "targetNoUnivDataOfEndpointLocalizedUnitW1012",
      "closedEmbeddingClosednessDataOfEndpointLocalizedUnitW1012",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1012",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1012",
      "targetSurjectiveCompactDataOfEndpointLocalizedUnitW1012",
      "targetSurjectiveCompactBranchFullDataOfEndpointLocalizedUnitW1012",
      "targetProviderDataOfEndpointLocalizedUnitW1012",
      "normalizedSourceEndpointDataOfEndpointLocalizedUnitW1012",
      "fullDataOfEndpointLocalizedUnitW1012",
      "w977LeavesOfEndpointLocalizedUnitW1012",
      "componentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1012",
      "endpointStrictExactOfEndpointLocalizedUnitW1012",
      "unitMappingConeAlgebraicExactOfEndpointLocalizedUnitW1012",
      "unitMappingConeStrictExactOfEndpointLocalizedUnitW1012",
      "unitMappingConeIsoNonemptyOfEndpointLocalizedUnitW1012",
      "directBoundedLeftCalculusOfEndpointLocalizedUnitW1012",
      "boundedDerivedInfinityCategoryOfEndpointLocalizedUnitW1012",
      "endpointLocalizedUnitInputNamesW1012_count"]
  providerRepackagingResult :=
    "proved: W1012 constructs the W982 localized-unit-choice provider surface\
      from W1003 endpoint-localized-unit data and feeds W1011"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1012 inherits W1011/W1010/W1009/W1008/W1007/W1006/W1005/\
      W1004/W1003/W1002/W998 target surjective-compact recovery after W1003 constructs W982"
  exactAtResult :=
    "proved: the W1012 W1003 endpoint-localized-unit provider surface feeds\
      W1011/W1010/W1009/W1008/W1007/W1006/W1005/W1004/W1003/W1002/W998/\
      W997/W996/W995/W994/W993/W988/W987/W986/W985/W984/W983/W982/W981/\
      W980/W979/W978/W977/W976/W975/W974/W973/W972/W971/W970/W969/W968/\
      W967/W966/W965/W964/W963/W962/W961/W959/W958/W957/W956/W955/W954/\
      W953/W952 stable ExactAt route"
  remainingInputs := endpointLocalizedUnitInputNamesW1012
  productSuccessClaimed := false

theorem currentW1012EndpointLocalizedUnitDirectRoute_productSuccess :
    (let state := currentMetrizableEndpointLocalizedUnitDirectRouteStateW1012;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
