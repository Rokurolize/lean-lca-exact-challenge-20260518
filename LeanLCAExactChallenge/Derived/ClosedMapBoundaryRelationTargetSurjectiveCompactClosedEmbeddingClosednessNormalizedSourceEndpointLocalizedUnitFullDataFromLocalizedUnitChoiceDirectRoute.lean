import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromUnitStrictExactIsoDataDirectRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataRoute

/-!
W1011 replaces W1010's W981 endpoint/unit-strict-exact provider surface by the
existing W982 localized-unit-choice surface. W982 already constructs W981, and
W1011 feeds that provider into W1010.
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

/-- W1011 constructs the W981 provider surface from W982 localized-unit-choice data. -/
noncomputable def unitStrictExactIsoDataOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  fullDataOfLocalizedUnitChoiceW982 localizedUnitChoiceData

/-- W1011 constructs the W971 component-field surface from W982 through W1010. -/
noncomputable def componentFieldsOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfUnitStrictExactIsoDataW1010
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)

/-- W1011 constructs W977 current full data from W982 through W1010. -/
noncomputable def currentFullDataOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfUnitStrictExactIsoDataW1010
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)

/-- W1011 builds the W1008 provider surface through W1010. -/
noncomputable def currentFullDataProviderOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfUnitStrictExactIsoDataW1010
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)

/-- W1011 constructs W987 branch full data through W1010. -/
noncomputable def branchFullDataOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfUnitStrictExactIsoDataW1010
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)

/-- W1011 builds the W1007 provider surface through W1010. -/
noncomputable def branchFullDataProviderOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfUnitStrictExactIsoDataW1010
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)

/-- W1011 recovers W730 boundary/relation data through W1010. -/
noncomputable def boundaryRelationDataOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfUnitStrictExactIsoDataW1010
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)

/-!
W1011 recovers W986 target/closedness/normalized-source/endpoint-localized data
through W1010.
-/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfUnitStrictExactIsoDataW1010
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)

/-- W1011 builds the W1006 provider surface through W1010. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfUnitStrictExactIsoDataW1010
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)

/-- W1011 projects W984 target/closed-embedding closedness data through W1010. -/
noncomputable def targetClosedEmbeddingClosednessDataOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    TargetNoUnivClosedEmbeddingClosednessDataProviderW984 :=
  targetClosedEmbeddingClosednessDataOfUnitStrictExactIsoDataW1010
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)

/-- W1011 projects W950 normalized-source/endpoint-localized-unit data through W1010. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950 :=
  normalizedSourceEndpointLocalizedUnitDataOfUnitStrictExactIsoDataW1010
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)

/-- W1011 projects W944 target no-univ data through W1010. -/
noncomputable def targetNoUnivDataOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944 :=
  targetNoUnivDataOfUnitStrictExactIsoDataW1010
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)

/-- W1011 projects W973 closed-embedding closedness data through W1010. -/
noncomputable def closedEmbeddingClosednessDataOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    ClosedEmbeddingClosednessDataProviderW973 :=
  closedEmbeddingClosednessDataOfUnitStrictExactIsoDataW1010
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)

/-- W1011 constructs W1004 normalized-source/endpoint-localized data through W1010. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1010
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)

/-- W1011 constructs W1003 endpoint-localized-unit data through W1010. -/
noncomputable def endpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1010
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)

/-- W1011 returns the W982 localized-unit-choice data through W1010. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfUnitStrictExactIsoDataW1010
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)

/-- W1011 recovers W715 target surjective-compact data through W1010. -/
noncomputable def targetSurjectiveCompactDataOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfUnitStrictExactIsoDataW1010
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)

/-- W1011 builds W997's branch-full-data surface through W1010. -/
noncomputable def targetSurjectiveCompactBranchFullDataOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997 :=
  targetSurjectiveCompactBranchFullDataOfUnitStrictExactIsoDataW1010
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)

/-- W1011 builds the W995 target-provider surface through W1010. -/
noncomputable def targetProviderDataOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995 :=
  targetProviderDataOfUnitStrictExactIsoDataW1010
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)

/-- W1011 builds the W994 normalized-source/endpoint route data through W1010. -/
noncomputable def normalizedSourceEndpointDataOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994 :=
  normalizedSourceEndpointDataOfUnitStrictExactIsoDataW1010
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)

/-- W1011 returns the constructed W987 branch full data through W1010. -/
noncomputable def fullDataOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfUnitStrictExactIsoDataW1010
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)

/- W1011 exposes W977 leaves through W1010. -/
noncomputable def w977LeavesOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w977LeavesOfUnitStrictExactIsoDataW1010
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)

/- W1011 exposes W971 component fields through W1010. -/
noncomputable def componentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1010
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)

/-- W1011 reconstructs endpoint strict exactness through W1010. -/
noncomputable def endpointStrictExactOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfUnitStrictExactIsoDataW1010
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)

/-- W1011 derives unit mapping-cone algebraic exactness through W1010. -/
noncomputable def unitMappingConeAlgebraicExactOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ :
        (((componentFieldsOfComponentFieldsW1009
            (componentFieldsOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfComponentFieldsW1009
            (componentFieldsOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)).unitMappingConeModel X).as.sc i).g x₂ =
            0 →
          ∃ x₁ :
            (((componentFieldsOfComponentFieldsW1009
                (componentFieldsOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfComponentFieldsW1009
                (componentFieldsOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)).unitMappingConeModel X).as.sc i).f x₁ =
              x₂ :=
  unitMappingConeAlgebraicExactOfUnitStrictExactIsoDataW1010
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)

/-- W1011 reconstructs unit mapping-cone strict short exactness through W1010. -/
noncomputable def unitMappingConeStrictExactOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfComponentFieldsW1009
            (componentFieldsOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfUnitStrictExactIsoDataW1010
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)

/-- W1011 wraps the unit mapping-cone isomorphism through W1010. -/
@[reducible]
noncomputable def unitMappingConeIsoNonemptyOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfComponentFieldsW1009
                    (componentFieldsOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfComponentFieldsW1009
            (componentFieldsOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfUnitStrictExactIsoDataW1010
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)

theorem directBoundedLeftCalculusOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfUnitStrictExactIsoDataW1010
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)

noncomputable def boundedDerivedInfinityCategoryOfLocalizedUnitChoiceW1011
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfUnitStrictExactIsoDataW1010
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1011 localizedUnitChoiceData)

def localizedUnitChoiceInputNamesW1011 : List String :=
  endpointStrictExactLocalizedUnitChoiceFullDataInputNamesW982

theorem localizedUnitChoiceInputNamesW1011_count :
    localizedUnitChoiceInputNamesW1011.length = 6 :=
  endpointStrictExactLocalizedUnitChoiceFullDataInputNamesW982_count

structure MetrizableLocalizedUnitChoiceDirectRouteStateW1011 : Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableLocalizedUnitChoiceDirectRouteStateW1011 :
    MetrizableLocalizedUnitChoiceDirectRouteStateW1011
    where
  seed := "w1011-localized-unit-choice-to-w1010-unit-strict-exact-route"
  declarations :=
    ["unitStrictExactIsoDataOfLocalizedUnitChoiceW1011",
      "componentFieldsOfLocalizedUnitChoiceW1011",
      "currentFullDataOfLocalizedUnitChoiceW1011",
      "currentFullDataProviderOfLocalizedUnitChoiceW1011",
      "branchFullDataOfLocalizedUnitChoiceW1011",
      "branchFullDataProviderOfLocalizedUnitChoiceW1011",
      "boundaryRelationDataOfLocalizedUnitChoiceW1011",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfLocalizedUnitChoiceW1011",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfLocalizedUnitChoiceW1011",
      "targetClosedEmbeddingClosednessDataOfLocalizedUnitChoiceW1011",
      "normalizedSourceEndpointLocalizedUnitDataOfLocalizedUnitChoiceW1011",
      "targetNoUnivDataOfLocalizedUnitChoiceW1011",
      "closedEmbeddingClosednessDataOfLocalizedUnitChoiceW1011",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1011",
      "endpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1011",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceW1011",
      "targetSurjectiveCompactDataOfLocalizedUnitChoiceW1011",
      "targetSurjectiveCompactBranchFullDataOfLocalizedUnitChoiceW1011",
      "targetProviderDataOfLocalizedUnitChoiceW1011",
      "normalizedSourceEndpointDataOfLocalizedUnitChoiceW1011",
      "fullDataOfLocalizedUnitChoiceW1011",
      "w977LeavesOfLocalizedUnitChoiceW1011",
      "componentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1011",
      "endpointStrictExactOfLocalizedUnitChoiceW1011",
      "unitMappingConeAlgebraicExactOfLocalizedUnitChoiceW1011",
      "unitMappingConeStrictExactOfLocalizedUnitChoiceW1011",
      "unitMappingConeIsoNonemptyOfLocalizedUnitChoiceW1011",
      "directBoundedLeftCalculusOfLocalizedUnitChoiceW1011",
      "boundedDerivedInfinityCategoryOfLocalizedUnitChoiceW1011",
      "localizedUnitChoiceInputNamesW1011_count"]
  providerRepackagingResult :=
    "proved: W1011 constructs the W981 endpoint/unit-strict-exact provider\
      surface from W982 localized-unit-choice data through W982 and feeds W1010"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1011 inherits W1010/W1009/W1008/W1007/W1006/W1005/W1004/\
      W1003/W1002/W998 target surjective-compact recovery after W982 constructs W981"
  exactAtResult :=
    "proved: the W1011 W982 localized-unit-choice provider surface feeds\
      W1010/W1009/W1008/W1007/W1006/W1005/W1004/W1003/W1002/W998/W997/\
      W996/W995/W994/W993/W988/W987/W986/W985/W984/W983/W982/W981/W980/\
      W979/W978/W977/W976/W975/W974/W973/W972/W971/W970/W969/W968/W967/\
      W966/W965/W964/W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/\
      W952 stable ExactAt route"
  remainingInputs := localizedUnitChoiceInputNamesW1011
  productSuccessClaimed := false

theorem currentW1011LocalizedUnitChoiceDirectRoute_productSuccess :
    (let state := currentMetrizableLocalizedUnitChoiceDirectRouteStateW1011;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
