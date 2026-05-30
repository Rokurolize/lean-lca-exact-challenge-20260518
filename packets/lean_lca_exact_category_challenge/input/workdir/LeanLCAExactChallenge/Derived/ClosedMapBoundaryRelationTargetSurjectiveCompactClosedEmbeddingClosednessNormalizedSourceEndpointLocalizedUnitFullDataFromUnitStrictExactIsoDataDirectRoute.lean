import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromComponentFieldsDirectRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromUnitStrictExactIsoDataRoute

/-!
W1010 replaces W1009's W971 component-field surface by the existing W981
endpoint/unit-strict-exact provider surface. W1001 already constructs W971
component fields from W981, and W1010 feeds those fields into W1009.
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

/-- W1010 constructs the W971 component-field surface from W981 provider data. -/
def componentFieldsOfUnitStrictExactIsoDataW1010
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfUnitStrictExactIsoDataW1001 fullData

/-- W1010 constructs W977 current full data from W981 through W1009. -/
noncomputable def currentFullDataOfUnitStrictExactIsoDataW1010
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfComponentFieldsW1009
    (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)

/-- W1010 builds the W1008 provider surface through W1009. -/
noncomputable def currentFullDataProviderOfUnitStrictExactIsoDataW1010
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfComponentFieldsW1009
    (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)

/-- W1010 constructs W987 branch full data through W1009. -/
noncomputable def branchFullDataOfUnitStrictExactIsoDataW1010
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfComponentFieldsW1009
    (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)

/-- W1010 builds the W1007 provider surface through W1009. -/
noncomputable def branchFullDataProviderOfUnitStrictExactIsoDataW1010
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfComponentFieldsW1009
    (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)

/-- W1010 recovers W730 boundary/relation data through W1009. -/
noncomputable def boundaryRelationDataOfUnitStrictExactIsoDataW1010
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfComponentFieldsW1009
    (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)

/--
W1010 recovers W986 target/closedness/normalized-source/endpoint-localized data
through W1009.
-/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfUnitStrictExactIsoDataW1010
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfComponentFieldsW1009
    (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)

/-- W1010 builds the W1006 provider surface through W1009. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfUnitStrictExactIsoDataW1010
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfComponentFieldsW1009
    (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)

/-- W1010 projects W984 target/closed-embedding closedness data through W1009. -/
noncomputable def targetClosedEmbeddingClosednessDataOfUnitStrictExactIsoDataW1010
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    TargetNoUnivClosedEmbeddingClosednessDataProviderW984 :=
  targetClosedEmbeddingClosednessDataOfComponentFieldsW1009
    (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)

/-- W1010 projects W950 normalized-source/endpoint-localized-unit data through W1009. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataOfUnitStrictExactIsoDataW1010
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950 :=
  normalizedSourceEndpointLocalizedUnitDataOfComponentFieldsW1009
    (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)

/-- W1010 projects W944 target no-univ data through W1009. -/
noncomputable def targetNoUnivDataOfUnitStrictExactIsoDataW1010
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944 :=
  targetNoUnivDataOfComponentFieldsW1009
    (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)

/-- W1010 projects W973 closed-embedding closedness data through W1009. -/
noncomputable def closedEmbeddingClosednessDataOfUnitStrictExactIsoDataW1010
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    ClosedEmbeddingClosednessDataProviderW973 :=
  closedEmbeddingClosednessDataOfComponentFieldsW1009
    (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)

/-- W1010 constructs W1004 normalized-source/endpoint-localized data through W1009. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1010
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfComponentFieldsW1009
    (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)

/-- W1010 constructs W1003 endpoint-localized-unit data through W1009. -/
noncomputable def endpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1010
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfComponentFieldsW1009
    (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)

/-- W1010 constructs W982 localized-unit-choice data through W1009. -/
noncomputable def localizedUnitChoiceDataOfUnitStrictExactIsoDataW1010
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfComponentFieldsW1009
    (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)

/-- W1010 recovers W715 target surjective-compact data through W1009. -/
noncomputable def targetSurjectiveCompactDataOfUnitStrictExactIsoDataW1010
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfComponentFieldsW1009
    (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)

/-- W1010 builds W997's branch-full-data surface through W1009. -/
noncomputable def targetSurjectiveCompactBranchFullDataOfUnitStrictExactIsoDataW1010
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997 :=
  targetSurjectiveCompactBranchFullDataOfComponentFieldsW1009
    (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)

/-- W1010 builds the W995 target-provider surface through W1009. -/
noncomputable def targetProviderDataOfUnitStrictExactIsoDataW1010
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995 :=
  targetProviderDataOfComponentFieldsW1009
    (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)

/-- W1010 builds the W994 normalized-source/endpoint route data through W1009. -/
noncomputable def normalizedSourceEndpointDataOfUnitStrictExactIsoDataW1010
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994 :=
  normalizedSourceEndpointDataOfComponentFieldsW1009
    (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)

/-- W1010 returns the constructed W987 branch full data through W1009. -/
noncomputable def fullDataOfUnitStrictExactIsoDataW1010
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfComponentFieldsW1009
    (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)

/- W1010 exposes W977 leaves through W1009. -/
noncomputable def w977LeavesOfUnitStrictExactIsoDataW1010
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w977LeavesOfComponentFieldsW1009
    (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)

/- W1010 exposes W971 component fields through W1009. -/
noncomputable def componentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1010
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsW1009
    (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)

/-- W1010 reconstructs endpoint strict exactness through W1009. -/
noncomputable def endpointStrictExactOfUnitStrictExactIsoDataW1010
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfComponentFieldsW1009
    (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)

/-- W1010 derives unit mapping-cone algebraic exactness through W1009. -/
noncomputable def unitMappingConeAlgebraicExactOfUnitStrictExactIsoDataW1010
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ :
        (((componentFieldsOfComponentFieldsW1009
            (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfComponentFieldsW1009
            (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)).unitMappingConeModel X).as.sc i).g x₂ =
            0 →
          ∃ x₁ :
            (((componentFieldsOfComponentFieldsW1009
                (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfComponentFieldsW1009
                (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)).unitMappingConeModel X).as.sc i).f x₁ =
              x₂ :=
  unitMappingConeAlgebraicExactOfComponentFieldsW1009
    (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)

/-- W1010 reconstructs unit mapping-cone strict short exactness through W1009. -/
noncomputable def unitMappingConeStrictExactOfUnitStrictExactIsoDataW1010
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfComponentFieldsW1009
            (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfComponentFieldsW1009
    (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)

/-- W1010 wraps the unit mapping-cone isomorphism through W1009. -/
@[reducible]
noncomputable def unitMappingConeIsoNonemptyOfUnitStrictExactIsoDataW1010
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfComponentFieldsW1009
                    (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfComponentFieldsW1009
            (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfComponentFieldsW1009
    (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)

theorem directBoundedLeftCalculusOfUnitStrictExactIsoDataW1010
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfComponentFieldsW1009
    (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)

noncomputable def boundedDerivedInfinityCategoryOfUnitStrictExactIsoDataW1010
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfComponentFieldsW1009
    (componentFieldsOfUnitStrictExactIsoDataW1010 fullData)

def unitStrictExactIsoDataInputNamesW1010 : List String :=
  endpointUnitStrictExactLocalizedUnitFullDataInputNamesW981

theorem unitStrictExactIsoDataInputNamesW1010_count :
    unitStrictExactIsoDataInputNamesW1010.length = 7 :=
  endpointUnitStrictExactLocalizedUnitFullDataInputNamesW981_count

structure MetrizableUnitStrictExactIsoDataDirectRouteStateW1010 : Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableUnitStrictExactIsoDataDirectRouteStateW1010 :
    MetrizableUnitStrictExactIsoDataDirectRouteStateW1010
    where
  seed := "w1010-unit-strict-exact-iso-data-to-w1009-component-fields-route"
  declarations :=
    ["componentFieldsOfUnitStrictExactIsoDataW1010",
      "currentFullDataOfUnitStrictExactIsoDataW1010",
      "currentFullDataProviderOfUnitStrictExactIsoDataW1010",
      "branchFullDataOfUnitStrictExactIsoDataW1010",
      "branchFullDataProviderOfUnitStrictExactIsoDataW1010",
      "boundaryRelationDataOfUnitStrictExactIsoDataW1010",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfUnitStrictExactIsoDataW1010",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfUnitStrictExactIsoDataW1010",
      "targetClosedEmbeddingClosednessDataOfUnitStrictExactIsoDataW1010",
      "normalizedSourceEndpointLocalizedUnitDataOfUnitStrictExactIsoDataW1010",
      "targetNoUnivDataOfUnitStrictExactIsoDataW1010",
      "closedEmbeddingClosednessDataOfUnitStrictExactIsoDataW1010",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1010",
      "endpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1010",
      "localizedUnitChoiceDataOfUnitStrictExactIsoDataW1010",
      "targetSurjectiveCompactDataOfUnitStrictExactIsoDataW1010",
      "targetSurjectiveCompactBranchFullDataOfUnitStrictExactIsoDataW1010",
      "targetProviderDataOfUnitStrictExactIsoDataW1010",
      "normalizedSourceEndpointDataOfUnitStrictExactIsoDataW1010",
      "fullDataOfUnitStrictExactIsoDataW1010",
      "w977LeavesOfUnitStrictExactIsoDataW1010",
      "componentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1010",
      "endpointStrictExactOfUnitStrictExactIsoDataW1010",
      "unitMappingConeAlgebraicExactOfUnitStrictExactIsoDataW1010",
      "unitMappingConeStrictExactOfUnitStrictExactIsoDataW1010",
      "unitMappingConeIsoNonemptyOfUnitStrictExactIsoDataW1010",
      "directBoundedLeftCalculusOfUnitStrictExactIsoDataW1010",
      "boundedDerivedInfinityCategoryOfUnitStrictExactIsoDataW1010",
      "unitStrictExactIsoDataInputNamesW1010_count"]
  providerRepackagingResult :=
    "proved: W1010 constructs the W971 component-field surface from W981\
      endpoint/unit-strict-exact provider data through W1001 and feeds W1009"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1010 inherits W1009/W1008/W1007/W1006/W1005/W1004/W1003/\
      W1002/W998 target surjective-compact recovery after W981 constructs W971"
  exactAtResult :=
    "proved: the W1010 W981 endpoint/unit-strict-exact provider surface feeds\
      W1009/W1008/W1007/W1006/W1005/W1004/W1003/W1002/W998/W997/W996/\
      W995/W994/W993/W988/W987/W986/W985/W984/W983/W982/W981/W980/W979/\
      W978/W977/W976/W975/W974/W973/W972/W971/W970/W969/W968/W967/W966/\
      W965/W964/W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/W952\
      stable ExactAt route"
  remainingInputs := unitStrictExactIsoDataInputNamesW1010
  productSuccessClaimed := false

theorem currentW1010UnitStrictExactIsoDataDirectRoute_productSuccess :
    (let state := currentMetrizableUnitStrictExactIsoDataDirectRouteStateW1010;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
