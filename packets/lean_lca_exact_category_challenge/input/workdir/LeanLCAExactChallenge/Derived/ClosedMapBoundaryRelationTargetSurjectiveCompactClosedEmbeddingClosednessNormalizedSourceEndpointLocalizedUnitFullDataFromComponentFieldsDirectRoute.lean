import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromCurrentFullDataDirectRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationDataNormalizedSourceTriangulationDataClosedEmbeddingEndpointLocalizedUnitFullDataFromComponentFieldsRoute

/-!
W1009 replaces W1008's W977 current full-data provider by the W971 component
field surface. W978 already constructs W977 from W971 component fields, and
W1009 feeds that constructed current full data into W1008.
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

/-- W1009 constructs W977 current full data from W971 component fields through W978. -/
def currentFullDataOfComponentFieldsW1009
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  fullDataOfComponentFieldsW978 leaves

/-- W1009 builds the W1008 provider surface from W971 component fields. -/
def currentFullDataProviderOfComponentFieldsW1009
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008
    where
  currentFullData := currentFullDataOfComponentFieldsW1009 leaves

/-- W1009 constructs W987 branch full data through W1008 after W978 builds W977. -/
noncomputable def branchFullDataOfComponentFieldsW1009
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfCurrentFullDataW1008
    (currentFullDataProviderOfComponentFieldsW1009 leaves)

/-- W1009 builds the W1007 provider surface through W1008. -/
noncomputable def branchFullDataProviderOfComponentFieldsW1009
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfCurrentFullDataW1008
    (currentFullDataProviderOfComponentFieldsW1009 leaves)

/-- W1009 recovers W730 boundary/relation data through W1008. -/
noncomputable def boundaryRelationDataOfComponentFieldsW1009
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfCurrentFullDataW1008
    (currentFullDataProviderOfComponentFieldsW1009 leaves)

/--
W1009 recovers W986 target/closedness/normalized-source/endpoint-localized data
through W1008.
-/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfComponentFieldsW1009
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfCurrentFullDataW1008
    (currentFullDataProviderOfComponentFieldsW1009 leaves)

/-- W1009 builds the W1006 provider surface through W1008. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfComponentFieldsW1009
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1008
    (currentFullDataProviderOfComponentFieldsW1009 leaves)

/-- W1009 projects W984 target/closed-embedding closedness data through W1008. -/
noncomputable def targetClosedEmbeddingClosednessDataOfComponentFieldsW1009
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    TargetNoUnivClosedEmbeddingClosednessDataProviderW984 :=
  targetClosedEmbeddingClosednessDataOfCurrentFullDataW1008
    (currentFullDataProviderOfComponentFieldsW1009 leaves)

/-- W1009 projects W950 normalized-source/endpoint-localized-unit data through W1008. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataOfComponentFieldsW1009
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950 :=
  normalizedSourceEndpointLocalizedUnitDataOfCurrentFullDataW1008
    (currentFullDataProviderOfComponentFieldsW1009 leaves)

/-- W1009 projects W944 target no-univ data through W1008. -/
noncomputable def targetNoUnivDataOfComponentFieldsW1009
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944 :=
  targetNoUnivDataOfCurrentFullDataW1008
    (currentFullDataProviderOfComponentFieldsW1009 leaves)

/-- W1009 projects W973 closed-embedding closedness data through W1008. -/
noncomputable def closedEmbeddingClosednessDataOfComponentFieldsW1009
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    ClosedEmbeddingClosednessDataProviderW973 :=
  closedEmbeddingClosednessDataOfCurrentFullDataW1008
    (currentFullDataProviderOfComponentFieldsW1009 leaves)

/-- W1009 constructs W1004 normalized-source/endpoint-localized data through W1008. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfComponentFieldsW1009
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1008
    (currentFullDataProviderOfComponentFieldsW1009 leaves)

/-- W1009 constructs W1003 endpoint-localized-unit data through W1008. -/
noncomputable def endpointLocalizedUnitDataProviderOfComponentFieldsW1009
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfCurrentFullDataW1008
    (currentFullDataProviderOfComponentFieldsW1009 leaves)

/-- W1009 constructs W982 localized-unit-choice data through W1008. -/
noncomputable def localizedUnitChoiceDataOfComponentFieldsW1009
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfCurrentFullDataW1008
    (currentFullDataProviderOfComponentFieldsW1009 leaves)

/-- W1009 recovers W715 target surjective-compact data through W1008. -/
noncomputable def targetSurjectiveCompactDataOfComponentFieldsW1009
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfCurrentFullDataW1008
    (currentFullDataProviderOfComponentFieldsW1009 leaves)

/-- W1009 builds W997's branch-full-data surface through W1008. -/
noncomputable def targetSurjectiveCompactBranchFullDataOfComponentFieldsW1009
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997 :=
  targetSurjectiveCompactBranchFullDataOfCurrentFullDataW1008
    (currentFullDataProviderOfComponentFieldsW1009 leaves)

/-- W1009 builds the W995 target-provider surface through W1008. -/
noncomputable def targetProviderDataOfComponentFieldsW1009
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995 :=
  targetProviderDataOfCurrentFullDataW1008
    (currentFullDataProviderOfComponentFieldsW1009 leaves)

/-- W1009 builds the W994 normalized-source/endpoint route data through W1008. -/
noncomputable def normalizedSourceEndpointDataOfComponentFieldsW1009
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994 :=
  normalizedSourceEndpointDataOfCurrentFullDataW1008
    (currentFullDataProviderOfComponentFieldsW1009 leaves)

/-- W1009 returns the constructed W987 branch full data through W1008. -/
noncomputable def fullDataOfComponentFieldsW1009
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfCurrentFullDataW1008
    (currentFullDataProviderOfComponentFieldsW1009 leaves)

/- W1009 exposes W977 leaves through W1008. -/
noncomputable def w977LeavesOfComponentFieldsW1009
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w977LeavesOfCurrentFullDataW1008
    (currentFullDataProviderOfComponentFieldsW1009 leaves)

/- W1009 exposes W971 component fields through W1008. -/
noncomputable def componentFieldsOfComponentFieldsW1009
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfCurrentFullDataW1008
    (currentFullDataProviderOfComponentFieldsW1009 leaves)

/-- W1009 reconstructs endpoint strict short exactness through W1008. -/
noncomputable def endpointStrictExactOfComponentFieldsW1009
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfCurrentFullDataW1008
    (currentFullDataProviderOfComponentFieldsW1009 leaves)

/-- W1009 derives unit mapping-cone algebraic exactness through W1008. -/
noncomputable def unitMappingConeAlgebraicExactOfComponentFieldsW1009
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ :
        (((componentFieldsOfComponentFieldsW1009 leaves).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfComponentFieldsW1009 leaves).unitMappingConeModel X).as.sc i).g x₂ =
            0 →
          ∃ x₁ :
            (((componentFieldsOfComponentFieldsW1009 leaves).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfComponentFieldsW1009 leaves).unitMappingConeModel X).as.sc i).f x₁ =
              x₂ :=
  unitMappingConeAlgebraicExactOfCurrentFullDataW1008
    (currentFullDataProviderOfComponentFieldsW1009 leaves)

/-- W1009 reconstructs unit mapping-cone strict short exactness through W1008. -/
noncomputable def unitMappingConeStrictExactOfComponentFieldsW1009
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfComponentFieldsW1009 leaves).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfCurrentFullDataW1008
    (currentFullDataProviderOfComponentFieldsW1009 leaves)

/-- W1009 wraps the unit mapping-cone isomorphism through W1008. -/
@[reducible]
noncomputable def unitMappingConeIsoNonemptyOfComponentFieldsW1009
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfComponentFieldsW1009 leaves).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfComponentFieldsW1009 leaves).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfCurrentFullDataW1008
    (currentFullDataProviderOfComponentFieldsW1009 leaves)

theorem directBoundedLeftCalculusOfComponentFieldsW1009
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfCurrentFullDataW1008
    (currentFullDataProviderOfComponentFieldsW1009 leaves)

noncomputable def boundedDerivedInfinityCategoryOfComponentFieldsW1009
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfCurrentFullDataW1008
    (currentFullDataProviderOfComponentFieldsW1009 leaves)

def componentFieldsInputNamesW1009 : List String :=
  closedEmbeddingEndpointLocalizedUnitFullDataFromComponentFieldsInputNamesW978

theorem componentFieldsInputNamesW1009_count :
    componentFieldsInputNamesW1009.length = 18 :=
  closedEmbeddingEndpointLocalizedUnitFullDataFromComponentFieldsInputNamesW978_count

structure MetrizableComponentFieldsDirectRouteStateW1009 : Type where
  seed : String
  declarations : List String
  componentFieldRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableComponentFieldsDirectRouteStateW1009 :
    MetrizableComponentFieldsDirectRouteStateW1009
    where
  seed := "w1009-component-fields-to-w1008-current-full-data-route"
  declarations :=
    ["currentFullDataOfComponentFieldsW1009",
      "currentFullDataProviderOfComponentFieldsW1009",
      "branchFullDataOfComponentFieldsW1009",
      "branchFullDataProviderOfComponentFieldsW1009",
      "boundaryRelationDataOfComponentFieldsW1009",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfComponentFieldsW1009",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfComponentFieldsW1009",
      "targetClosedEmbeddingClosednessDataOfComponentFieldsW1009",
      "normalizedSourceEndpointLocalizedUnitDataOfComponentFieldsW1009",
      "targetNoUnivDataOfComponentFieldsW1009",
      "closedEmbeddingClosednessDataOfComponentFieldsW1009",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfComponentFieldsW1009",
      "endpointLocalizedUnitDataProviderOfComponentFieldsW1009",
      "localizedUnitChoiceDataOfComponentFieldsW1009",
      "targetSurjectiveCompactDataOfComponentFieldsW1009",
      "targetSurjectiveCompactBranchFullDataOfComponentFieldsW1009",
      "targetProviderDataOfComponentFieldsW1009",
      "normalizedSourceEndpointDataOfComponentFieldsW1009",
      "fullDataOfComponentFieldsW1009",
      "w977LeavesOfComponentFieldsW1009",
      "componentFieldsOfComponentFieldsW1009",
      "endpointStrictExactOfComponentFieldsW1009",
      "unitMappingConeAlgebraicExactOfComponentFieldsW1009",
      "unitMappingConeStrictExactOfComponentFieldsW1009",
      "unitMappingConeIsoNonemptyOfComponentFieldsW1009",
      "directBoundedLeftCalculusOfComponentFieldsW1009",
      "boundedDerivedInfinityCategoryOfComponentFieldsW1009",
      "componentFieldsInputNamesW1009_count"]
  componentFieldRepackagingResult :=
    "proved: W1009 constructs W977 current full data from W971 component\
      fields through W978 and feeds the W1008 current-full-data route"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1009 inherits W1008/W1007/W1006/W1005/W1004/W1003/W1002/\
      W998 target surjective-compact recovery after W971 constructs W977"
  exactAtResult :=
    "proved: the W1009 W971 component-field surface feeds W1008/W1007/\
      W1006/W1005/W1004/W1003/W1002/W998/W997/W996/W995/W994/W993/W988/\
      W987/W986/W985/W984/W983/W982/W981/W980/W979/W978/W977/W976/W975/\
      W974/W973/W972/W971/W970/W969/W968/W967/W966/W965/W964/W963/W962/\
      W961/W959/W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := componentFieldsInputNamesW1009
  productSuccessClaimed := false

theorem currentW1009ComponentFieldsDirectRoute_productSuccess :
    (let state := currentMetrizableComponentFieldsDirectRouteStateW1009;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
