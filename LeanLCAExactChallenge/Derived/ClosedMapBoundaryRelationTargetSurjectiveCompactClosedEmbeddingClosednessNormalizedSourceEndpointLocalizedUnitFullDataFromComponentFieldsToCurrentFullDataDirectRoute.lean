import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromCurrentFullDataToBranchFullDataDirectRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromComponentFieldsDirectRoute

/-!
W1018 replaces W1017's W1008 current-full-data surface by the existing W1009
component-field surface. W1009 already constructs W1008 from W971 component
fields through W978, and W1018 feeds that provider into W1017.
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

/-- W1018 constructs the W1008 current-full-data surface from W1009 component fields. -/
def currentFullDataProviderOfComponentFieldsW1018
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfComponentFieldsW1009 componentFields

/-- W1018 constructs the W1007 branch-full-data surface from W1009 through W1017. -/
noncomputable def branchFullDataProviderOfComponentFieldsW1018
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfCurrentFullDataW1017
    (currentFullDataProviderOfComponentFieldsW1018 componentFields)

/-- W1018 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1009 through W1017. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfComponentFieldsW1018
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1017
    (currentFullDataProviderOfComponentFieldsW1018 componentFields)

/-- W1018 constructs the W1005 target/closed-embedding-closedness surface from W1009 through W1017. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfComponentFieldsW1018
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1017
    (currentFullDataProviderOfComponentFieldsW1018 componentFields)

/-- W1018 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1009 through W1017. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfComponentFieldsW1018
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1017
    (currentFullDataProviderOfComponentFieldsW1018 componentFields)

/-- W1018 constructs the W982 localized-unit-choice surface from W1009 through W1017. -/
noncomputable def localizedUnitChoiceDataOfComponentFieldsW1018
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfCurrentFullDataW1017
    (currentFullDataProviderOfComponentFieldsW1018 componentFields)

/-- W1018 constructs the W971 component-field surface from W1009 through W1017. -/
noncomputable def componentFieldsOfComponentFieldsW1018
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfCurrentFullDataW1017
    (currentFullDataProviderOfComponentFieldsW1018 componentFields)

/-- W1018 constructs W977 current full data from W1009 through W1017. -/
noncomputable def currentFullDataOfComponentFieldsW1018
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfCurrentFullDataW1017
    (currentFullDataProviderOfComponentFieldsW1018 componentFields)

/-- W1018 constructs W987 branch full data through W1017. -/
noncomputable def branchFullDataOfComponentFieldsW1018
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfCurrentFullDataW1017
    (currentFullDataProviderOfComponentFieldsW1018 componentFields)

/-- W1018 recovers W715 target surjective-compact data through W1017. -/
noncomputable def targetSurjectiveCompactDataOfComponentFieldsW1018
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfCurrentFullDataW1017
    (currentFullDataProviderOfComponentFieldsW1018 componentFields)

/-- W1018 returns the constructed W987 branch full data through W1017. -/
noncomputable def fullDataOfComponentFieldsW1018
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfCurrentFullDataW1017
    (currentFullDataProviderOfComponentFieldsW1018 componentFields)

theorem directBoundedLeftCalculusOfComponentFieldsW1018
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfCurrentFullDataW1017
    (currentFullDataProviderOfComponentFieldsW1018 componentFields)

noncomputable def boundedDerivedInfinityCategoryOfComponentFieldsW1018
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfCurrentFullDataW1017
    (currentFullDataProviderOfComponentFieldsW1018 componentFields)

def componentFieldsInputNamesW1018 : List String :=
  componentFieldsInputNamesW1009

theorem componentFieldsInputNamesW1018_count :
    componentFieldsInputNamesW1018.length = 18 :=
  componentFieldsInputNamesW1009_count

structure MetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1018 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1018 :
    MetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1018
    where
  seed := "w1018-component-fields-to-w1017-current-full-data-route"
  declarations :=
    ["currentFullDataProviderOfComponentFieldsW1018",
      "branchFullDataProviderOfComponentFieldsW1018",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfComponentFieldsW1018",
      "targetClosedEmbeddingClosednessDataProviderOfComponentFieldsW1018",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfComponentFieldsW1018",
      "localizedUnitChoiceDataOfComponentFieldsW1018",
      "componentFieldsOfComponentFieldsW1018",
      "currentFullDataOfComponentFieldsW1018",
      "branchFullDataOfComponentFieldsW1018",
      "targetSurjectiveCompactDataOfComponentFieldsW1018",
      "fullDataOfComponentFieldsW1018",
      "directBoundedLeftCalculusOfComponentFieldsW1018",
      "boundedDerivedInfinityCategoryOfComponentFieldsW1018",
      "componentFieldsInputNamesW1018_count"]
  providerRepackagingResult :=
    "proved: W1018 constructs the W1008 current-full-data provider surface\
      from W1009 component fields and feeds W1017"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1018 inherits W1017/W1016/W1015/W1014/W1013/W1012/W1011/\
      W1010/W1009/W1008/W1007/W1006/W1005/W1004/W1003/W1002/W998 target\
      surjective-compact recovery after W1009 constructs W1008"
  exactAtResult :=
    "proved: the W1018 W1009 component-field provider surface feeds\
      W1017/W1016/W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/\
      W1007/W1006/W1005/W1004/W1003/W1002/W998/W997/W996/W995/W994/\
      W993/W988/W987/W986/W985/W984/W983/W982/W981/W980/W979/W978/W977/\
      W976/W975/W974/W973/W972/W971/W970/W969/W968/W967/W966/W965/W964/\
      W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/W952 stable\
      ExactAt route"
  remainingInputs := componentFieldsInputNamesW1018
  productSuccessClaimed := false

theorem currentW1018ComponentFieldsDirectRoute_productSuccess :
    (let state :=
        currentMetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1018;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
