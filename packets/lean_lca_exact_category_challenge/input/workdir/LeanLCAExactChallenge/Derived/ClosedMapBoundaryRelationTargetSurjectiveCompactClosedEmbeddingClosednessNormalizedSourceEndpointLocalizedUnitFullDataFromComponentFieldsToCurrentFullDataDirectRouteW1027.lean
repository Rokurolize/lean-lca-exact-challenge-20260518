import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromCurrentFullDataToBranchFullDataDirectRouteW1026
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromComponentFieldsDirectRoute

/-!
W1027 replaces W1026's W1008 current-full-data surface by the existing W1009
component-field surface. W1009 already constructs W1008 from W971 component
fields through W978, and W1027 feeds that provider into W1026.
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

/-- W1027 constructs the W1008 current-full-data surface from W1009 component fields. -/
def currentFullDataProviderOfComponentFieldsW1027
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfComponentFieldsW1009 componentFields

/-- W1027 constructs the W1007 branch-full-data surface from W1009 through W1026. -/
noncomputable def branchFullDataProviderOfComponentFieldsW1027
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfCurrentFullDataW1026
    (currentFullDataProviderOfComponentFieldsW1027 componentFields)

/-- W1027 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1009 through W1026. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfComponentFieldsW1027
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1026
    (currentFullDataProviderOfComponentFieldsW1027 componentFields)

/-- W1027 constructs the W1005 target/closed-embedding-closedness surface from W1009 through W1026. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfComponentFieldsW1027
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1026
    (currentFullDataProviderOfComponentFieldsW1027 componentFields)

/-- W1027 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1009 through W1026. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfComponentFieldsW1027
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1026
    (currentFullDataProviderOfComponentFieldsW1027 componentFields)

/-- W1027 constructs the W1003 endpoint-localized-unit surface from W1009 through W1026. -/
noncomputable def endpointLocalizedUnitDataProviderOfComponentFieldsW1027
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfCurrentFullDataW1026
    (currentFullDataProviderOfComponentFieldsW1027 componentFields)

/-- W1027 constructs the W982 localized-unit-choice surface from W1009 through W1026. -/
noncomputable def localizedUnitChoiceDataOfComponentFieldsW1027
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfCurrentFullDataW1026
    (currentFullDataProviderOfComponentFieldsW1027 componentFields)

/-- W1027 constructs the W981 provider surface from W1009 through W1026. -/
noncomputable def unitStrictExactIsoDataOfComponentFieldsW1027
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfCurrentFullDataW1026
    (currentFullDataProviderOfComponentFieldsW1027 componentFields)

/-- W1027 constructs the W971 component-field surface from W1009 through W1026. -/
noncomputable def componentFieldsOfComponentFieldsW1027
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfCurrentFullDataW1026
    (currentFullDataProviderOfComponentFieldsW1027 componentFields)

/-- W1027 exposes the rebuilt W1008 current-full-data surface after routing through W1026. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfComponentFieldsW1027
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataW1026
    (currentFullDataProviderOfComponentFieldsW1027 componentFields)

/-- W1027 exposes the rebuilt W1007 branch-full-data surface after routing through W1026. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfComponentFieldsW1027
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfCurrentFullDataW1026
    (currentFullDataProviderOfComponentFieldsW1027 componentFields)

/-- W1027 exposes the rebuilt W982 localized-unit-choice surface after routing through W1026. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfComponentFieldsW1027
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfCurrentFullDataW1026
    (currentFullDataProviderOfComponentFieldsW1027 componentFields)

/-- W1027 exposes the rebuilt W971 component fields after routing through W1026. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsW1027
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfCurrentFullDataW1026
    (currentFullDataProviderOfComponentFieldsW1027 componentFields)

/-- W1027 constructs W977 current full data from W1009 through W1026. -/
noncomputable def currentFullDataOfComponentFieldsW1027
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfCurrentFullDataW1026
    (currentFullDataProviderOfComponentFieldsW1027 componentFields)

/-- W1027 constructs W987 branch full data from W1009 through W1026. -/
noncomputable def branchFullDataOfComponentFieldsW1027
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfCurrentFullDataW1026
    (currentFullDataProviderOfComponentFieldsW1027 componentFields)

/-- W1027 recovers W715 target surjective-compact data from W1009 through W1026. -/
noncomputable def targetSurjectiveCompactDataOfComponentFieldsW1027
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfCurrentFullDataW1026
    (currentFullDataProviderOfComponentFieldsW1027 componentFields)

/-- W1027 returns the constructed W987 branch full data from W1009 through W1026. -/
noncomputable def fullDataOfComponentFieldsW1027
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfCurrentFullDataW1026
    (currentFullDataProviderOfComponentFieldsW1027 componentFields)

theorem directBoundedLeftCalculusOfComponentFieldsW1027
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfCurrentFullDataW1026
    (currentFullDataProviderOfComponentFieldsW1027 componentFields)

noncomputable def boundedDerivedInfinityCategoryOfComponentFieldsW1027
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfCurrentFullDataW1026
    (currentFullDataProviderOfComponentFieldsW1027 componentFields)

def componentFieldsInputNamesW1027 : List String :=
  componentFieldsInputNamesW1009

theorem componentFieldsInputNamesW1027_count :
    componentFieldsInputNamesW1027.length = 18 :=
  componentFieldsInputNamesW1009_count

structure MetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1027 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1027 :
    MetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1027
    where
  seed := "w1027-component-fields-to-w1026-current-full-data-route"
  declarations :=
    ["currentFullDataProviderOfComponentFieldsW1027",
      "branchFullDataProviderOfComponentFieldsW1027",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfComponentFieldsW1027",
      "targetClosedEmbeddingClosednessDataProviderOfComponentFieldsW1027",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfComponentFieldsW1027",
      "endpointLocalizedUnitDataProviderOfComponentFieldsW1027",
      "localizedUnitChoiceDataOfComponentFieldsW1027",
      "unitStrictExactIsoDataOfComponentFieldsW1027",
      "componentFieldsOfComponentFieldsW1027",
      "currentFullDataProviderOfCurrentFullDataOfComponentFieldsW1027",
      "branchFullDataProviderOfBranchFullDataOfComponentFieldsW1027",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfComponentFieldsW1027",
      "componentFieldsOfComponentFieldsOfComponentFieldsW1027",
      "currentFullDataOfComponentFieldsW1027",
      "branchFullDataOfComponentFieldsW1027",
      "targetSurjectiveCompactDataOfComponentFieldsW1027",
      "fullDataOfComponentFieldsW1027",
      "directBoundedLeftCalculusOfComponentFieldsW1027",
      "boundedDerivedInfinityCategoryOfComponentFieldsW1027",
      "componentFieldsInputNamesW1027_count"]
  providerRepackagingResult :=
    "proved: W1027 constructs the W1026 W1008 current-full-data provider\
      surface from W1009 component fields and feeds W1026"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1027 inherits W1026/W1025/W1024/W1023/W1022/W1021/W1020/\
      W1019/W1018/W1017/W1016/W1015/W1014/W1013/W1012/W1011/W1010/\
      W1009/W1008/W1007/W1006/W1005/W1004/W1003/W1002/W998 target\
      surjective-compact recovery after W1009 constructs W1008"
  exactAtResult :=
    "proved: the W1027 W1009 component-field provider surface feeds\
      W1026/W1025/W1024/W1023/W1022/W1021/W1020/W1019/W1018/W1017/\
      W1016/W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/\
      W1006/W1005/W1004/W1003/W1002/W998/W997/W996/W995/W994/W993/\
      W988/W987/W986/W985/W984/W983/W982/W981/W980/W979/W978/W977/\
      W976/W975/W974/W973/W972/W971/W970/W969/W968/W967/W966/W965/\
      W964/W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/W952\
      stable ExactAt route"
  remainingInputs := componentFieldsInputNamesW1027
  productSuccessClaimed := false

theorem currentW1027ComponentFieldsToCurrentFullDataDirectRoute_productSuccess :
    (let state :=
        currentMetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1027;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
