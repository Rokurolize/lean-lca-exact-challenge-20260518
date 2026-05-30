import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromCurrentFullDataToBranchFullDataDirectRouteW1035
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromComponentFieldsDirectRoute

/-!
W1036 replaces W1035's W1008 current-full-data surface by the existing W1009
component-field surface. W1009 already constructs W1008 from W971 component
fields through W978, and W1036 feeds that provider into W1035.
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

/-- W1036 constructs the W1008 current-full-data surface from W1009 component fields. -/
def currentFullDataProviderOfComponentFieldsW1036
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfComponentFieldsW1009 componentFields

/-- W1036 constructs the W1007 branch-full-data surface from W1009 through W1035. -/
noncomputable def branchFullDataProviderOfComponentFieldsW1036
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfCurrentFullDataW1035
    (currentFullDataProviderOfComponentFieldsW1036 componentFields)

/-- W1036 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1009 through W1035. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfComponentFieldsW1036
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1035
    (currentFullDataProviderOfComponentFieldsW1036 componentFields)

/-- W1036 constructs the W1005 target/closed-embedding-closedness surface from W1009 through W1035. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfComponentFieldsW1036
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1035
    (currentFullDataProviderOfComponentFieldsW1036 componentFields)

/-- W1036 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1009 through W1035. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfComponentFieldsW1036
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1035
    (currentFullDataProviderOfComponentFieldsW1036 componentFields)

/-- W1036 constructs the W1003 endpoint-localized-unit surface from W1009 through W1035. -/
noncomputable def endpointLocalizedUnitDataProviderOfComponentFieldsW1036
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfCurrentFullDataW1035
    (currentFullDataProviderOfComponentFieldsW1036 componentFields)

/-- W1036 constructs the W982 localized-unit-choice surface from W1009 through W1035. -/
noncomputable def localizedUnitChoiceDataOfComponentFieldsW1036
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfCurrentFullDataW1035
    (currentFullDataProviderOfComponentFieldsW1036 componentFields)

/-- W1036 constructs the W981 provider surface from W1009 through W1035. -/
noncomputable def unitStrictExactIsoDataOfComponentFieldsW1036
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfCurrentFullDataW1035
    (currentFullDataProviderOfComponentFieldsW1036 componentFields)

/-- W1036 constructs the W971 component-field surface from W1009 through W1035. -/
noncomputable def componentFieldsOfComponentFieldsW1036
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfCurrentFullDataW1035
    (currentFullDataProviderOfComponentFieldsW1036 componentFields)

/-- W1036 exposes the rebuilt W1008 current-full-data surface after routing through W1035. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfComponentFieldsW1036
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataW1035
    (currentFullDataProviderOfComponentFieldsW1036 componentFields)

/-- W1036 exposes the rebuilt W1007 branch-full-data surface after routing through W1035. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfComponentFieldsW1036
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfCurrentFullDataW1035
    (currentFullDataProviderOfComponentFieldsW1036 componentFields)

/-- W1036 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1035. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfComponentFieldsW1036
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfCurrentFullDataW1035
    (currentFullDataProviderOfComponentFieldsW1036 componentFields)

/-- W1036 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1035. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfComponentFieldsW1036
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfCurrentFullDataW1035
    (currentFullDataProviderOfComponentFieldsW1036 componentFields)

/-- W1036 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1035. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfComponentFieldsW1036
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfCurrentFullDataW1035
    (currentFullDataProviderOfComponentFieldsW1036 componentFields)

/-- W1036 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1035. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfComponentFieldsW1036
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfCurrentFullDataW1035
    (currentFullDataProviderOfComponentFieldsW1036 componentFields)

/-- W1036 exposes the rebuilt W982 localized-unit-choice surface after routing through W1035. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfComponentFieldsW1036
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfCurrentFullDataW1035
    (currentFullDataProviderOfComponentFieldsW1036 componentFields)

/-- W1036 exposes the rebuilt W981 surface after routing through W1035. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfComponentFieldsW1036
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfCurrentFullDataW1035
    (currentFullDataProviderOfComponentFieldsW1036 componentFields)

/-- W1036 exposes the rebuilt W971 component fields after routing through W1035. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsW1036
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfCurrentFullDataW1035
    (currentFullDataProviderOfComponentFieldsW1036 componentFields)

/-- W1036 exposes the rebuilt W1008 current-full-data surface after routing through W1035. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfComponentFieldsW1036
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfCurrentFullDataW1035
    (currentFullDataProviderOfComponentFieldsW1036 componentFields)

/-- W1036 exposes the rebuilt W1007 branch-full-data surface after routing through W1035. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfComponentFieldsW1036
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataOfCurrentFullDataW1035
    (currentFullDataProviderOfComponentFieldsW1036 componentFields)

/-- W1036 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1035. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfComponentFieldsW1036
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfCurrentFullDataW1035
    (currentFullDataProviderOfComponentFieldsW1036 componentFields)

/-- W1036 exposes the twice-rebuilt W971 component fields after routing through W1035. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsW1036
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfCurrentFullDataW1035
    (currentFullDataProviderOfComponentFieldsW1036 componentFields)

/-- W1036 constructs W977 current full data from W1009 through W1035. -/
noncomputable def currentFullDataOfComponentFieldsW1036
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfCurrentFullDataW1035
    (currentFullDataProviderOfComponentFieldsW1036 componentFields)

/-- W1036 constructs W987 branch full data from W1009 through W1035. -/
noncomputable def branchFullDataOfComponentFieldsW1036
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfCurrentFullDataW1035
    (currentFullDataProviderOfComponentFieldsW1036 componentFields)

/-- W1036 recovers W715 target surjective-compact data from W1009 through W1035. -/
noncomputable def targetSurjectiveCompactDataOfComponentFieldsW1036
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfCurrentFullDataW1035
    (currentFullDataProviderOfComponentFieldsW1036 componentFields)

/-- W1036 returns the constructed W987 branch full data from W1009 through W1035. -/
noncomputable def fullDataOfComponentFieldsW1036
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfCurrentFullDataW1035
    (currentFullDataProviderOfComponentFieldsW1036 componentFields)

theorem directBoundedLeftCalculusOfComponentFieldsW1036
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfCurrentFullDataW1035
    (currentFullDataProviderOfComponentFieldsW1036 componentFields)

noncomputable def boundedDerivedInfinityCategoryOfComponentFieldsW1036
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfCurrentFullDataW1035
    (currentFullDataProviderOfComponentFieldsW1036 componentFields)

def componentFieldsInputNamesW1036 : List String :=
  componentFieldsInputNamesW1009

theorem componentFieldsInputNamesW1036_count :
    componentFieldsInputNamesW1036.length = 18 :=
  componentFieldsInputNamesW1009_count

structure MetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1036 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1036 :
    MetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1036
    where
  seed := "w1036-component-fields-to-w1035-current-full-data-route"
  declarations :=
    ["currentFullDataProviderOfComponentFieldsW1036",
      "branchFullDataProviderOfComponentFieldsW1036",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfComponentFieldsW1036",
      "targetClosedEmbeddingClosednessDataProviderOfComponentFieldsW1036",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfComponentFieldsW1036",
      "endpointLocalizedUnitDataProviderOfComponentFieldsW1036",
      "localizedUnitChoiceDataOfComponentFieldsW1036",
      "unitStrictExactIsoDataOfComponentFieldsW1036",
      "componentFieldsOfComponentFieldsW1036",
      "currentFullDataProviderOfCurrentFullDataOfComponentFieldsW1036",
      "branchFullDataProviderOfBranchFullDataOfComponentFieldsW1036",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfComponentFieldsW1036",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfComponentFieldsW1036",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfComponentFieldsW1036",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfComponentFieldsW1036",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfComponentFieldsW1036",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfComponentFieldsW1036",
      "componentFieldsOfComponentFieldsOfComponentFieldsW1036",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfComponentFieldsW1036",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfComponentFieldsW1036",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfComponentFieldsW1036",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsW1036",
      "currentFullDataOfComponentFieldsW1036",
      "branchFullDataOfComponentFieldsW1036",
      "targetSurjectiveCompactDataOfComponentFieldsW1036",
      "fullDataOfComponentFieldsW1036",
      "directBoundedLeftCalculusOfComponentFieldsW1036",
      "boundedDerivedInfinityCategoryOfComponentFieldsW1036",
      "componentFieldsInputNamesW1036_count"]
  providerRepackagingResult :=
    "proved: W1036 constructs the W1035 W1008 current-full-data provider\
      surface from W1009 component fields and feeds W1035"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1036 inherits W1035/W1034/W1033/W1032/W1031/W1030/W1029/\
      W1028/W1027/W1026/W1025/W1024/W1023/W1022/W1021/W1020/W1019/\
      W1018/W1017/W1016/W1015/W1014/W1013/W1012/W1011/W1010/W1009/\
      W1008/W1007/W1006/W1005/W1004/W1003/W1002/W998 target\
      surjective-compact recovery after W1009 constructs W1008"
  exactAtResult :=
    "proved: the W1036 W1009 component-field provider surface feeds\
      W1035/W1034/W1033/W1032/W1031/W1030/W1029/W1028/W1027/W1026/\
      W1025/W1024/W1023/W1022/W1021/W1020/W1019/W1018/W1017/W1016/\
      W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/\
      W1005/W1004/W1003/W1002/W998/W997/W996/W995/W994/W993/W988/\
      W987/W986/W985/W984/W983/W982/W981/W980/W979/W978/W977/W976/\
      W975/W974/W973/W972/W971/W970/W969/W968/W967/W966/W965/W964/\
      W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := componentFieldsInputNamesW1036
  productSuccessClaimed := false

theorem currentW1036ComponentFieldsToCurrentFullDataDirectRoute_productSuccess :
    (let state :=
        currentMetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1036;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
