import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromCurrentFullDataToBranchFullDataDirectRouteW1044
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromComponentFieldsDirectRoute

/-!
W1045 replaces W1044's W1008 current-full-data surface by the existing W1009
component-field surface. W1009 already constructs W1008 from W971 component
fields through W978, and W1045 feeds that provider into W1044.
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

/-- W1045 constructs the W1008 current-full-data surface from W1009 component fields. -/
def currentFullDataProviderOfComponentFieldsW1045
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfComponentFieldsW1009 componentFields

/-- W1045 constructs the W1007 branch-full-data surface from W1009 through W1044. -/
noncomputable def branchFullDataProviderOfComponentFieldsW1045
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfCurrentFullDataW1044
    (currentFullDataProviderOfComponentFieldsW1045 componentFields)

/-- W1045 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1009 through W1044. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfComponentFieldsW1045
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1044
    (currentFullDataProviderOfComponentFieldsW1045 componentFields)

/-- W1045 constructs the W1005 target/closed-embedding-closedness surface from W1009 through W1044. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfComponentFieldsW1045
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1044
    (currentFullDataProviderOfComponentFieldsW1045 componentFields)

/-- W1045 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1009 through W1044. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfComponentFieldsW1045
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1044
    (currentFullDataProviderOfComponentFieldsW1045 componentFields)

/-- W1045 constructs the W1003 endpoint-localized-unit surface from W1009 through W1044. -/
noncomputable def endpointLocalizedUnitDataProviderOfComponentFieldsW1045
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfCurrentFullDataW1044
    (currentFullDataProviderOfComponentFieldsW1045 componentFields)

/-- W1045 constructs the W982 localized-unit-choice surface from W1009 through W1044. -/
noncomputable def localizedUnitChoiceDataOfComponentFieldsW1045
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfCurrentFullDataW1044
    (currentFullDataProviderOfComponentFieldsW1045 componentFields)

/-- W1045 constructs the W981 provider surface from W1009 through W1044. -/
noncomputable def unitStrictExactIsoDataOfComponentFieldsW1045
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfCurrentFullDataW1044
    (currentFullDataProviderOfComponentFieldsW1045 componentFields)

/-- W1045 constructs the W971 component-field surface from W1009 through W1044. -/
noncomputable def componentFieldsOfComponentFieldsW1045
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfCurrentFullDataW1044
    (currentFullDataProviderOfComponentFieldsW1045 componentFields)

/-- W1045 exposes the rebuilt W1008 current-full-data surface after routing through W1044. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfComponentFieldsW1045
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataW1044
    (currentFullDataProviderOfComponentFieldsW1045 componentFields)

/-- W1045 exposes the rebuilt W1007 branch-full-data surface after routing through W1044. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfComponentFieldsW1045
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfCurrentFullDataW1044
    (currentFullDataProviderOfComponentFieldsW1045 componentFields)

/-- W1045 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1044. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfComponentFieldsW1045
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfCurrentFullDataW1044
    (currentFullDataProviderOfComponentFieldsW1045 componentFields)

/-- W1045 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1044. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfComponentFieldsW1045
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfCurrentFullDataW1044
    (currentFullDataProviderOfComponentFieldsW1045 componentFields)

/-- W1045 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1044. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfComponentFieldsW1045
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfCurrentFullDataW1044
    (currentFullDataProviderOfComponentFieldsW1045 componentFields)

/-- W1045 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1044. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfComponentFieldsW1045
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfCurrentFullDataW1044
    (currentFullDataProviderOfComponentFieldsW1045 componentFields)

/-- W1045 exposes the rebuilt W982 localized-unit-choice surface after routing through W1044. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfComponentFieldsW1045
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfCurrentFullDataW1044
    (currentFullDataProviderOfComponentFieldsW1045 componentFields)

/-- W1045 exposes the rebuilt W981 surface after routing through W1044. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfComponentFieldsW1045
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfCurrentFullDataW1044
    (currentFullDataProviderOfComponentFieldsW1045 componentFields)

/-- W1045 exposes the rebuilt W971 component fields after routing through W1044. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsW1045
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfCurrentFullDataW1044
    (currentFullDataProviderOfComponentFieldsW1045 componentFields)

/-- W1045 exposes the rebuilt W1008 current-full-data surface after routing through W1044. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfComponentFieldsW1045
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfCurrentFullDataW1044
    (currentFullDataProviderOfComponentFieldsW1045 componentFields)

/-- W1045 exposes the rebuilt W1007 branch-full-data surface after routing through W1044. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfComponentFieldsW1045
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataOfCurrentFullDataW1044
    (currentFullDataProviderOfComponentFieldsW1045 componentFields)

/-- W1045 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1044. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfComponentFieldsW1045
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfCurrentFullDataW1044
    (currentFullDataProviderOfComponentFieldsW1045 componentFields)

/-- W1045 exposes the twice-rebuilt W971 component fields after routing through W1044. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsW1045
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfCurrentFullDataW1044
    (currentFullDataProviderOfComponentFieldsW1045 componentFields)

/-- W1045 constructs W977 current full data from W1009 through W1044. -/
noncomputable def currentFullDataOfComponentFieldsW1045
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfCurrentFullDataW1044
    (currentFullDataProviderOfComponentFieldsW1045 componentFields)

/-- W1045 constructs W987 branch full data from W1009 through W1044. -/
noncomputable def branchFullDataOfComponentFieldsW1045
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfCurrentFullDataW1044
    (currentFullDataProviderOfComponentFieldsW1045 componentFields)

/-- W1045 recovers W715 target surjective-compact data from W1009 through W1044. -/
noncomputable def targetSurjectiveCompactDataOfComponentFieldsW1045
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfCurrentFullDataW1044
    (currentFullDataProviderOfComponentFieldsW1045 componentFields)

/-- W1045 returns the constructed W987 branch full data from W1009 through W1044. -/
noncomputable def fullDataOfComponentFieldsW1045
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfCurrentFullDataW1044
    (currentFullDataProviderOfComponentFieldsW1045 componentFields)

theorem directBoundedLeftCalculusOfComponentFieldsW1045
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfCurrentFullDataW1044
    (currentFullDataProviderOfComponentFieldsW1045 componentFields)

noncomputable def boundedDerivedInfinityCategoryOfComponentFieldsW1045
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfCurrentFullDataW1044
    (currentFullDataProviderOfComponentFieldsW1045 componentFields)

def componentFieldsInputNamesW1045 : List String :=
  componentFieldsInputNamesW1009

theorem componentFieldsInputNamesW1045_count :
    componentFieldsInputNamesW1045.length = 18 :=
  componentFieldsInputNamesW1009_count

structure MetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1045 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1045 :
    MetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1045
    where
  seed := "w1045-component-fields-to-w1044-current-full-data-route"
  declarations :=
    ["currentFullDataProviderOfComponentFieldsW1045",
      "branchFullDataProviderOfComponentFieldsW1045",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfComponentFieldsW1045",
      "targetClosedEmbeddingClosednessDataProviderOfComponentFieldsW1045",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfComponentFieldsW1045",
      "endpointLocalizedUnitDataProviderOfComponentFieldsW1045",
      "localizedUnitChoiceDataOfComponentFieldsW1045",
      "unitStrictExactIsoDataOfComponentFieldsW1045",
      "componentFieldsOfComponentFieldsW1045",
      "currentFullDataProviderOfCurrentFullDataOfComponentFieldsW1045",
      "branchFullDataProviderOfBranchFullDataOfComponentFieldsW1045",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfComponentFieldsW1045",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfComponentFieldsW1045",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfComponentFieldsW1045",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfComponentFieldsW1045",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfComponentFieldsW1045",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfComponentFieldsW1045",
      "componentFieldsOfComponentFieldsOfComponentFieldsW1045",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfComponentFieldsW1045",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfComponentFieldsW1045",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfComponentFieldsW1045",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsW1045",
      "currentFullDataOfComponentFieldsW1045",
      "branchFullDataOfComponentFieldsW1045",
      "targetSurjectiveCompactDataOfComponentFieldsW1045",
      "fullDataOfComponentFieldsW1045",
      "directBoundedLeftCalculusOfComponentFieldsW1045",
      "boundedDerivedInfinityCategoryOfComponentFieldsW1045",
      "componentFieldsInputNamesW1045_count"]
  providerRepackagingResult :=
    "proved: W1045 constructs the W1044 W1008 current-full-data provider\
      surface from W1009 component fields and feeds W1044"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1045 inherits W1044/W1043/W1042/W1041/W1040/W1039/\
      W1038/W1037/W1036/W1035/W1034/W1033/W1032/W1031/W1030/W1029/\
      W1028/W1027/W1026/W1025/W1024/W1023/W1022/W1021/W1020/W1019/\
      W1018/W1017/W1016/W1015/W1014/W1013/W1012/W1011/W1010/W1009/\
      W1008/W1007/W1006/W1005/W1004/W1003/W1002/W998 target\
      surjective-compact recovery after W1009 constructs W1008"
  exactAtResult :=
    "proved: the W1045 W1009 component-field provider surface feeds\
      W1044/W1043/W1042/W1041/W1040/W1039/W1038/W1037/W1036/W1035/\
      W1034/W1033/W1032/W1031/W1030/W1029/W1028/W1027/W1026/W1025/\
      W1024/W1023/W1022/W1021/W1020/W1019/W1018/W1017/W1016/W1015/\
      W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/\
      W1004/W1003/W1002/W998/W997/W996/W995/W994/W993/W988/W987/\
      W986/W985/W984/W983/W982/W981/W980/W979/W978/W977/W976/W975/\
      W974/W973/W972/W971/W970/W969/W968/W967/W966/W965/W964/W963/\
      W962/W961/W959/W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := componentFieldsInputNamesW1045
  productSuccessClaimed := false

theorem currentW1045ComponentFieldsToCurrentFullDataDirectRoute_productSuccess :
    (let state :=
        currentMetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1045;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
