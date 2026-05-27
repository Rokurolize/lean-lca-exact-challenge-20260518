import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromComponentFieldsToCurrentFullDataDirectRouteW1045
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromUnitStrictExactIsoDataDirectRoute

/-!
W1046 replaces W1045's W1009 component-field surface by the existing W1010
endpoint/unit-strict-exact provider surface. W1010 already constructs W971
component fields from W981, and W1046 feeds those fields into W1045.
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

/-- W1046 constructs the W1045 component-field surface from W981 data through W1010. -/
def componentFieldsOfUnitStrictExactIsoDataW1046
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfUnitStrictExactIsoDataW1010 unitStrictExactIsoData

/-- W1046 constructs the W1008 current-full-data surface from W981 data through W1045. -/
noncomputable def currentFullDataProviderOfUnitStrictExactIsoDataW1046
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfComponentFieldsW1045
    (componentFieldsOfUnitStrictExactIsoDataW1046 unitStrictExactIsoData)

/-- W1046 constructs the W1007 branch-full-data surface from W981 data through W1045. -/
noncomputable def branchFullDataProviderOfUnitStrictExactIsoDataW1046
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfComponentFieldsW1045
    (componentFieldsOfUnitStrictExactIsoDataW1046 unitStrictExactIsoData)

/-- W1046 constructs the W1006 target/closedness/normalized-source/endpoint surface from W981 data through W1045. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfUnitStrictExactIsoDataW1046
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfComponentFieldsW1045
    (componentFieldsOfUnitStrictExactIsoDataW1046 unitStrictExactIsoData)

/-- W1046 constructs the W1005 target/closed-embedding-closedness surface from W981 data through W1045. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfUnitStrictExactIsoDataW1046
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfComponentFieldsW1045
    (componentFieldsOfUnitStrictExactIsoDataW1046 unitStrictExactIsoData)

/-- W1046 constructs the W1004 normalized-source/endpoint-localized-unit surface from W981 data through W1045. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1046
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfComponentFieldsW1045
    (componentFieldsOfUnitStrictExactIsoDataW1046 unitStrictExactIsoData)

/-- W1046 constructs the W1003 endpoint-localized-unit surface from W981 data through W1045. -/
noncomputable def endpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1046
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfComponentFieldsW1045
    (componentFieldsOfUnitStrictExactIsoDataW1046 unitStrictExactIsoData)

/-- W1046 constructs the W982 localized-unit-choice surface from W981 data through W1045. -/
noncomputable def localizedUnitChoiceDataOfUnitStrictExactIsoDataW1046
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfComponentFieldsW1045
    (componentFieldsOfUnitStrictExactIsoDataW1046 unitStrictExactIsoData)

/-- W1046 exposes the rebuilt W981 surface after routing through W1045. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataW1046
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfComponentFieldsW1045
    (componentFieldsOfUnitStrictExactIsoDataW1046 unitStrictExactIsoData)

/-- W1046 exposes the rebuilt W971 component fields after routing through W1045. -/
noncomputable def componentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1046
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsW1045
    (componentFieldsOfUnitStrictExactIsoDataW1046 unitStrictExactIsoData)

/-- W1046 exposes the rebuilt W1008 current-full-data surface after routing through W1045. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfUnitStrictExactIsoDataW1046
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfComponentFieldsW1045
    (componentFieldsOfUnitStrictExactIsoDataW1046 unitStrictExactIsoData)

/-- W1046 exposes the rebuilt W1007 branch-full-data surface after routing through W1045. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfUnitStrictExactIsoDataW1046
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfComponentFieldsW1045
    (componentFieldsOfUnitStrictExactIsoDataW1046 unitStrictExactIsoData)

/-- W1046 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1045. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfUnitStrictExactIsoDataW1046
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfComponentFieldsW1045
    (componentFieldsOfUnitStrictExactIsoDataW1046 unitStrictExactIsoData)

/-- W1046 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1045. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfUnitStrictExactIsoDataW1046
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfComponentFieldsW1045
    (componentFieldsOfUnitStrictExactIsoDataW1046 unitStrictExactIsoData)

/-- W1046 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1045. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfUnitStrictExactIsoDataW1046
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfComponentFieldsW1045
    (componentFieldsOfUnitStrictExactIsoDataW1046 unitStrictExactIsoData)

/-- W1046 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1045. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfUnitStrictExactIsoDataW1046
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfComponentFieldsW1045
    (componentFieldsOfUnitStrictExactIsoDataW1046 unitStrictExactIsoData)

/-- W1046 exposes the rebuilt W982 localized-unit-choice surface after routing through W1045. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfUnitStrictExactIsoDataW1046
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfComponentFieldsW1045
    (componentFieldsOfUnitStrictExactIsoDataW1046 unitStrictExactIsoData)

/-- W1046 exposes the rebuilt W981 surface after the nested W1045 pass. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataW1046
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfComponentFieldsW1045
    (componentFieldsOfUnitStrictExactIsoDataW1046 unitStrictExactIsoData)

/-- W1046 exposes the rebuilt W971 component fields after the nested W1045 pass. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1046
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsW1045
    (componentFieldsOfUnitStrictExactIsoDataW1046 unitStrictExactIsoData)

/-- W1046 exposes the rebuilt W1008 current-full-data surface after the nested W1045 pass. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfUnitStrictExactIsoDataW1046
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfComponentFieldsW1045
    (componentFieldsOfUnitStrictExactIsoDataW1046 unitStrictExactIsoData)

/-- W1046 exposes the rebuilt W1007 branch-full-data surface after the nested W1045 pass. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfUnitStrictExactIsoDataW1046
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataOfComponentFieldsW1045
    (componentFieldsOfUnitStrictExactIsoDataW1046 unitStrictExactIsoData)

/-- W1046 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1045. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfUnitStrictExactIsoDataW1046
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfComponentFieldsW1045
    (componentFieldsOfUnitStrictExactIsoDataW1046 unitStrictExactIsoData)

/-- W1046 exposes the twice-rebuilt W971 component fields after routing through W1045. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1046
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsW1045
    (componentFieldsOfUnitStrictExactIsoDataW1046 unitStrictExactIsoData)

/-- W1046 constructs W977 current full data from W981 data through W1045. -/
noncomputable def currentFullDataOfUnitStrictExactIsoDataW1046
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfComponentFieldsW1045
    (componentFieldsOfUnitStrictExactIsoDataW1046 unitStrictExactIsoData)

/-- W1046 constructs W987 branch full data from W981 data through W1045. -/
noncomputable def branchFullDataOfUnitStrictExactIsoDataW1046
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfComponentFieldsW1045
    (componentFieldsOfUnitStrictExactIsoDataW1046 unitStrictExactIsoData)

/-- W1046 recovers W715 target surjective-compact data from W981 data through W1045. -/
noncomputable def targetSurjectiveCompactDataOfUnitStrictExactIsoDataW1046
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfComponentFieldsW1045
    (componentFieldsOfUnitStrictExactIsoDataW1046 unitStrictExactIsoData)

/-- W1046 returns the constructed W987 branch full data from W981 data through W1045. -/
noncomputable def fullDataOfUnitStrictExactIsoDataW1046
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfComponentFieldsW1045
    (componentFieldsOfUnitStrictExactIsoDataW1046 unitStrictExactIsoData)

theorem directBoundedLeftCalculusOfUnitStrictExactIsoDataW1046
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfComponentFieldsW1045
    (componentFieldsOfUnitStrictExactIsoDataW1046 unitStrictExactIsoData)

noncomputable def boundedDerivedInfinityCategoryOfUnitStrictExactIsoDataW1046
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfComponentFieldsW1045
    (componentFieldsOfUnitStrictExactIsoDataW1046 unitStrictExactIsoData)

def unitStrictExactIsoDataInputNamesW1046 : List String :=
  unitStrictExactIsoDataInputNamesW1010

theorem unitStrictExactIsoDataInputNamesW1046_count :
    unitStrictExactIsoDataInputNamesW1046.length = 7 :=
  unitStrictExactIsoDataInputNamesW1010_count

structure MetrizableUnitStrictExactIsoDataToComponentFieldsDirectRouteStateW1046 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableUnitStrictExactIsoDataToComponentFieldsDirectRouteStateW1046 :
    MetrizableUnitStrictExactIsoDataToComponentFieldsDirectRouteStateW1046
    where
  seed := "w1046-unit-strict-exact-iso-data-to-w1045-component-fields-route"
  declarations :=
    ["componentFieldsOfUnitStrictExactIsoDataW1046",
      "currentFullDataProviderOfUnitStrictExactIsoDataW1046",
      "branchFullDataProviderOfUnitStrictExactIsoDataW1046",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfUnitStrictExactIsoDataW1046",
      "targetClosedEmbeddingClosednessDataProviderOfUnitStrictExactIsoDataW1046",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1046",
      "endpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1046",
      "localizedUnitChoiceDataOfUnitStrictExactIsoDataW1046",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataW1046",
      "componentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1046",
      "currentFullDataProviderOfCurrentFullDataOfUnitStrictExactIsoDataW1046",
      "branchFullDataProviderOfBranchFullDataOfUnitStrictExactIsoDataW1046",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfUnitStrictExactIsoDataW1046",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfUnitStrictExactIsoDataW1046",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfUnitStrictExactIsoDataW1046",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfUnitStrictExactIsoDataW1046",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfUnitStrictExactIsoDataW1046",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataW1046",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1046",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfUnitStrictExactIsoDataW1046",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfUnitStrictExactIsoDataW1046",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfUnitStrictExactIsoDataW1046",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1046",
      "currentFullDataOfUnitStrictExactIsoDataW1046",
      "branchFullDataOfUnitStrictExactIsoDataW1046",
      "targetSurjectiveCompactDataOfUnitStrictExactIsoDataW1046",
      "fullDataOfUnitStrictExactIsoDataW1046",
      "directBoundedLeftCalculusOfUnitStrictExactIsoDataW1046",
      "boundedDerivedInfinityCategoryOfUnitStrictExactIsoDataW1046",
      "unitStrictExactIsoDataInputNamesW1046_count"]
  providerRepackagingResult :=
    "proved: W1046 constructs the W1045 W971 component-field surface from\
      W981 endpoint/unit-strict-exact provider data through W1010 and feeds\
      W1045"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1046 inherits W1045/W1044/W1043/W1042/W1041/W1040/\
      W1039/W1038/W1037/W1036/W1035/W1034/W1033/W1032/W1031/W1030/\
      W1029/W1028/W1027/W1026/W1025/W1024/W1023/W1022/W1021/W1020/\
      W1019/W1018/W1017/W1016/W1015/W1014/W1013/W1012/W1011/W1010/\
      W1009/W1008/W1007/W1006/W1005/W1004/W1003/W1002/W998 target\
      surjective-compact recovery after W1010 constructs W971 fields"
  exactAtResult :=
    "proved: the W1046 W981 endpoint/unit-strict-exact provider surface feeds\
      W1045/W1044/W1043/W1042/W1041/W1040/W1039/W1038/W1037/W1036/\
      W1035/W1034/W1033/W1032/W1031/W1030/W1029/W1028/W1027/W1026/\
      W1025/W1024/W1023/W1022/W1021/W1020/W1019/W1018/W1017/W1016/\
      W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/\
      W1005/W1004/W1003/W1002/W998/W997/W996/W995/W994/W993/W988/\
      W987/W986/W985/W984/W983/W982/W981/W980/W979/W978/W977/W976/\
      W975/W974/W973/W972/W971/W970/W969/W968/W967/W966/W965/W964/\
      W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := unitStrictExactIsoDataInputNamesW1046
  productSuccessClaimed := false

theorem currentW1046UnitStrictExactIsoDataToComponentFieldsDirectRoute_productSuccess :
    (let state :=
        currentMetrizableUnitStrictExactIsoDataToComponentFieldsDirectRouteStateW1046;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
