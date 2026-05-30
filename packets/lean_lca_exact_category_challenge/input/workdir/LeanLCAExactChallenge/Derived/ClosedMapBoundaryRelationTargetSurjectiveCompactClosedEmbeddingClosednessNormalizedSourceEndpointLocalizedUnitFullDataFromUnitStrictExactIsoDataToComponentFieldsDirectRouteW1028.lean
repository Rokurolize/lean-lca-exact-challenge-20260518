import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromComponentFieldsToCurrentFullDataDirectRouteW1027
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromUnitStrictExactIsoDataDirectRoute

/-!
W1028 replaces W1027's W1009 component-field surface by the existing W1010
endpoint/unit-strict-exact provider surface. W1010 already constructs W971
component fields from W981, and W1028 feeds those fields into W1027.
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

/-- W1028 constructs the W1027 component-field surface from W981 data through W1010. -/
def componentFieldsOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfUnitStrictExactIsoDataW1010 unitStrictExactIsoData

/-- W1028 constructs the W1008 current-full-data surface from W981 data through W1027. -/
noncomputable def currentFullDataProviderOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfComponentFieldsW1027
    (componentFieldsOfUnitStrictExactIsoDataW1028 unitStrictExactIsoData)

/-- W1028 constructs the W1007 branch-full-data surface from W981 data through W1027. -/
noncomputable def branchFullDataProviderOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfComponentFieldsW1027
    (componentFieldsOfUnitStrictExactIsoDataW1028 unitStrictExactIsoData)

/-- W1028 constructs the W1006 target/closedness/normalized-source/endpoint surface from W981 data through W1027. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfComponentFieldsW1027
    (componentFieldsOfUnitStrictExactIsoDataW1028 unitStrictExactIsoData)

/-- W1028 constructs the W1005 target/closed-embedding-closedness surface from W981 data through W1027. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfComponentFieldsW1027
    (componentFieldsOfUnitStrictExactIsoDataW1028 unitStrictExactIsoData)

/-- W1028 constructs the W1004 normalized-source/endpoint-localized-unit surface from W981 data through W1027. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfComponentFieldsW1027
    (componentFieldsOfUnitStrictExactIsoDataW1028 unitStrictExactIsoData)

/-- W1028 constructs the W1003 endpoint-localized-unit surface from W981 data through W1027. -/
noncomputable def endpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfComponentFieldsW1027
    (componentFieldsOfUnitStrictExactIsoDataW1028 unitStrictExactIsoData)

/-- W1028 constructs the W982 localized-unit-choice surface from W981 data through W1027. -/
noncomputable def localizedUnitChoiceDataOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfComponentFieldsW1027
    (componentFieldsOfUnitStrictExactIsoDataW1028 unitStrictExactIsoData)

/-- W1028 exposes the rebuilt W981 surface after routing through W1027. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfComponentFieldsW1027
    (componentFieldsOfUnitStrictExactIsoDataW1028 unitStrictExactIsoData)

/-- W1028 exposes the rebuilt W971 component fields after routing through W1027. -/
noncomputable def componentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsW1027
    (componentFieldsOfUnitStrictExactIsoDataW1028 unitStrictExactIsoData)

/-- W1028 exposes the rebuilt W1008 current-full-data surface after routing through W1027. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfComponentFieldsW1027
    (componentFieldsOfUnitStrictExactIsoDataW1028 unitStrictExactIsoData)

/-- W1028 exposes the rebuilt W1007 branch-full-data surface after routing through W1027. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfComponentFieldsW1027
    (componentFieldsOfUnitStrictExactIsoDataW1028 unitStrictExactIsoData)

/-- W1028 exposes the rebuilt W982 localized-unit-choice surface after routing through W1027. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfComponentFieldsW1027
    (componentFieldsOfUnitStrictExactIsoDataW1028 unitStrictExactIsoData)

/-- W1028 exposes the twice-rebuilt W971 component fields after routing through W1027. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsW1027
    (componentFieldsOfUnitStrictExactIsoDataW1028 unitStrictExactIsoData)

/-- W1028 constructs W977 current full data from W981 data through W1027. -/
noncomputable def currentFullDataOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfComponentFieldsW1027
    (componentFieldsOfUnitStrictExactIsoDataW1028 unitStrictExactIsoData)

/-- W1028 constructs W987 branch full data from W981 data through W1027. -/
noncomputable def branchFullDataOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfComponentFieldsW1027
    (componentFieldsOfUnitStrictExactIsoDataW1028 unitStrictExactIsoData)

/-- W1028 recovers W715 target surjective-compact data from W981 data through W1027. -/
noncomputable def targetSurjectiveCompactDataOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfComponentFieldsW1027
    (componentFieldsOfUnitStrictExactIsoDataW1028 unitStrictExactIsoData)

/-- W1028 returns the constructed W987 branch full data from W981 data through W1027. -/
noncomputable def fullDataOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfComponentFieldsW1027
    (componentFieldsOfUnitStrictExactIsoDataW1028 unitStrictExactIsoData)

theorem directBoundedLeftCalculusOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfComponentFieldsW1027
    (componentFieldsOfUnitStrictExactIsoDataW1028 unitStrictExactIsoData)

noncomputable def boundedDerivedInfinityCategoryOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfComponentFieldsW1027
    (componentFieldsOfUnitStrictExactIsoDataW1028 unitStrictExactIsoData)

def unitStrictExactIsoDataInputNamesW1028 : List String :=
  unitStrictExactIsoDataInputNamesW1010

theorem unitStrictExactIsoDataInputNamesW1028_count :
    unitStrictExactIsoDataInputNamesW1028.length = 7 :=
  unitStrictExactIsoDataInputNamesW1010_count

structure MetrizableUnitStrictExactIsoDataToComponentFieldsDirectRouteStateW1028 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableUnitStrictExactIsoDataToComponentFieldsDirectRouteStateW1028 :
    MetrizableUnitStrictExactIsoDataToComponentFieldsDirectRouteStateW1028
    where
  seed := "w1028-unit-strict-exact-iso-data-to-w1027-component-fields-route"
  declarations :=
    ["componentFieldsOfUnitStrictExactIsoDataW1028",
      "currentFullDataProviderOfUnitStrictExactIsoDataW1028",
      "branchFullDataProviderOfUnitStrictExactIsoDataW1028",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfUnitStrictExactIsoDataW1028",
      "targetClosedEmbeddingClosednessDataProviderOfUnitStrictExactIsoDataW1028",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1028",
      "endpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1028",
      "localizedUnitChoiceDataOfUnitStrictExactIsoDataW1028",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataW1028",
      "componentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1028",
      "currentFullDataProviderOfCurrentFullDataOfUnitStrictExactIsoDataW1028",
      "branchFullDataProviderOfBranchFullDataOfUnitStrictExactIsoDataW1028",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfUnitStrictExactIsoDataW1028",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1028",
      "currentFullDataOfUnitStrictExactIsoDataW1028",
      "branchFullDataOfUnitStrictExactIsoDataW1028",
      "targetSurjectiveCompactDataOfUnitStrictExactIsoDataW1028",
      "fullDataOfUnitStrictExactIsoDataW1028",
      "directBoundedLeftCalculusOfUnitStrictExactIsoDataW1028",
      "boundedDerivedInfinityCategoryOfUnitStrictExactIsoDataW1028",
      "unitStrictExactIsoDataInputNamesW1028_count"]
  providerRepackagingResult :=
    "proved: W1028 constructs the W1027 W971 component-field surface from\
      W981 endpoint/unit-strict-exact provider data through W1010 and feeds\
      W1027"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1028 inherits W1027/W1026/W1025/W1024/W1023/W1022/W1021/\
      W1020/W1019/W1018/W1017/W1016/W1015/W1014/W1013/W1012/W1011/\
      W1010/W1009/W1008/W1007/W1006/W1005/W1004/W1003/W1002/W998\
      target surjective-compact recovery after W1010 constructs W971 fields"
  exactAtResult :=
    "proved: the W1028 W981 endpoint/unit-strict-exact provider surface feeds\
      W1027/W1026/W1025/W1024/W1023/W1022/W1021/W1020/W1019/W1018/\
      W1017/W1016/W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/\
      W1007/W1006/W1005/W1004/W1003/W1002/W998/W997/W996/W995/W994/\
      W993/W988/W987/W986/W985/W984/W983/W982/W981/W980/W979/W978/W977/\
      W976/W975/W974/W973/W972/W971/W970/W969/W968/W967/W966/W965/\
      W964/W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/W952\
      stable ExactAt route"
  remainingInputs := unitStrictExactIsoDataInputNamesW1028
  productSuccessClaimed := false

theorem currentW1028UnitStrictExactIsoDataToComponentFieldsDirectRoute_productSuccess :
    (let state :=
        currentMetrizableUnitStrictExactIsoDataToComponentFieldsDirectRouteStateW1028;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
