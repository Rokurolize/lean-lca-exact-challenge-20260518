import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromBranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointDirectRouteW1025
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromCurrentFullDataDirectRoute

/-!
W1026 replaces W1025's W1007 branch-full-data surface by the existing W1008
current-full-data surface. W1008 already constructs W1007 from W977 current
full data, and W1026 feeds that provider into W1025.
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

/-- W1026 constructs the W1007 branch-full-data surface from W1008 data. -/
noncomputable def branchFullDataProviderOfCurrentFullDataW1026
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfCurrentFullDataW1008 currentFullData

/-- W1026 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1008 through W1025. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1026
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1025
    (branchFullDataProviderOfCurrentFullDataW1026 currentFullData)

/-- W1026 constructs the W1005 target/closed-embedding-closedness surface from W1008 through W1025. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1026
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfBranchFullDataW1025
    (branchFullDataProviderOfCurrentFullDataW1026 currentFullData)

/-- W1026 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1008 through W1025. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1026
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfBranchFullDataW1025
    (branchFullDataProviderOfCurrentFullDataW1026 currentFullData)

/-- W1026 constructs the W1003 endpoint-localized-unit surface from W1008 through W1025. -/
noncomputable def endpointLocalizedUnitDataProviderOfCurrentFullDataW1026
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfBranchFullDataW1025
    (branchFullDataProviderOfCurrentFullDataW1026 currentFullData)

/-- W1026 constructs the W982 localized-unit-choice surface from W1008 through W1025. -/
noncomputable def localizedUnitChoiceDataOfCurrentFullDataW1026
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfBranchFullDataW1025
    (branchFullDataProviderOfCurrentFullDataW1026 currentFullData)

/-- W1026 constructs the W981 provider surface from W1008 through W1025. -/
noncomputable def unitStrictExactIsoDataOfCurrentFullDataW1026
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfBranchFullDataW1025
    (branchFullDataProviderOfCurrentFullDataW1026 currentFullData)

/-- W1026 constructs the W971 component-field surface from W1008 through W1025. -/
noncomputable def componentFieldsOfCurrentFullDataW1026
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfBranchFullDataW1025
    (branchFullDataProviderOfCurrentFullDataW1026 currentFullData)

/-- W1026 constructs the W1008 current-full-data surface from W1008 through W1025. -/
noncomputable def currentFullDataProviderOfCurrentFullDataW1026
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfBranchFullDataW1025
    (branchFullDataProviderOfCurrentFullDataW1026 currentFullData)

/-- W1026 exposes the rebuilt W1007 branch-full-data surface after routing through W1025. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfCurrentFullDataW1026
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataW1025
    (branchFullDataProviderOfCurrentFullDataW1026 currentFullData)

/-- W1026 exposes the rebuilt W982 localized-unit-choice surface after routing through W1025. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfCurrentFullDataW1026
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfBranchFullDataW1025
    (branchFullDataProviderOfCurrentFullDataW1026 currentFullData)

/-- W1026 exposes the rebuilt W971 component fields after routing through W1025. -/
noncomputable def componentFieldsOfComponentFieldsOfCurrentFullDataW1026
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfBranchFullDataW1025
    (branchFullDataProviderOfCurrentFullDataW1026 currentFullData)

/-- W1026 constructs W977 current full data from W1008 through W1025. -/
noncomputable def currentFullDataOfCurrentFullDataW1026
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfBranchFullDataW1025
    (branchFullDataProviderOfCurrentFullDataW1026 currentFullData)

/-- W1026 constructs W987 branch full data from W1008 through W1025. -/
noncomputable def branchFullDataOfCurrentFullDataW1026
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfBranchFullDataW1025
    (branchFullDataProviderOfCurrentFullDataW1026 currentFullData)

/-- W1026 recovers W715 target surjective-compact data from W1008 through W1025. -/
noncomputable def targetSurjectiveCompactDataOfCurrentFullDataW1026
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfBranchFullDataW1025
    (branchFullDataProviderOfCurrentFullDataW1026 currentFullData)

/-- W1026 returns the constructed W987 branch full data from W1008 through W1025. -/
noncomputable def fullDataOfCurrentFullDataW1026
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfBranchFullDataW1025
    (branchFullDataProviderOfCurrentFullDataW1026 currentFullData)

theorem directBoundedLeftCalculusOfCurrentFullDataW1026
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfBranchFullDataW1025
    (branchFullDataProviderOfCurrentFullDataW1026 currentFullData)

noncomputable def boundedDerivedInfinityCategoryOfCurrentFullDataW1026
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfBranchFullDataW1025
    (branchFullDataProviderOfCurrentFullDataW1026 currentFullData)

def currentFullDataInputNamesW1026 : List String :=
  currentFullDataInputNamesW1008

theorem currentFullDataInputNamesW1026_count :
    currentFullDataInputNamesW1026.length = 1 :=
  currentFullDataInputNamesW1008_count

structure MetrizableCurrentFullDataToComponentFieldsDirectRouteStateW1026 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableCurrentFullDataToComponentFieldsDirectRouteStateW1026 :
    MetrizableCurrentFullDataToComponentFieldsDirectRouteStateW1026
    where
  seed := "w1026-current-full-data-to-w1025-component-fields-route"
  declarations :=
    ["branchFullDataProviderOfCurrentFullDataW1026",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1026",
      "targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1026",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1026",
      "endpointLocalizedUnitDataProviderOfCurrentFullDataW1026",
      "localizedUnitChoiceDataOfCurrentFullDataW1026",
      "unitStrictExactIsoDataOfCurrentFullDataW1026",
      "componentFieldsOfCurrentFullDataW1026",
      "currentFullDataProviderOfCurrentFullDataW1026",
      "branchFullDataProviderOfBranchFullDataOfCurrentFullDataW1026",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfCurrentFullDataW1026",
      "componentFieldsOfComponentFieldsOfCurrentFullDataW1026",
      "currentFullDataOfCurrentFullDataW1026",
      "branchFullDataOfCurrentFullDataW1026",
      "targetSurjectiveCompactDataOfCurrentFullDataW1026",
      "fullDataOfCurrentFullDataW1026",
      "directBoundedLeftCalculusOfCurrentFullDataW1026",
      "boundedDerivedInfinityCategoryOfCurrentFullDataW1026",
      "currentFullDataInputNamesW1026_count"]
  providerRepackagingResult :=
    "proved: W1026 constructs the W1025 W1007 branch-full-data provider\
      surface from W1008 current full data and feeds W1025"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1026 inherits W1025/W1024/W1023/W1022/W1021/W1020/W1019/\
      W1018/W1017/W1016/W1015/W1014/W1013/W1012/W1011/W1010/W1009/\
      W1008/W1007/W1006/W1005/W1004/W1003/W1002/W998 target\
      surjective-compact recovery after W1008 constructs W1007"
  exactAtResult :=
    "proved: the W1026 W1008 current-full-data provider surface feeds\
      W1025/W1024/W1023/W1022/W1021/W1020/W1019/W1018/W1017/W1016/\
      W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/\
      W1005/W1004/W1003/W1002/W998/W997/W996/W995/W994/W993/W988/\
      W987/W986/W985/W984/W983/W982/W981/W980/W979/W978/W977/W976/\
      W975/W974/W973/W972/W971/W970/W969/W968/W967/W966/W965/W964/\
      W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/W952 stable\
      ExactAt route"
  remainingInputs := currentFullDataInputNamesW1026
  productSuccessClaimed := false

theorem currentW1026CurrentFullDataToComponentFieldsDirectRoute_productSuccess :
    (let state :=
        currentMetrizableCurrentFullDataToComponentFieldsDirectRouteStateW1026;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
