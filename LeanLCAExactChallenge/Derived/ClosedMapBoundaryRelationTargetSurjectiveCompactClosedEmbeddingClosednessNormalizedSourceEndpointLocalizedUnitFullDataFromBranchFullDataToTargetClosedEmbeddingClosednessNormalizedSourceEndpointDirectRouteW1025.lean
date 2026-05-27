import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromTargetClosedEmbeddingClosednessNormalizedSourceEndpointToTargetClosedEmbeddingClosednessDirectRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromBranchFullDataDirectRoute

/-!
W1025 replaces W1024's W1006 target/closedness/normalized-source/endpoint
surface by the existing W1007 branch-full-data surface. W1007 already
constructs W1006, and W1025 feeds that provider into W1024.
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

/-- W1025 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1007 data. -/
def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1025
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1007
    branchFullData

/-- W1025 constructs the W1005 target/closed-embedding-closedness surface from W1007 through W1024. -/
def targetClosedEmbeddingClosednessDataProviderOfBranchFullDataW1025
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1024
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1025
      branchFullData)

/-- W1025 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1007 through W1024. -/
def normalizedSourceEndpointLocalizedUnitDataProviderOfBranchFullDataW1025
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1024
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1025
      branchFullData)

/-- W1025 constructs the W1003 endpoint-localized-unit surface from W1007 through W1024. -/
def endpointLocalizedUnitDataProviderOfBranchFullDataW1025
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1024
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1025
      branchFullData)

/-- W1025 constructs the W982 localized-unit-choice surface from W1007 through W1024. -/
def localizedUnitChoiceDataOfBranchFullDataW1025
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1024
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1025
      branchFullData)

/-- W1025 constructs the W981 provider surface from W1007 through W1024. -/
noncomputable def unitStrictExactIsoDataOfBranchFullDataW1025
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1024
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1025
      branchFullData)

/-- W1025 constructs the W971 component-field surface from W1007 through W1024. -/
noncomputable def componentFieldsOfBranchFullDataW1025
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1024
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1025
      branchFullData)

/-- W1025 constructs the W1008 current-full-data surface from W1007 through W1024. -/
noncomputable def currentFullDataProviderOfBranchFullDataW1025
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1024
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1025
      branchFullData)

/-- W1025 constructs the W1007 branch-full-data surface from W1007 through W1024. -/
noncomputable def branchFullDataProviderOfBranchFullDataW1025
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1024
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1025
      branchFullData)

/-- W1025 exposes the rebuilt W982 localized-unit-choice surface after routing through W1024. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfBranchFullDataW1025
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1024
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1025
      branchFullData)

/-- W1025 exposes the rebuilt W971 component fields after routing through W1024. -/
noncomputable def componentFieldsOfComponentFieldsOfBranchFullDataW1025
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1024
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1025
      branchFullData)

/-- W1025 constructs W977 current full data from W1007 through W1024. -/
noncomputable def currentFullDataOfBranchFullDataW1025
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1024
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1025
      branchFullData)

/-- W1025 constructs W987 branch full data from W1007 through W1024. -/
noncomputable def branchFullDataOfBranchFullDataW1025
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1024
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1025
      branchFullData)

/-- W1025 recovers W715 target surjective-compact data from W1007 through W1024. -/
noncomputable def targetSurjectiveCompactDataOfBranchFullDataW1025
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1024
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1025
      branchFullData)

/-- W1025 returns the constructed W987 branch full data from W1007 through W1024. -/
noncomputable def fullDataOfBranchFullDataW1025
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1024
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1025
      branchFullData)

theorem directBoundedLeftCalculusOfBranchFullDataW1025
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1024
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1025
      branchFullData)

noncomputable def boundedDerivedInfinityCategoryOfBranchFullDataW1025
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1024
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1025
      branchFullData)

def branchFullDataInputNamesW1025 : List String :=
  branchFullDataInputNamesW1007

theorem branchFullDataInputNamesW1025_count :
    branchFullDataInputNamesW1025.length = 1 :=
  branchFullDataInputNamesW1007_count

structure MetrizableBranchFullDataToComponentFieldsDirectRouteStateW1025 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableBranchFullDataToComponentFieldsDirectRouteStateW1025 :
    MetrizableBranchFullDataToComponentFieldsDirectRouteStateW1025
    where
  seed := "w1025-branch-full-data-to-w1024-component-fields-route"
  declarations :=
    ["targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1025",
      "targetClosedEmbeddingClosednessDataProviderOfBranchFullDataW1025",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfBranchFullDataW1025",
      "endpointLocalizedUnitDataProviderOfBranchFullDataW1025",
      "localizedUnitChoiceDataOfBranchFullDataW1025",
      "unitStrictExactIsoDataOfBranchFullDataW1025",
      "componentFieldsOfBranchFullDataW1025",
      "currentFullDataProviderOfBranchFullDataW1025",
      "branchFullDataProviderOfBranchFullDataW1025",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfBranchFullDataW1025",
      "componentFieldsOfComponentFieldsOfBranchFullDataW1025",
      "currentFullDataOfBranchFullDataW1025",
      "branchFullDataOfBranchFullDataW1025",
      "targetSurjectiveCompactDataOfBranchFullDataW1025",
      "fullDataOfBranchFullDataW1025",
      "directBoundedLeftCalculusOfBranchFullDataW1025",
      "boundedDerivedInfinityCategoryOfBranchFullDataW1025",
      "branchFullDataInputNamesW1025_count"]
  providerRepackagingResult :=
    "proved: W1025 constructs the W1024 W1006 target/closedness/normalized-source/endpoint\
      provider surface from W1007 branch-full-data and feeds W1024"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1025 inherits W1024/W1023/W1022/W1021/W1020/W1019/W1018/\
      W1017/W1016/W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/\
      W1007/W1006/W1005/W1004/W1003/W1002/W998 target surjective-compact recovery after W1007 constructs W1006"
  exactAtResult :=
    "proved: the W1025 W1007 branch-full-data provider surface feeds\
      W1024/W1023/W1022/W1021/W1020/W1019/W1018/W1017/W1016/W1015/\
      W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/\
      W1004/W1003/W1002/W998/W997/W996/W995/W994/W993/W988/W987/\
      W986/W985/W984/W983/W982/W981/W980/W979/W978/W977/W976/W975/\
      W974/W973/W972/W971/W970/W969/W968/W967/W966/W965/W964/W963/\
      W962/W961/W959/W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := branchFullDataInputNamesW1025
  productSuccessClaimed := false

theorem currentW1025BranchFullDataToComponentFieldsDirectRoute_productSuccess :
    (let state :=
        currentMetrizableBranchFullDataToComponentFieldsDirectRouteStateW1025;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
