import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromBranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointDirectRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromCurrentFullDataDirectRoute

/-!
W1017 replaces W1016's W1007 branch-full-data surface by the existing W1008
current-full-data surface. W1008 already constructs W1007 from W977 current
full data through W999, and W1017 feeds that provider into W1016.
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

/-- W1017 constructs the W1007 branch-full-data surface from W1008 data. -/
noncomputable def branchFullDataProviderOfCurrentFullDataW1017
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfCurrentFullDataW1008 currentFullData

/-- W1017 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1008 through W1016. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1017
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1016
    (branchFullDataProviderOfCurrentFullDataW1017 currentFullData)

/-- W1017 constructs the W1005 target/closed-embedding-closedness surface from W1008 through W1016. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1017
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfBranchFullDataW1016
    (branchFullDataProviderOfCurrentFullDataW1017 currentFullData)

/-- W1017 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1008 through W1016. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1017
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfBranchFullDataW1016
    (branchFullDataProviderOfCurrentFullDataW1017 currentFullData)

/-- W1017 constructs the W982 localized-unit-choice surface from W1008 through W1016. -/
noncomputable def localizedUnitChoiceDataOfCurrentFullDataW1017
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfBranchFullDataW1016
    (branchFullDataProviderOfCurrentFullDataW1017 currentFullData)

/-- W1017 constructs the W971 component-field surface from W1008 through W1016. -/
noncomputable def componentFieldsOfCurrentFullDataW1017
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfBranchFullDataW1016
    (branchFullDataProviderOfCurrentFullDataW1017 currentFullData)

/-- W1017 constructs W977 current full data from W1008 through W1016. -/
noncomputable def currentFullDataOfCurrentFullDataW1017
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfBranchFullDataW1016
    (branchFullDataProviderOfCurrentFullDataW1017 currentFullData)

/-- W1017 builds the W1008 provider surface through W1016. -/
noncomputable def currentFullDataProviderOfCurrentFullDataW1017
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfBranchFullDataW1016
    (branchFullDataProviderOfCurrentFullDataW1017 currentFullData)

/-- W1017 constructs W987 branch full data through W1016. -/
noncomputable def branchFullDataOfCurrentFullDataW1017
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfBranchFullDataW1016
    (branchFullDataProviderOfCurrentFullDataW1017 currentFullData)

/-- W1017 recovers W715 target surjective-compact data through W1016. -/
noncomputable def targetSurjectiveCompactDataOfCurrentFullDataW1017
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfBranchFullDataW1016
    (branchFullDataProviderOfCurrentFullDataW1017 currentFullData)

/-- W1017 returns the constructed W987 branch full data through W1016. -/
noncomputable def fullDataOfCurrentFullDataW1017
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfBranchFullDataW1016
    (branchFullDataProviderOfCurrentFullDataW1017 currentFullData)

theorem directBoundedLeftCalculusOfCurrentFullDataW1017
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfBranchFullDataW1016
    (branchFullDataProviderOfCurrentFullDataW1017 currentFullData)

noncomputable def boundedDerivedInfinityCategoryOfCurrentFullDataW1017
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfBranchFullDataW1016
    (branchFullDataProviderOfCurrentFullDataW1017 currentFullData)

def currentFullDataInputNamesW1017 : List String :=
  currentFullDataInputNamesW1008

theorem currentFullDataInputNamesW1017_count :
    currentFullDataInputNamesW1017.length = 1 :=
  currentFullDataInputNamesW1008_count

structure MetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1017 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1017 :
    MetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1017
    where
  seed := "w1017-current-full-data-to-w1016-branch-full-data-route"
  declarations :=
    ["branchFullDataProviderOfCurrentFullDataW1017",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1017",
      "targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1017",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1017",
      "localizedUnitChoiceDataOfCurrentFullDataW1017",
      "componentFieldsOfCurrentFullDataW1017",
      "currentFullDataOfCurrentFullDataW1017",
      "currentFullDataProviderOfCurrentFullDataW1017",
      "branchFullDataOfCurrentFullDataW1017",
      "targetSurjectiveCompactDataOfCurrentFullDataW1017",
      "fullDataOfCurrentFullDataW1017",
      "directBoundedLeftCalculusOfCurrentFullDataW1017",
      "boundedDerivedInfinityCategoryOfCurrentFullDataW1017",
      "currentFullDataInputNamesW1017_count"]
  providerRepackagingResult :=
    "proved: W1017 constructs the W1007 branch-full-data provider surface\
      from W1008 current full data and feeds W1016"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1017 inherits W1016/W1015/W1014/W1013/W1012/W1011/W1010/\
      W1009/W1008/W1007/W1006/W1005/W1004/W1003/W1002/W998 target\
      surjective-compact recovery after W1008 constructs W1007"
  exactAtResult :=
    "proved: the W1017 W1008 current-full-data provider surface feeds\
      W1016/W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/\
      W1006/W1005/W1004/W1003/W1002/W998/W997/W996/W995/W994/W993/\
      W988/W987/W986/W985/W984/W983/W982/W981/W980/W979/W978/W977/\
      W976/W975/W974/W973/W972/W971/W970/W969/W968/W967/W966/W965/\
      W964/W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/W952\
      stable ExactAt route"
  remainingInputs := currentFullDataInputNamesW1017
  productSuccessClaimed := false

theorem currentW1017CurrentFullDataDirectRoute_productSuccess :
    (let state :=
        currentMetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1017;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
