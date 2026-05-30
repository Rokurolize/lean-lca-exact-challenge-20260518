import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromTargetClosedEmbeddingClosednessNormalizedSourceEndpointDirectRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromBranchFullDataDirectRoute

/-!
W1016 replaces W1015's W1006 target/closed-embedding-closedness/
normalized-source/endpoint surface by the existing W1007 branch-full-data
surface. W1007 already constructs W1006, and W1016 feeds that provider into
W1015.
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

/-- W1016 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1007 data. -/
def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1016
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1007
    branchFullData

/-- W1016 constructs the W1005 target/closed-embedding-closedness surface from W1007 through W1015. -/
def targetClosedEmbeddingClosednessDataProviderOfBranchFullDataW1016
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1015
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1016
      branchFullData)

/-- W1016 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1007 through W1015. -/
def normalizedSourceEndpointLocalizedUnitDataProviderOfBranchFullDataW1016
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1015
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1016
      branchFullData)

/-- W1016 constructs the W982 localized-unit-choice surface from W1007 through W1015. -/
def localizedUnitChoiceDataOfBranchFullDataW1016
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1015
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1016
      branchFullData)

/-- W1016 constructs the W971 component-field surface from W1007 through W1015. -/
noncomputable def componentFieldsOfBranchFullDataW1016
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1015
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1016
      branchFullData)

/-- W1016 constructs W977 current full data from W1007 through W1015. -/
noncomputable def currentFullDataOfBranchFullDataW1016
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1015
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1016
      branchFullData)

/-- W1016 builds the W1008 provider surface through W1015. -/
noncomputable def currentFullDataProviderOfBranchFullDataW1016
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1015
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1016
      branchFullData)

/-- W1016 constructs W987 branch full data through W1015. -/
noncomputable def branchFullDataOfBranchFullDataW1016
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1015
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1016
      branchFullData)

/-- W1016 recovers W715 target surjective-compact data through W1015. -/
noncomputable def targetSurjectiveCompactDataOfBranchFullDataW1016
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1015
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1016
      branchFullData)

/-- W1016 returns the constructed W987 branch full data through W1015. -/
noncomputable def fullDataOfBranchFullDataW1016
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1015
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1016
      branchFullData)

theorem directBoundedLeftCalculusOfBranchFullDataW1016
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1015
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1016
      branchFullData)

noncomputable def boundedDerivedInfinityCategoryOfBranchFullDataW1016
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1015
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1016
      branchFullData)

def branchFullDataInputNamesW1016 : List String :=
  branchFullDataInputNamesW1007

theorem branchFullDataInputNamesW1016_count :
    branchFullDataInputNamesW1016.length = 1 :=
  branchFullDataInputNamesW1007_count

structure MetrizableBranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointDirectRouteStateW1016 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableBranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointDirectRouteStateW1016 :
    MetrizableBranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointDirectRouteStateW1016
    where
  seed := "w1016-branch-full-data-to-w1015-target-closed-embedding-normalized-source-endpoint-route"
  declarations :=
    ["targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1016",
      "targetClosedEmbeddingClosednessDataProviderOfBranchFullDataW1016",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfBranchFullDataW1016",
      "localizedUnitChoiceDataOfBranchFullDataW1016",
      "componentFieldsOfBranchFullDataW1016",
      "currentFullDataOfBranchFullDataW1016",
      "currentFullDataProviderOfBranchFullDataW1016",
      "branchFullDataOfBranchFullDataW1016",
      "targetSurjectiveCompactDataOfBranchFullDataW1016",
      "fullDataOfBranchFullDataW1016",
      "directBoundedLeftCalculusOfBranchFullDataW1016",
      "boundedDerivedInfinityCategoryOfBranchFullDataW1016",
      "branchFullDataInputNamesW1016_count"]
  providerRepackagingResult :=
    "proved: W1016 constructs the W1006 target/closedness/normalized-source/\
      endpoint provider surface from one W1007 branch-full-data provider and\
      feeds W1015"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1016 inherits W1015/W1014/W1013/W1012/W1011/W1010/W1009/\
      W1008/W1007/W1006/W1005/W1004/W1003/W1002/W998 target\
      surjective-compact recovery after W1007 constructs W1006"
  exactAtResult :=
    "proved: the W1016 W1007 branch-full-data provider surface feeds\
      W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/\
      W1005/W1004/W1003/W1002/W998/W997/W996/W995/W994/W993/W988/\
      W987/W986/W985/W984/W983/W982/W981/W980/W979/W978/W977/W976/\
      W975/W974/W973/W972/W971/W970/W969/W968/W967/W966/W965/W964/\
      W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/W952 stable\
      ExactAt route"
  remainingInputs := branchFullDataInputNamesW1016
  productSuccessClaimed := false

theorem currentW1016BranchFullDataDirectRoute_productSuccess :
    (let state :=
        currentMetrizableBranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointDirectRouteStateW1016;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
