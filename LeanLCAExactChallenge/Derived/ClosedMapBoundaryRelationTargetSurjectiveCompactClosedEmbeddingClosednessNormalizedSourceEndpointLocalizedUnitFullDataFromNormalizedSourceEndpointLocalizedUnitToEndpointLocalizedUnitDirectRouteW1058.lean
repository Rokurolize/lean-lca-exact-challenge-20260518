import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromEndpointLocalizedUnitToLocalizedUnitChoiceDirectRouteW1057
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromNormalizedSourceEndpointLocalizedUnitRoute

/-!
W1058 replaces W1057's W1012 endpoint-localized-unit input surface by the
existing W1013 normalized-source/endpoint-localized-unit input surface. W1013 already
constructs the W1003 endpoint-localized-unit provider accepted by W1057.
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

/-- W1058 constructs the W1003 endpoint-localized-unit surface through W1013 data. -/
def endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
    normalizedSourceEndpointLocalizedUnitData

/-- W1058 constructs the W982 localized-unit-choice surface from W1004 through W1057. -/
def localizedUnitChoiceDataOfNormalizedSourceEndpointLocalizedUnitW1058
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfEndpointLocalizedUnitW1057
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
      normalizedSourceEndpointLocalizedUnitData)

/-- W1058 constructs the W981 provider surface from W1004 through W1057. -/
noncomputable def unitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1058
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfEndpointLocalizedUnitW1057
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
      normalizedSourceEndpointLocalizedUnitData)

/-- W1058 constructs the W971 component-field surface from W1004 through W1057. -/
noncomputable def componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1058
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfEndpointLocalizedUnitW1057
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
      normalizedSourceEndpointLocalizedUnitData)

/-- W1058 constructs the W1008 current-full-data surface from W1004 through W1057. -/
noncomputable def currentFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfEndpointLocalizedUnitW1057
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
      normalizedSourceEndpointLocalizedUnitData)

/-- W1058 constructs the W1007 branch-full-data surface from W1004 through W1057. -/
noncomputable def branchFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfEndpointLocalizedUnitW1057
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
      normalizedSourceEndpointLocalizedUnitData)

/-- W1058 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1004 through W1057. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfEndpointLocalizedUnitW1057
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
      normalizedSourceEndpointLocalizedUnitData)

/-- W1058 constructs the W1005 target/closed-embedding-closedness surface from W1004 through W1057. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfEndpointLocalizedUnitW1057
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
      normalizedSourceEndpointLocalizedUnitData)

/-- W1058 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1057. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1057
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
      normalizedSourceEndpointLocalizedUnitData)

/-- W1058 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1057. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1058
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1057
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
      normalizedSourceEndpointLocalizedUnitData)

/-- W1058 exposes the rebuilt W982 localized-unit-choice surface after routing through W1057. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1058
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1057
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
      normalizedSourceEndpointLocalizedUnitData)

/-- W1058 exposes the rebuilt W981 surface after routing through W1057. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1058
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfEndpointLocalizedUnitW1057
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
      normalizedSourceEndpointLocalizedUnitData)

/-- W1058 exposes the rebuilt W971 component fields after routing through W1057. -/
noncomputable def componentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1058
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1057
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
      normalizedSourceEndpointLocalizedUnitData)

/-- W1058 exposes the rebuilt W1008 current-full-data surface after routing through W1057. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfNormalizedSourceEndpointLocalizedUnitW1058
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfEndpointLocalizedUnitW1057
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
      normalizedSourceEndpointLocalizedUnitData)

/-- W1058 exposes the rebuilt W1007 branch-full-data surface after routing through W1057. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1058
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfEndpointLocalizedUnitW1057
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
      normalizedSourceEndpointLocalizedUnitData)

/-- W1058 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1057. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfNormalizedSourceEndpointLocalizedUnitW1058
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfEndpointLocalizedUnitW1057
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
      normalizedSourceEndpointLocalizedUnitData)

/-- W1058 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1057. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfNormalizedSourceEndpointLocalizedUnitW1058
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfEndpointLocalizedUnitW1057
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
      normalizedSourceEndpointLocalizedUnitData)

/-- W1058 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1057. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1058
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfEndpointLocalizedUnitW1057
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
      normalizedSourceEndpointLocalizedUnitData)

/-- W1058 exposes the rebuilt W1003 endpoint-localized-unit surface after the nested W1057 pass. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1058
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitW1057
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
      normalizedSourceEndpointLocalizedUnitData)

/-- W1058 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1057. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1058
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1057
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
      normalizedSourceEndpointLocalizedUnitData)

/-- W1058 exposes the twice-rebuilt W981 surface after routing through W1057. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1058
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfEndpointLocalizedUnitW1057
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
      normalizedSourceEndpointLocalizedUnitData)

/-- W1058 exposes the twice-rebuilt W971 component fields after routing through W1057. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1058
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1057
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
      normalizedSourceEndpointLocalizedUnitData)

/-- W1058 exposes the rebuilt W1008 current-full-data surface after the nested W1057 pass. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfNormalizedSourceEndpointLocalizedUnitW1058
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfEndpointLocalizedUnitW1057
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
      normalizedSourceEndpointLocalizedUnitData)

/-- W1058 exposes the rebuilt W1007 branch-full-data surface after the nested W1057 pass. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1058
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataOfEndpointLocalizedUnitW1057
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
      normalizedSourceEndpointLocalizedUnitData)

/-- W1058 exposes the triply rebuilt W982 localized-unit-choice surface after routing through W1057. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1058
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1057
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
      normalizedSourceEndpointLocalizedUnitData)

/-- W1058 exposes the triply rebuilt W971 component fields after routing through W1057. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1058
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1057
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
      normalizedSourceEndpointLocalizedUnitData)

/-- W1058 constructs W977 current full data from W1004 through W1057. -/
noncomputable def currentFullDataOfNormalizedSourceEndpointLocalizedUnitW1058
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfEndpointLocalizedUnitW1057
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
      normalizedSourceEndpointLocalizedUnitData)

/-- W1058 constructs W987 branch full data from W1004 through W1057. -/
noncomputable def branchFullDataOfNormalizedSourceEndpointLocalizedUnitW1058
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfEndpointLocalizedUnitW1057
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
      normalizedSourceEndpointLocalizedUnitData)

/-- W1058 recovers W715 target surjective-compact data from W1004 through W1057. -/
noncomputable def targetSurjectiveCompactDataOfNormalizedSourceEndpointLocalizedUnitW1058
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfEndpointLocalizedUnitW1057
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
      normalizedSourceEndpointLocalizedUnitData)

/-- W1058 returns the constructed W987 branch full data from W1004 through W1057. -/
noncomputable def fullDataOfNormalizedSourceEndpointLocalizedUnitW1058
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfEndpointLocalizedUnitW1057
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
      normalizedSourceEndpointLocalizedUnitData)

theorem directBoundedLeftCalculusOfNormalizedSourceEndpointLocalizedUnitW1058
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfEndpointLocalizedUnitW1057
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
      normalizedSourceEndpointLocalizedUnitData)

noncomputable def boundedDerivedInfinityCategoryOfNormalizedSourceEndpointLocalizedUnitW1058
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfEndpointLocalizedUnitW1057
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058
      normalizedSourceEndpointLocalizedUnitData)

def normalizedSourceEndpointLocalizedUnitInputNamesW1058 : List String :=
  normalizedSourceEndpointLocalizedUnitInputNamesW1013

theorem normalizedSourceEndpointLocalizedUnitInputNamesW1058_count :
    normalizedSourceEndpointLocalizedUnitInputNamesW1058.length = 4 :=
  normalizedSourceEndpointLocalizedUnitInputNamesW1013_count

structure MetrizableNormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRouteStateW1058 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableNormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRouteStateW1058 :
    MetrizableNormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRouteStateW1058
    where
  seed := "w1058-normalized-source-endpoint-localized-unit-to-w1057-endpoint-localized-unit-route"
  declarations :=
    ["endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058",
      "localizedUnitChoiceDataOfNormalizedSourceEndpointLocalizedUnitW1058",
      "unitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1058",
      "componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1058",
      "currentFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058",
      "branchFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058",
      "targetClosedEmbeddingClosednessDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1058",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1058",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1058",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1058",
      "componentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1058",
      "currentFullDataProviderOfCurrentFullDataOfNormalizedSourceEndpointLocalizedUnitW1058",
      "branchFullDataProviderOfBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1058",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfNormalizedSourceEndpointLocalizedUnitW1058",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfNormalizedSourceEndpointLocalizedUnitW1058",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1058",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1058",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1058",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1058",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1058",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfNormalizedSourceEndpointLocalizedUnitW1058",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1058",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1058",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1058",
      "currentFullDataOfNormalizedSourceEndpointLocalizedUnitW1058",
      "branchFullDataOfNormalizedSourceEndpointLocalizedUnitW1058",
      "targetSurjectiveCompactDataOfNormalizedSourceEndpointLocalizedUnitW1058",
      "fullDataOfNormalizedSourceEndpointLocalizedUnitW1058",
      "directBoundedLeftCalculusOfNormalizedSourceEndpointLocalizedUnitW1058",
      "boundedDerivedInfinityCategoryOfNormalizedSourceEndpointLocalizedUnitW1058",
      "normalizedSourceEndpointLocalizedUnitInputNamesW1058_count"]
  providerRepackagingResult :=
    "proved: W1058 constructs the W1057 W1012 endpoint-localized-unit\
      input surface from W1013 normalized-source/endpoint-localized-unit data\
      and feeds W1057"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1058 inherits W1057/W1056/W1055/W1054/W1053/W1052/\
      W1051/W1050/W1049/W1048/W1047/W1046/W1045/W1044/W1043/W1042/\
      W1041/W1040/W1039/W1038/W1037/W1036/W1035/W1034/W1033/W1032/\
      W1031/W1030/W1029/W1028/W1027/W1026/W1025/W1024/W1023/W1022/\
      W1021/W1020/W1019/W1018/W1017/W1016/W1015/W1014/W1013/W1012/\
      W1011/W1010/W1009/W1008/W1007/W1006/W1005/W1004/W1003/W1002/\
      W998 target surjective-compact recovery after W1013 constructs the endpoint-localized-unit provider"
  exactAtResult :=
    "proved: the W1058 W1013 normalized-source/endpoint-localized-unit\
      input surface feeds W1057/W1056/W1055/W1054/W1053/W1052/W1051/\
      W1050/W1049/W1048/W1047/W1046/W1045/W1044/W1043/W1042/W1041/\
      W1040/W1039/W1038/W1037/W1036/W1035/W1034/W1033/W1032/W1031/\
      W1030/W1029/W1028/W1027/W1026/W1025/W1024/W1023/W1022/W1021/\
      W1020/W1019/W1018/W1017/W1016/W1015/W1014/W1013/W1012/W1011/\
      W1010/W1009/W1008/W1007/W1006/W1005/W1004/W1003/W1002/W998/\
      W997/W996/W995/W994/W993/W988/W987/W986/W985/W984/W983/W982/\
      W981/W980/W979/W978/W977/W976/W975/W974/W973/W972/W971/W970/\
      W969/W968/W967/W966/W965/W964/W963/W962/W961/W959/W958/W957/\
      W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := normalizedSourceEndpointLocalizedUnitInputNamesW1058
  productSuccessClaimed := false

theorem currentW1058NormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRoute_productSuccess :
    (let state :=
        currentMetrizableNormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRouteStateW1058;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
