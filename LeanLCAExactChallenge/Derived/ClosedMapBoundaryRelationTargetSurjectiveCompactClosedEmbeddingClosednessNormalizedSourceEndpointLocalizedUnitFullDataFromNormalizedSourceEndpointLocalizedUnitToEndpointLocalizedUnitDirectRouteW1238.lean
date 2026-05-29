import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromEndpointLocalizedUnitToLocalizedUnitChoiceDirectRouteW1237
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromNormalizedSourceEndpointLocalizedUnitRoute

/-!
W1238 replaces W1237's W1003 endpoint-localized-unit input surface by the
existing W1013 normalized-source/endpoint-localized-unit input surface. W1013 already
constructs the W1003 endpoint-localized-unit provider accepted by W1237.
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

/-- W1238 constructs the W1003 endpoint-localized-unit surface through W1013 data. -/
def endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
    normalizedSourceEndpointLocalizedUnitData

/-- W1238 constructs the W982 localized-unit-choice surface from W1004 through W1237. -/
def localizedUnitChoiceDataOfNormalizedSourceEndpointLocalizedUnitW1238
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfEndpointLocalizedUnitW1237
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
      normalizedSourceEndpointLocalizedUnitData)

/-- W1238 constructs the W981 provider surface from W1004 through W1237. -/
noncomputable def unitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1238
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfEndpointLocalizedUnitW1237
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
      normalizedSourceEndpointLocalizedUnitData)

/-- W1238 constructs the W971 component-field surface from W1004 through W1237. -/
noncomputable def componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1238
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfEndpointLocalizedUnitW1237
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
      normalizedSourceEndpointLocalizedUnitData)

/-- W1238 constructs the W1008 current-full-data surface from W1004 through W1237. -/
noncomputable def currentFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfEndpointLocalizedUnitW1237
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
      normalizedSourceEndpointLocalizedUnitData)

/-- W1238 constructs the W1007 branch-full-data surface from W1004 through W1237. -/
noncomputable def branchFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfEndpointLocalizedUnitW1237
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
      normalizedSourceEndpointLocalizedUnitData)

/-- W1238 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1004 through W1237. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfEndpointLocalizedUnitW1237
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
      normalizedSourceEndpointLocalizedUnitData)

/-- W1238 constructs the W1005 target/closed-embedding-closedness surface from W1004 through W1237. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfEndpointLocalizedUnitW1237
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
      normalizedSourceEndpointLocalizedUnitData)

/-- W1238 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1237. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1237
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
      normalizedSourceEndpointLocalizedUnitData)

/-- W1238 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1237. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1238
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1237
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
      normalizedSourceEndpointLocalizedUnitData)

/-- W1238 exposes the rebuilt W982 localized-unit-choice surface after routing through W1237. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1238
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1237
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
      normalizedSourceEndpointLocalizedUnitData)

/-- W1238 exposes the rebuilt W981 surface after routing through W1237. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1238
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfEndpointLocalizedUnitW1237
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
      normalizedSourceEndpointLocalizedUnitData)

/-- W1238 exposes the rebuilt W971 component fields after routing through W1237. -/
noncomputable def componentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1238
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1237
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
      normalizedSourceEndpointLocalizedUnitData)

/-- W1238 exposes the rebuilt W1008 current-full-data surface after routing through W1237. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfNormalizedSourceEndpointLocalizedUnitW1238
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfEndpointLocalizedUnitW1237
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
      normalizedSourceEndpointLocalizedUnitData)

/-- W1238 exposes the rebuilt W1007 branch-full-data surface after routing through W1237. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1238
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfEndpointLocalizedUnitW1237
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
      normalizedSourceEndpointLocalizedUnitData)

/-- W1238 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1237. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfNormalizedSourceEndpointLocalizedUnitW1238
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfEndpointLocalizedUnitW1237
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
      normalizedSourceEndpointLocalizedUnitData)

/-- W1238 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1237. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfNormalizedSourceEndpointLocalizedUnitW1238
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfEndpointLocalizedUnitW1237
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
      normalizedSourceEndpointLocalizedUnitData)

/-- W1238 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1237. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1238
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfEndpointLocalizedUnitW1237
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
      normalizedSourceEndpointLocalizedUnitData)

/-- W1238 exposes the rebuilt W1003 endpoint-localized-unit surface after the nested W1237 pass. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1238
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitW1237
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
      normalizedSourceEndpointLocalizedUnitData)

/-- W1238 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1237. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1238
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1237
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
      normalizedSourceEndpointLocalizedUnitData)

/-- W1238 exposes the twice-rebuilt W981 surface after routing through W1237. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1238
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfEndpointLocalizedUnitW1237
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
      normalizedSourceEndpointLocalizedUnitData)

/-- W1238 exposes the twice-rebuilt W971 component fields after routing through W1237. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1238
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1237
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
      normalizedSourceEndpointLocalizedUnitData)

/-- W1238 exposes the rebuilt W1008 current-full-data surface after the nested W1237 pass. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfNormalizedSourceEndpointLocalizedUnitW1238
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfEndpointLocalizedUnitW1237
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
      normalizedSourceEndpointLocalizedUnitData)

/-- W1238 exposes the rebuilt W1007 branch-full-data surface after the nested W1237 pass. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1238
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataOfEndpointLocalizedUnitW1237
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
      normalizedSourceEndpointLocalizedUnitData)

/-- W1238 exposes the triply rebuilt W982 localized-unit-choice surface after routing through W1237. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1238
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1237
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
      normalizedSourceEndpointLocalizedUnitData)

/-- W1238 exposes the triply rebuilt W971 component fields after routing through W1237. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1238
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1237
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
      normalizedSourceEndpointLocalizedUnitData)

/-- W1238 constructs W977 current full data from W1004 through W1237. -/
noncomputable def currentFullDataOfNormalizedSourceEndpointLocalizedUnitW1238
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfEndpointLocalizedUnitW1237
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
      normalizedSourceEndpointLocalizedUnitData)

/-- W1238 constructs W987 branch full data from W1004 through W1237. -/
noncomputable def branchFullDataOfNormalizedSourceEndpointLocalizedUnitW1238
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfEndpointLocalizedUnitW1237
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
      normalizedSourceEndpointLocalizedUnitData)

/-- W1238 recovers W715 target surjective-compact data from W1004 through W1237. -/
noncomputable def targetSurjectiveCompactDataOfNormalizedSourceEndpointLocalizedUnitW1238
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfEndpointLocalizedUnitW1237
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
      normalizedSourceEndpointLocalizedUnitData)

/-- W1238 returns the constructed W987 branch full data from W1004 through W1237. -/
noncomputable def fullDataOfNormalizedSourceEndpointLocalizedUnitW1238
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfEndpointLocalizedUnitW1237
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
      normalizedSourceEndpointLocalizedUnitData)

theorem directBoundedLeftCalculusOfNormalizedSourceEndpointLocalizedUnitW1238
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfEndpointLocalizedUnitW1237
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
      normalizedSourceEndpointLocalizedUnitData)

noncomputable def boundedDerivedInfinityCategoryOfNormalizedSourceEndpointLocalizedUnitW1238
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfEndpointLocalizedUnitW1237
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238
      normalizedSourceEndpointLocalizedUnitData)

def normalizedSourceEndpointLocalizedUnitInputNamesW1238 : List String :=
  normalizedSourceEndpointLocalizedUnitInputNamesW1013

theorem normalizedSourceEndpointLocalizedUnitInputNamesW1238_count :
    normalizedSourceEndpointLocalizedUnitInputNamesW1238.length = 4 :=
  normalizedSourceEndpointLocalizedUnitInputNamesW1013_count

structure MetrizableNormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRouteStateW1238 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableNormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRouteStateW1238 :
    MetrizableNormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRouteStateW1238
    where
  seed := "w1238-normalized-source-endpoint-localized-unit-to-w1237-endpoint-localized-unit-route"
  declarations :=
    ["endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238",
      "localizedUnitChoiceDataOfNormalizedSourceEndpointLocalizedUnitW1238",
      "unitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1238",
      "componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1238",
      "currentFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238",
      "branchFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238",
      "targetClosedEmbeddingClosednessDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1238",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1238",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1238",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1238",
      "componentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1238",
      "currentFullDataProviderOfCurrentFullDataOfNormalizedSourceEndpointLocalizedUnitW1238",
      "branchFullDataProviderOfBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1238",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfNormalizedSourceEndpointLocalizedUnitW1238",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfNormalizedSourceEndpointLocalizedUnitW1238",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1238",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1238",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1238",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1238",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1238",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfNormalizedSourceEndpointLocalizedUnitW1238",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1238",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1238",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1238",
      "currentFullDataOfNormalizedSourceEndpointLocalizedUnitW1238",
      "branchFullDataOfNormalizedSourceEndpointLocalizedUnitW1238",
      "targetSurjectiveCompactDataOfNormalizedSourceEndpointLocalizedUnitW1238",
      "fullDataOfNormalizedSourceEndpointLocalizedUnitW1238",
      "directBoundedLeftCalculusOfNormalizedSourceEndpointLocalizedUnitW1238",
      "boundedDerivedInfinityCategoryOfNormalizedSourceEndpointLocalizedUnitW1238",
      "normalizedSourceEndpointLocalizedUnitInputNamesW1238_count"]
  providerRepackagingResult :=
    "proved: W1238 constructs the W1237 W1012 endpoint-localized-unit\
      input surface from W1013 normalized-source/endpoint-localized-unit data\
      and feeds W1237"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1238 inherits W1237/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/W1098/W1097/W1096/\
      W1095/W1094/W1093/W1092/W1091/W1090/W1089/W1088/W1087/W1086/\
      W1085/W1084/W1083/W1082/W1081/W1080/W1079/W1078/W1077/W1076/\
      W1075/W1074/W1073/W1072/W1071/W1070/W1069/W1068/W1067/W1066/\
      W1065/W1064/W1063/W1062/W1061/W1060/W1059/W1058/W1057/W1056/\
      W1055/W1054/W1053/W1052/W1051/W1050/W1049/W1048/W1047/W1046/\
      W1045/W1044/W1043/W1042/W1041/W1040/W1039/W1038/W1037/W1036/\
      W1035/W1034/W1033/W1032/W1031/W1030/W1029/W1028/W1027/W1026/\
      W1025/W1024/W1023/W1022/W1021/W1020/W1019/W1018/W1017/W1016/\
      W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/\
      W1005/W1004/W1003/W1002/W998 target\
      surjective-compact recovery after W1013 constructs the endpoint-localized-unit provider"
  exactAtResult :=
    "proved: the W1238 W1013 normalized-source/endpoint-localized-unit\
      input surface feeds W1237/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/W1098/W1097/W1096/\
      W1095/W1094/W1093/W1092/W1091/W1090/W1089/W1088/W1087/W1086/\
      W1085/W1084/W1083/W1082/W1081/W1080/W1079/W1078/W1077/W1076/\
      W1075/W1074/W1073/W1072/W1071/W1070/W1069/W1068/W1067/W1066/\
      W1065/W1064/W1063/W1062/W1061/W1060/W1059/W1058/W1057/W1056/\
      W1055/W1054/W1053/W1052/W1051/W1050/W1049/W1048/W1047/W1046/\
      W1045/W1044/W1043/W1042/W1041/W1040/W1039/W1038/W1037/W1036/\
      W1035/W1034/W1033/W1032/W1031/W1030/W1029/W1028/W1027/W1026/\
      W1025/W1024/W1023/W1022/W1021/W1020/W1019/W1018/W1017/W1016/\
      W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/\
      W1005/W1004/W1003/W1002/W998/W997/W996/W995/W994/\
      W993/W988/W987/W986/W985/W984/W983/W982/W981/W980/W979/W978/\
      W977/W976/W975/W974/W973/W972/W971/W970/W969/W968/W967/W966/\
      W965/W964/W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/\
      W952 stable ExactAt route"
  remainingInputs := normalizedSourceEndpointLocalizedUnitInputNamesW1238
  productSuccessClaimed := false

theorem currentW1238NormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRoute_productSuccess :
    (let state :=
        currentMetrizableNormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRouteStateW1238;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
