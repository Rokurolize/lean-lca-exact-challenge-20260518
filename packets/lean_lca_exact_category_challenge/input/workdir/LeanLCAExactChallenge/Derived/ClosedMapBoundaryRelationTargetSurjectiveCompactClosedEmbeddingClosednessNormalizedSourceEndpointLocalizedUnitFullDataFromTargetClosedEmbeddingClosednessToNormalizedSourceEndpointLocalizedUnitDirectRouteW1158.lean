import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromNormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRouteW1157
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromTargetClosedEmbeddingClosednessDirectRoute

/-!
W1158 replaces W1157's W1013 normalized-source/endpoint-localized-unit input
surface by the existing W1014 target/closed-embedding-closedness input surface.
W1014 already constructs W1004, and W1158 feeds that provider into W1157.
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

/-- W1158 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1005 data. -/
def normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1014
    targetClosedEmbeddingClosednessData

/-- W1158 constructs the W1003 endpoint-localized-unit surface from W1005 through W1157. -/
def endpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
      targetClosedEmbeddingClosednessData)

/-- W1158 constructs the W982 localized-unit-choice surface from W1005 through W1157. -/
def localizedUnitChoiceDataOfTargetClosedEmbeddingClosednessW1158
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
      targetClosedEmbeddingClosednessData)

/-- W1158 constructs the W981 provider surface from W1005 through W1157. -/
noncomputable def unitStrictExactIsoDataOfTargetClosedEmbeddingClosednessW1158
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
      targetClosedEmbeddingClosednessData)

/-- W1158 constructs the W971 component-field surface from W1005 through W1157. -/
noncomputable def componentFieldsOfTargetClosedEmbeddingClosednessW1158
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
      targetClosedEmbeddingClosednessData)

/-- W1158 constructs the W1008 current-full-data surface from W1005 through W1157. -/
noncomputable def currentFullDataProviderOfTargetClosedEmbeddingClosednessW1158
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
      targetClosedEmbeddingClosednessData)

/-- W1158 constructs the W1007 branch-full-data surface from W1005 through W1157. -/
noncomputable def branchFullDataProviderOfTargetClosedEmbeddingClosednessW1158
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
      targetClosedEmbeddingClosednessData)

/-- W1158 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1005 through W1157. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessW1158
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
      targetClosedEmbeddingClosednessData)

/-- W1158 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1157. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessW1158
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
      targetClosedEmbeddingClosednessData)

/-- W1158 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1157. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1158
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
      targetClosedEmbeddingClosednessData)

/-- W1158 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1157. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1158
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
      targetClosedEmbeddingClosednessData)

/-- W1158 exposes the rebuilt W982 localized-unit-choice surface after routing through W1157. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessW1158
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
      targetClosedEmbeddingClosednessData)

/-- W1158 exposes the rebuilt W981 surface after routing through W1157. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfTargetClosedEmbeddingClosednessW1158
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
      targetClosedEmbeddingClosednessData)

/-- W1158 exposes the rebuilt W971 component fields after routing through W1157. -/
noncomputable def componentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessW1158
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
      targetClosedEmbeddingClosednessData)

/-- W1158 exposes the rebuilt W1008 current-full-data surface after routing through W1157. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfTargetClosedEmbeddingClosednessW1158
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
      targetClosedEmbeddingClosednessData)

/-- W1158 exposes the rebuilt W1007 branch-full-data surface after routing through W1157. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfTargetClosedEmbeddingClosednessW1158
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
      targetClosedEmbeddingClosednessData)

/-- W1158 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1157. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfTargetClosedEmbeddingClosednessW1158
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
      targetClosedEmbeddingClosednessData)

/-- W1158 returns the nested rebuilt W1005 target/closed-embedding-closedness surface through W1157. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfTargetClosedEmbeddingClosednessW1158
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
      targetClosedEmbeddingClosednessData)

/-- W1158 exposes the twice-rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1157. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1158
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
      targetClosedEmbeddingClosednessData)

/-- W1158 exposes the nested rebuilt W1003 endpoint-localized-unit surface through W1157. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1158
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
      targetClosedEmbeddingClosednessData)

/-- W1158 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1157. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessW1158
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
      targetClosedEmbeddingClosednessData)

/-- W1158 exposes the twice-rebuilt W981 surface after routing through W1157. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfTargetClosedEmbeddingClosednessW1158
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
      targetClosedEmbeddingClosednessData)

/-- W1158 exposes the twice-rebuilt W971 component fields after routing through W1157. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessW1158
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
      targetClosedEmbeddingClosednessData)

/-- W1158 exposes the rebuilt W1008 current-full-data surface after the nested W1157 pass. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfTargetClosedEmbeddingClosednessW1158
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
      targetClosedEmbeddingClosednessData)

/-- W1158 exposes the rebuilt W1007 branch-full-data surface after the nested W1157 pass. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfTargetClosedEmbeddingClosednessW1158
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
      targetClosedEmbeddingClosednessData)

/-- W1158 exposes the triply rebuilt W982 localized-unit-choice surface after routing through W1157. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessW1158
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
      targetClosedEmbeddingClosednessData)

/-- W1158 exposes the triply rebuilt W971 component fields after routing through W1157. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessW1158
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
      targetClosedEmbeddingClosednessData)

/-- W1158 constructs W977 current full data from W1005 through W1157. -/
noncomputable def currentFullDataOfTargetClosedEmbeddingClosednessW1158
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
      targetClosedEmbeddingClosednessData)

/-- W1158 constructs W987 branch full data from W1005 through W1157. -/
noncomputable def branchFullDataOfTargetClosedEmbeddingClosednessW1158
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
      targetClosedEmbeddingClosednessData)

/-- W1158 recovers W715 target surjective-compact data from W1005 through W1157. -/
noncomputable def targetSurjectiveCompactDataOfTargetClosedEmbeddingClosednessW1158
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
      targetClosedEmbeddingClosednessData)

/-- W1158 returns the constructed W987 branch full data from W1005 through W1157. -/
noncomputable def fullDataOfTargetClosedEmbeddingClosednessW1158
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
      targetClosedEmbeddingClosednessData)

theorem directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessW1158
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
      targetClosedEmbeddingClosednessData)

noncomputable def boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessW1158
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158
      targetClosedEmbeddingClosednessData)

def targetClosedEmbeddingClosednessInputNamesW1158 : List String :=
  targetClosedEmbeddingClosednessInputNamesW1014

theorem targetClosedEmbeddingClosednessInputNamesW1158_count :
    targetClosedEmbeddingClosednessInputNamesW1158.length = 3 :=
  targetClosedEmbeddingClosednessInputNamesW1014_count

structure MetrizableTargetClosedEmbeddingClosednessToNormalizedSourceEndpointLocalizedUnitDirectRouteStateW1158 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetClosedEmbeddingClosednessToNormalizedSourceEndpointLocalizedUnitDirectRouteStateW1158 :
    MetrizableTargetClosedEmbeddingClosednessToNormalizedSourceEndpointLocalizedUnitDirectRouteStateW1158
    where
  seed := "w1158-target-closed-embedding-closedness-to-w1157-normalized-source-endpoint-route"
  declarations :=
    ["normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158",
      "endpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1158",
      "localizedUnitChoiceDataOfTargetClosedEmbeddingClosednessW1158",
      "unitStrictExactIsoDataOfTargetClosedEmbeddingClosednessW1158",
      "componentFieldsOfTargetClosedEmbeddingClosednessW1158",
      "currentFullDataProviderOfTargetClosedEmbeddingClosednessW1158",
      "branchFullDataProviderOfTargetClosedEmbeddingClosednessW1158",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessW1158",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessW1158",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1158",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1158",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessW1158",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfTargetClosedEmbeddingClosednessW1158",
      "componentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessW1158",
      "currentFullDataProviderOfCurrentFullDataOfTargetClosedEmbeddingClosednessW1158",
      "branchFullDataProviderOfBranchFullDataOfTargetClosedEmbeddingClosednessW1158",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfTargetClosedEmbeddingClosednessW1158",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfTargetClosedEmbeddingClosednessW1158",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1158",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1158",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessW1158",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfTargetClosedEmbeddingClosednessW1158",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessW1158",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfTargetClosedEmbeddingClosednessW1158",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfTargetClosedEmbeddingClosednessW1158",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessW1158",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessW1158",
      "currentFullDataOfTargetClosedEmbeddingClosednessW1158",
      "branchFullDataOfTargetClosedEmbeddingClosednessW1158",
      "targetSurjectiveCompactDataOfTargetClosedEmbeddingClosednessW1158",
      "fullDataOfTargetClosedEmbeddingClosednessW1158",
      "directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessW1158",
      "boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessW1158",
      "targetClosedEmbeddingClosednessInputNamesW1158_count"]
  providerRepackagingResult :=
    "proved: W1158 constructs the W1157 W1013 normalized-source/endpoint\
      localized-unit input surface from W1014 target/closed-embedding\
      closedness data and feeds W1157"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1158 inherits W1157/W1111/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/W1098/W1097/\
      W1096/W1095/W1094/W1093/W1092/W1091/W1090/W1089/W1088/W1087/\
      W1086/W1085/W1084/W1083/W1082/W1081/W1080/W1079/W1078/W1077/\
      W1076/W1075/W1074/W1073/W1072/W1071/W1070/W1069/W1068/W1067/\
      W1066/W1065/W1064/W1063/W1062/W1061/W1060/W1059/W1058/W1057/\
      W1056/W1055/W1054/W1053/W1052/W1051/W1050/W1049/W1048/W1047/\
      W1046/W1045/W1044/W1043/W1042/W1041/W1040/W1039/W1038/W1037/\
      W1036/W1035/W1034/W1033/W1032/W1031/W1030/W1029/W1028/W1027/\
      W1026/W1025/W1024/W1023/W1022/W1021/W1020/W1019/W1018/W1017/\
      W1016/W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/\
      W1006/W1005/W1004/W1003/W1002/W998 target surjective-compact\
      recovery after W1014 constructs W1004"
  exactAtResult :=
    "proved: the W1158 W1014 target/closed-embedding-closedness input\
      surface feeds W1157/W1111/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/W1098/W1097/W1096/\
      W1095/W1094/W1093/W1092/W1091/W1090/W1089/W1088/W1087/W1086/\
      W1085/W1084/W1083/W1082/W1081/W1080/W1079/W1078/W1077/W1076/\
      W1075/W1074/W1073/W1072/W1071/W1070/W1069/W1068/W1067/W1066/\
      W1065/W1064/W1063/W1062/W1061/W1060/W1059/W1058/W1057/W1056/\
      W1055/W1054/W1053/W1052/W1051/W1050/W1049/W1048/W1047/W1046/\
      W1045/W1044/W1043/W1042/W1041/W1040/W1039/W1038/W1037/W1036/\
      W1035/W1034/W1033/W1032/W1031/W1030/W1029/W1028/W1027/W1026/\
      W1025/W1024/W1023/W1022/W1021/W1020/W1019/W1018/W1017/W1016/\
      W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/\
      W1005/W1004/W1003/W1002/W998/W997/W996/W995/W994/W993/W988/\
      W987/W986/W985/W984/W983/W982/W981/W980/W979/W978/W977/W976/\
      W975/W974/W973/W972/W971/W970/W969/W968/W967/W966/W965/W964/\
      W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/W952 stable\
      ExactAt route"
  remainingInputs := targetClosedEmbeddingClosednessInputNamesW1158
  productSuccessClaimed := false

theorem currentW1158TargetClosedEmbeddingClosednessToNormalizedSourceEndpointLocalizedUnitDirectRoute_productSuccess :
    (let state :=
        currentMetrizableTargetClosedEmbeddingClosednessToNormalizedSourceEndpointLocalizedUnitDirectRouteStateW1158;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
