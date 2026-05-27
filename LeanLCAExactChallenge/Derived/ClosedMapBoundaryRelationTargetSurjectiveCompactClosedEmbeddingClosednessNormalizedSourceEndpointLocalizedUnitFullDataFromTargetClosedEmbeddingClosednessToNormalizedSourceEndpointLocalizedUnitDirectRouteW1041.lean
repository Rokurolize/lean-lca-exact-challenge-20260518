import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromNormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRouteW1040
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromTargetClosedEmbeddingClosednessRoute

/-!
W1041 replaces W1040's W1004 normalized-source/endpoint-localized-unit provider
surface by the existing W1005 target/closed-embedding-closedness surface. W1005
already constructs W1004, and W1041 feeds that provider into W1040.
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

/-- W1041 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1005 data. -/
def normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1005
    targetClosedEmbeddingClosednessData

/-- W1041 constructs the W1003 endpoint-localized-unit surface from W1005 through W1040. -/
def endpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
      targetClosedEmbeddingClosednessData)

/-- W1041 constructs the W982 localized-unit-choice surface from W1005 through W1040. -/
def localizedUnitChoiceDataOfTargetClosedEmbeddingClosednessW1041
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
      targetClosedEmbeddingClosednessData)

/-- W1041 constructs the W981 provider surface from W1005 through W1040. -/
noncomputable def unitStrictExactIsoDataOfTargetClosedEmbeddingClosednessW1041
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
      targetClosedEmbeddingClosednessData)

/-- W1041 constructs the W971 component-field surface from W1005 through W1040. -/
noncomputable def componentFieldsOfTargetClosedEmbeddingClosednessW1041
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
      targetClosedEmbeddingClosednessData)

/-- W1041 constructs the W1008 current-full-data surface from W1005 through W1040. -/
noncomputable def currentFullDataProviderOfTargetClosedEmbeddingClosednessW1041
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
      targetClosedEmbeddingClosednessData)

/-- W1041 constructs the W1007 branch-full-data surface from W1005 through W1040. -/
noncomputable def branchFullDataProviderOfTargetClosedEmbeddingClosednessW1041
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
      targetClosedEmbeddingClosednessData)

/-- W1041 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1005 through W1040. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessW1041
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
      targetClosedEmbeddingClosednessData)

/-- W1041 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1040. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessW1041
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
      targetClosedEmbeddingClosednessData)

/-- W1041 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1040. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1041
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
      targetClosedEmbeddingClosednessData)

/-- W1041 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1040. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1041
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
      targetClosedEmbeddingClosednessData)

/-- W1041 exposes the rebuilt W982 localized-unit-choice surface after routing through W1040. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessW1041
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
      targetClosedEmbeddingClosednessData)

/-- W1041 exposes the rebuilt W981 surface after routing through W1040. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfTargetClosedEmbeddingClosednessW1041
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
      targetClosedEmbeddingClosednessData)

/-- W1041 exposes the rebuilt W971 component fields after routing through W1040. -/
noncomputable def componentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessW1041
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
      targetClosedEmbeddingClosednessData)

/-- W1041 exposes the rebuilt W1008 current-full-data surface after routing through W1040. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfTargetClosedEmbeddingClosednessW1041
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
      targetClosedEmbeddingClosednessData)

/-- W1041 exposes the rebuilt W1007 branch-full-data surface after routing through W1040. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfTargetClosedEmbeddingClosednessW1041
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
      targetClosedEmbeddingClosednessData)

/-- W1041 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1040. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfTargetClosedEmbeddingClosednessW1041
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
      targetClosedEmbeddingClosednessData)

/-- W1041 returns the nested rebuilt W1005 target/closed-embedding-closedness surface through W1040. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfTargetClosedEmbeddingClosednessW1041
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
      targetClosedEmbeddingClosednessData)

/-- W1041 exposes the twice-rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1040. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1041
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
      targetClosedEmbeddingClosednessData)

/-- W1041 exposes the nested rebuilt W1003 endpoint-localized-unit surface through W1040. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1041
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
      targetClosedEmbeddingClosednessData)

/-- W1041 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1040. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessW1041
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
      targetClosedEmbeddingClosednessData)

/-- W1041 exposes the twice-rebuilt W981 surface after routing through W1040. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfTargetClosedEmbeddingClosednessW1041
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
      targetClosedEmbeddingClosednessData)

/-- W1041 exposes the twice-rebuilt W971 component fields after routing through W1040. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessW1041
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
      targetClosedEmbeddingClosednessData)

/-- W1041 exposes the rebuilt W1008 current-full-data surface after the nested W1040 pass. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfTargetClosedEmbeddingClosednessW1041
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
      targetClosedEmbeddingClosednessData)

/-- W1041 exposes the rebuilt W1007 branch-full-data surface after the nested W1040 pass. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfTargetClosedEmbeddingClosednessW1041
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
      targetClosedEmbeddingClosednessData)

/-- W1041 exposes the triply rebuilt W982 localized-unit-choice surface after routing through W1040. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessW1041
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
      targetClosedEmbeddingClosednessData)

/-- W1041 exposes the triply rebuilt W971 component fields after routing through W1040. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessW1041
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
      targetClosedEmbeddingClosednessData)

/-- W1041 constructs W977 current full data from W1005 through W1040. -/
noncomputable def currentFullDataOfTargetClosedEmbeddingClosednessW1041
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
      targetClosedEmbeddingClosednessData)

/-- W1041 constructs W987 branch full data from W1005 through W1040. -/
noncomputable def branchFullDataOfTargetClosedEmbeddingClosednessW1041
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
      targetClosedEmbeddingClosednessData)

/-- W1041 recovers W715 target surjective-compact data from W1005 through W1040. -/
noncomputable def targetSurjectiveCompactDataOfTargetClosedEmbeddingClosednessW1041
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
      targetClosedEmbeddingClosednessData)

/-- W1041 returns the constructed W987 branch full data from W1005 through W1040. -/
noncomputable def fullDataOfTargetClosedEmbeddingClosednessW1041
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
      targetClosedEmbeddingClosednessData)

theorem directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessW1041
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
      targetClosedEmbeddingClosednessData)

noncomputable def boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessW1041
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041
      targetClosedEmbeddingClosednessData)

def targetClosedEmbeddingClosednessInputNamesW1041 : List String :=
  targetClosedEmbeddingClosednessInputNamesW1005

theorem targetClosedEmbeddingClosednessInputNamesW1041_count :
    targetClosedEmbeddingClosednessInputNamesW1041.length = 3 :=
  targetClosedEmbeddingClosednessInputNamesW1005_count

structure MetrizableTargetClosedEmbeddingClosednessToNormalizedSourceEndpointLocalizedUnitDirectRouteStateW1041 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetClosedEmbeddingClosednessToNormalizedSourceEndpointLocalizedUnitDirectRouteStateW1041 :
    MetrizableTargetClosedEmbeddingClosednessToNormalizedSourceEndpointLocalizedUnitDirectRouteStateW1041
    where
  seed := "w1041-target-closed-embedding-closedness-to-w1040-normalized-source-endpoint-route"
  declarations :=
    ["normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041",
      "endpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1041",
      "localizedUnitChoiceDataOfTargetClosedEmbeddingClosednessW1041",
      "unitStrictExactIsoDataOfTargetClosedEmbeddingClosednessW1041",
      "componentFieldsOfTargetClosedEmbeddingClosednessW1041",
      "currentFullDataProviderOfTargetClosedEmbeddingClosednessW1041",
      "branchFullDataProviderOfTargetClosedEmbeddingClosednessW1041",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessW1041",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessW1041",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1041",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1041",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessW1041",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfTargetClosedEmbeddingClosednessW1041",
      "componentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessW1041",
      "currentFullDataProviderOfCurrentFullDataOfTargetClosedEmbeddingClosednessW1041",
      "branchFullDataProviderOfBranchFullDataOfTargetClosedEmbeddingClosednessW1041",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfTargetClosedEmbeddingClosednessW1041",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfTargetClosedEmbeddingClosednessW1041",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1041",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1041",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessW1041",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfTargetClosedEmbeddingClosednessW1041",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessW1041",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfTargetClosedEmbeddingClosednessW1041",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfTargetClosedEmbeddingClosednessW1041",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessW1041",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessW1041",
      "currentFullDataOfTargetClosedEmbeddingClosednessW1041",
      "branchFullDataOfTargetClosedEmbeddingClosednessW1041",
      "targetSurjectiveCompactDataOfTargetClosedEmbeddingClosednessW1041",
      "fullDataOfTargetClosedEmbeddingClosednessW1041",
      "directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessW1041",
      "boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessW1041",
      "targetClosedEmbeddingClosednessInputNamesW1041_count"]
  providerRepackagingResult :=
    "proved: W1041 constructs the W1040 W1004 normalized-source/endpoint\
      localized-unit provider surface from W1005 target/closed-embedding\
      closedness data and feeds W1040"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1041 inherits W1040/W1039/W1038/W1037/W1036/W1035/W1034/\
      W1033/W1032/W1031/W1030/W1029/W1028/W1027/W1026/W1025/W1024/\
      W1023/W1022/W1021/W1020/W1019/W1018/W1017/W1016/W1015/W1014/\
      W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/W1004/\
      W1003/W1002/W998 target surjective-compact recovery after W1005 constructs W1004"
  exactAtResult :=
    "proved: the W1041 W1005 target/closed-embedding-closedness provider\
      surface feeds W1040/W1039/W1038/W1037/W1036/W1035/W1034/W1033/\
      W1032/W1031/W1030/W1029/W1028/W1027/W1026/W1025/W1024/W1023/\
      W1022/W1021/W1020/W1019/W1018/W1017/W1016/W1015/W1014/W1013/\
      W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/W1004/W1003/\
      W1002/W998/W997/W996/W995/W994/W993/W988/W987/W986/W985/W984/\
      W983/W982/W981/W980/W979/W978/W977/W976/W975/W974/W973/W972/\
      W971/W970/W969/W968/W967/W966/W965/W964/W963/W962/W961/W959/\
      W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := targetClosedEmbeddingClosednessInputNamesW1041
  productSuccessClaimed := false

theorem currentW1041TargetClosedEmbeddingClosednessToNormalizedSourceEndpointLocalizedUnitDirectRoute_productSuccess :
    (let state :=
        currentMetrizableTargetClosedEmbeddingClosednessToNormalizedSourceEndpointLocalizedUnitDirectRouteStateW1041;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
