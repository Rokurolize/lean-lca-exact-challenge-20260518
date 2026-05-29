import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromTargetClosedEmbeddingClosednessToNormalizedSourceEndpointLocalizedUnitDirectRouteW1212
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromTargetClosedEmbeddingClosednessNormalizedSourceEndpointDirectRoute

/-!
W1213 replaces W1212's W1014 target/closed-embedding-closedness input surface
by the existing W1015 target/closed-embedding-closedness/normalized-source
endpoint input surface. W1015 already constructs W1005, and W1213 feeds that
provider into W1212.
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

/-- W1213 constructs the W1005 target/closed-embedding-closedness surface from W1006 data. -/
def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1015
    targetClosedEmbeddingClosednessNormalizedSourceEndpointData

/-- W1213 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1006 through W1212. -/
def normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1212
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1213 constructs the W1003 endpoint-localized-unit surface from W1006 through W1212. -/
def endpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  endpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1212
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1213 constructs the W982 localized-unit-choice surface from W1006 through W1212. -/
def localizedUnitChoiceDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  localizedUnitChoiceDataOfTargetClosedEmbeddingClosednessW1212
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1213 constructs the W981 provider surface from W1006 through W1212. -/
noncomputable def unitStrictExactIsoDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  unitStrictExactIsoDataOfTargetClosedEmbeddingClosednessW1212
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1213 constructs the W971 component-field surface from W1006 through W1212. -/
noncomputable def componentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  componentFieldsOfTargetClosedEmbeddingClosednessW1212
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1213 constructs the W1008 current-full-data surface from W1006 through W1212. -/
noncomputable def currentFullDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  currentFullDataProviderOfTargetClosedEmbeddingClosednessW1212
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1213 constructs the W1007 branch-full-data surface from W1006 through W1212. -/
noncomputable def branchFullDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  branchFullDataProviderOfTargetClosedEmbeddingClosednessW1212
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1213 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface through W1212. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessW1212
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1213 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1212. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessW1212
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1213 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1212. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1212
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1213 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1212. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1212
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1213 exposes the rebuilt W982 localized-unit-choice surface after routing through W1212. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessW1212
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1213 exposes the rebuilt W981 surface after routing through W1212. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfTargetClosedEmbeddingClosednessW1212
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1213 exposes the rebuilt W971 component fields after routing through W1212. -/
noncomputable def componentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  componentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessW1212
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1213 exposes the rebuilt W1008 current-full-data surface after routing through W1212. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  currentFullDataProviderOfCurrentFullDataOfTargetClosedEmbeddingClosednessW1212
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1213 exposes the rebuilt W1007 branch-full-data surface after routing through W1212. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  branchFullDataProviderOfBranchFullDataOfTargetClosedEmbeddingClosednessW1212
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1213 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1212. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfTargetClosedEmbeddingClosednessW1212
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1213 returns the nested rebuilt W1005 target/closed-embedding-closedness surface through W1212. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfTargetClosedEmbeddingClosednessOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfTargetClosedEmbeddingClosednessW1212
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1213 exposes the twice-rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1212. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1212
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1213 exposes the nested rebuilt W1003 endpoint-localized-unit surface through W1212. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1212
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1213 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1212. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessW1212
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1213 exposes the twice-rebuilt W981 surface after routing through W1212. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfTargetClosedEmbeddingClosednessW1212
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1213 exposes the twice-rebuilt W971 component fields after routing through W1212. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessW1212
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1213 exposes the rebuilt W1008 current-full-data surface after the nested W1212 pass. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfTargetClosedEmbeddingClosednessW1212
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1213 exposes the rebuilt W1007 branch-full-data surface after the nested W1212 pass. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataOfTargetClosedEmbeddingClosednessW1212
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1213 exposes the triply rebuilt W982 localized-unit-choice surface after routing through W1212. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessW1212
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1213 exposes the triply rebuilt W971 component fields after routing through W1212. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessW1212
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1213 constructs W977 current full data from W1006 through W1212. -/
noncomputable def currentFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  currentFullDataOfTargetClosedEmbeddingClosednessW1212
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1213 constructs W987 branch full data from W1006 through W1212. -/
noncomputable def branchFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  branchFullDataOfTargetClosedEmbeddingClosednessW1212
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1213 recovers W715 target surjective-compact data from W1006 through W1212. -/
noncomputable def targetSurjectiveCompactDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  targetSurjectiveCompactDataOfTargetClosedEmbeddingClosednessW1212
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1213 returns the constructed W987 branch full data from W1006 through W1212. -/
noncomputable def fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  fullDataOfTargetClosedEmbeddingClosednessW1212
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

theorem directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessW1212
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

noncomputable def boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessW1212
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

def targetClosedEmbeddingClosednessNormalizedSourceEndpointInputNamesW1213 : List String :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointInputNamesW1015

theorem targetClosedEmbeddingClosednessNormalizedSourceEndpointInputNamesW1213_count :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointInputNamesW1213.length =
      2 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointInputNamesW1015_count

structure MetrizableTargetClosedEmbeddingClosednessNormalizedSourceEndpointToTargetClosedEmbeddingClosednessDirectRouteStateW1213 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetClosedEmbeddingClosednessNormalizedSourceEndpointToTargetClosedEmbeddingClosednessDirectRouteStateW1213 :
    MetrizableTargetClosedEmbeddingClosednessNormalizedSourceEndpointToTargetClosedEmbeddingClosednessDirectRouteStateW1213
    where
  seed := "w1213-target-closed-embedding-closedness-normalized-source-endpoint-to-w1212-target-closed-embedding-closedness-route"
  declarations :=
    ["targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "endpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "localizedUnitChoiceDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "unitStrictExactIsoDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "componentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "currentFullDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "branchFullDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "componentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "currentFullDataProviderOfCurrentFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "branchFullDataProviderOfBranchFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfTargetClosedEmbeddingClosednessOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "currentFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "branchFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "targetSurjectiveCompactDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1213",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointInputNamesW1213_count"]
  providerRepackagingResult :=
    "proved: W1213 constructs the W1212 W1014 target/closed-embedding\
      closedness input surface from W1015 target/closedness/normalized-source/\
      endpoint data and feeds W1212"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1213 inherits W1212/W1112/W1111/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/\
      W1098/W1097/W1096/W1095/W1094/W1093/W1092/W1091/W1090/W1089/\
      W1088/W1087/W1086/W1085/W1084/W1083/W1082/W1081/W1080/W1079/\
      W1078/W1077/W1076/W1075/W1074/W1073/W1072/W1071/W1070/W1069/\
      W1068/W1067/W1066/W1065/W1064/W1063/W1062/W1061/W1060/W1059/\
      W1058/W1057/W1056/W1055/W1054/W1053/W1052/W1051/W1050/W1049/\
      W1048/W1047/W1046/W1045/W1044/W1043/W1042/W1041/W1040/W1039/\
      W1038/W1037/W1036/W1035/W1034/W1033/W1032/W1031/W1030/W1029/\
      W1028/W1027/W1026/W1025/W1024/W1023/W1022/W1021/W1020/W1019/\
      W1018/W1017/W1016/W1015/W1014/W1013/W1012/W1011/W1010/W1009/\
      W1008/W1007/W1006/W1005/W1004/W1003/W1002/W998 target\
      surjective-compact recovery after W1015 constructs W1005"
  exactAtResult :=
    "proved: the W1213 W1015 target/closedness/normalized-source/endpoint\
      input surface feeds W1212/W1112/W1111/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/W1098/\
      W1097/W1096/W1095/W1094/W1093/W1092/W1091/W1090/W1089/W1088/\
      W1087/W1086/W1085/W1084/W1083/W1082/W1081/W1080/W1079/W1078/\
      W1077/W1076/W1075/W1074/W1073/W1072/W1071/W1070/W1069/W1068/\
      W1067/W1066/W1065/W1064/W1063/W1062/W1061/W1060/W1059/W1058/\
      W1057/W1056/W1055/W1054/W1053/W1052/W1051/W1050/W1049/W1048/\
      W1047/W1046/W1045/W1044/W1043/W1042/W1041/W1040/W1039/W1038/\
      W1037/W1036/W1035/W1034/W1033/W1032/W1031/W1030/W1029/W1028/\
      W1027/W1026/W1025/W1024/W1023/W1022/W1021/W1020/W1019/W1018/\
      W1017/W1016/W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/\
      W1007/W1006/W1005/W1004/W1003/W1002/W998/W997/W996/W995/W994/\
      W993/W988/W987/W986/W985/W984/W983/W982/W981/W980/W979/W978/\
      W977/W976/W975/W974/W973/W972/W971/W970/W969/W968/W967/W966/\
      W965/W964/W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/\
      W952 stable ExactAt route"
  remainingInputs := targetClosedEmbeddingClosednessNormalizedSourceEndpointInputNamesW1213
  productSuccessClaimed := false

theorem currentW1213TargetClosedEmbeddingClosednessNormalizedSourceEndpointToTargetClosedEmbeddingClosednessDirectRoute_productSuccess :
    (let state :=
        currentMetrizableTargetClosedEmbeddingClosednessNormalizedSourceEndpointToTargetClosedEmbeddingClosednessDirectRouteStateW1213;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
