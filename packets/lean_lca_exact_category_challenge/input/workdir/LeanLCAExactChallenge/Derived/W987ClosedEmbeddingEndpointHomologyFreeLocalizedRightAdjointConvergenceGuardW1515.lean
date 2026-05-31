import LeanLCAExactChallenge.Derived.W987ClosedEmbeddingEndpointHomologyFreeStrictPreimageConvergenceGuardW1514
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataLocalizedNormalizedStrictRepresentativeComparisonStableConvergenceFieldSplitGuardW1379

/-!
W1515 composes the W1514 W987 strict-representative route with the existing
W1379 localized/normalized strict-representative convergence guard. W1514
reaches W890; W1379 records the W890-to-W889, W889-to-W888, W888-to-W887, and
W887-to-W886 delegations.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

noncomputable section

/-- W1515 reuses the W1514 strict-preimage convergence surface. -/
abbrev W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputW1515 :
    Type 2 :=
  W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputW1514

/-- W1515 names the W890 strict-representative leaves reached by W1514. -/
def strictRepresentativeFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputW1515) :
    MetrizableWppStrictRepresentativeLiftBlueprintFieldLeavesW890 :=
  strictRepresentativeFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
    input

/-- W1515 projects W1514's W890 leaves to W889 normalized-lift leaves. -/
def normalizedLiftBlueprintFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputW1515) :
    MetrizableWppNormalizedLiftBlueprintFieldLeavesW889 :=
  normalizedLiftBlueprintFieldLeavesOfStrictRepresentativeFieldsW890
    (strictRepresentativeFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
      input)

/-- W1515 projects W1514 through W889 to W888 normalized fixed-target leaves. -/
def normalizedFixedTargetFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputW1515) :
    MetrizableWppNormalizedFixedTargetFieldLeavesW888 :=
  normalizedFixedTargetFieldLeavesOfNormalizedLiftBlueprintFieldsW889
    (normalizedLiftBlueprintFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
      input)

/-- W1515 projects W1514 through W888 to W887 localized-right-adjoint leaves. -/
def localizedRightAdjointFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputW1515) :
    MetrizableWppLocalizedRightAdjointFieldLeavesW887 :=
  localizedRightAdjointFieldLeavesOfNormalizedFixedTargetFieldsW888
    (normalizedFixedTargetFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
      input)

/-- W1515 projects W1514 through W887 to W886 endpoint strict-topology leaves. -/
def endpointStrictTopologyFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputW1515) :
    MetrizableWppEndpointStrictTopologyFieldLeavesW886 :=
  endpointStrictTopologyFieldLeavesOfLocalizedRightAdjointFieldsW887
    (localizedRightAdjointFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
      input)

/-- W1515 exposes the same concrete leaves as W1514. -/
def concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputW1515) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
    input

/-- W1515 exposes the same route data as W1514. -/
def routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputW1515) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
    input

/-- W1515 exposes the same direct bounded left calculus package as W1514. -/
theorem directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputW1515) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
    input

/-- W1515 exposes the same bounded derived infinity-category package as W1514. -/
def boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputW1515) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
    input

/-- W1515 specializes W1379's W890 strict-representative assembly to W1514 leaves. -/
theorem w1515StrictRepresentativeLiftBlueprintRunsThroughW890W1379
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputW1515) :
    strictRepresentativeLiftBlueprintOfFieldsW890
        (strictRepresentativeFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input) =
      { objData :=
          (strictRepresentativeFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input).strictRepresentativeObjectData
        mapData :=
          (strictRepresentativeFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input).strictRepresentativeMapData
        map_id :=
          (strictRepresentativeFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input).strictRepresentativeMapId
        map_comp :=
          (strictRepresentativeFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input).strictRepresentativeMapComp } :=
  w890StrictRepresentativeLiftBlueprintRunsThroughFieldsW1379
    (strictRepresentativeFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
      input)

/-- W1515 specializes W1379's W889 normalized-lift assembly to W1514 leaves. -/
theorem w1515NormalizedLiftBlueprintRunsThroughW889W1379
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputW1515) :
    normalizedLiftBlueprintOfFieldsW889
        (normalizedLiftBlueprintFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input) =
      { blueprint :=
          (normalizedLiftBlueprintFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input).strictRepresentativeLiftBlueprint
        obj_image :=
          (normalizedLiftBlueprintFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input).sourceImageObjectNormalization
        map_image :=
          (normalizedLiftBlueprintFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input).sourceImageMapNormalization } :=
  w889NormalizedLiftBlueprintRunsThroughFieldsW1379
    (normalizedLiftBlueprintFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
      input)

/-- W1515 specializes W1379's W888 normalized fixed-target assembly to W1514 leaves. -/
theorem w1515NormalizedFixedTargetDataRunsThroughW888W1379
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputW1515) :
    normalizedFixedTargetDataOfFieldsW888
        (normalizedFixedTargetFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input) =
      { normalizedLiftBlueprint :=
          (normalizedFixedTargetFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input).normalizedLiftBlueprint
        targetFixedTargetUniq :=
          (normalizedFixedTargetFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input).targetFixedTargetUniq
        localizationModelFixedTargetUniq :=
          (normalizedFixedTargetFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input).localizationModelFixedTargetUniq } :=
  w888NormalizedFixedTargetDataRunsThroughFieldsW1379
    (normalizedFixedTargetFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
      input)

/-- W1515 specializes W1379's W887 localized-right-adjoint assembly to W1514 leaves. -/
theorem w1515LocalizedRightAdjointDataRunsThroughW887W1379
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputW1515) :
    localizedRightAdjointDataOfFieldsW887
        (localizedRightAdjointFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input) =
      { boundedHomotopyLocalizedRightAdjoint :=
          (localizedRightAdjointFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input).boundedHomotopyLocalizedRightAdjoint
        boundedHomotopyLocalizedAdjunction :=
          (localizedRightAdjointFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input).boundedHomotopyLocalizedAdjunction
        boundedHomotopyLocalizedUnitMem :=
          (localizedRightAdjointFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input).boundedHomotopyLocalizedUnitMem } :=
  w887LocalizedRightAdjointDataRunsThroughFieldsW1379
    (localizedRightAdjointFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
      input)

/-- W1515 composes W1514's W890 route with W1379's W890-to-W889 step. -/
theorem w1515ConcreteLeavesRunThroughW890W889
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputW1515) :
    concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
        input =
      concreteLeavesOfNormalizedLiftBlueprintFieldsComparisonW889
        (normalizedLiftBlueprintFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input) := by
  calc
    concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
        input =
        concreteLeavesOfStrictRepresentativeFieldsComparisonW890
          (strictRepresentativeFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input) :=
      w1514ConcreteLeavesRunThroughW891W890 input
    _ =
        concreteLeavesOfNormalizedLiftBlueprintFieldsComparisonW889
          (normalizedLiftBlueprintFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input) :=
      w890ConcreteLeavesRunThroughW889W1379
        (strictRepresentativeFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input)

theorem w1515RouteDataProviderRunsThroughW890W889
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputW1515) :
    routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
        input =
      routeDataProviderOfNormalizedLiftBlueprintFieldsComparisonW889
        (normalizedLiftBlueprintFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input) := by
  calc
    routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
        input =
        routeDataProviderOfStrictRepresentativeFieldsComparisonW890
          (strictRepresentativeFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input) :=
      w1514RouteDataProviderRunsThroughW891W890 input
    _ =
        routeDataProviderOfNormalizedLiftBlueprintFieldsComparisonW889
          (normalizedLiftBlueprintFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input) :=
      w890RouteDataProviderRunsThroughW889W1379
        (strictRepresentativeFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input)

theorem w1515DirectCalculusRunsThroughW890W889
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputW1515) :
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
        input =
      directBoundedLeftCalculusOfNormalizedLiftBlueprintFieldsComparisonStableExactAtW889
        (normalizedLiftBlueprintFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input) := by
  calc
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
        input =
        directBoundedLeftCalculusOfStrictRepresentativeFieldsComparisonStableExactAtW890
          (strictRepresentativeFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input) :=
      w1514DirectCalculusRunsThroughW891W890 input
    _ =
        directBoundedLeftCalculusOfNormalizedLiftBlueprintFieldsComparisonStableExactAtW889
          (normalizedLiftBlueprintFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input) :=
      w890DirectCalculusRunsThroughW889W1379
        (strictRepresentativeFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input)

theorem w1515StablePackageRunsThroughW890W889
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputW1515) :
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
        input =
      boundedDerivedInfinityCategoryOfNormalizedLiftBlueprintFieldsComparisonStableExactAtW889
        (normalizedLiftBlueprintFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input) := by
  calc
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
        input =
        boundedDerivedInfinityCategoryOfStrictRepresentativeFieldsComparisonStableExactAtW890
          (strictRepresentativeFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input) :=
      w1514StablePackageRunsThroughW891W890 input
    _ =
        boundedDerivedInfinityCategoryOfNormalizedLiftBlueprintFieldsComparisonStableExactAtW889
          (normalizedLiftBlueprintFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input) :=
      w890StablePackageRunsThroughW889W1379
        (strictRepresentativeFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input)

/-- W1515 further composes through W889 to W888. -/
theorem w1515ConcreteLeavesRunThroughW889W888
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputW1515) :
    concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
        input =
      concreteLeavesOfNormalizedFixedTargetFieldsComparisonW888
        (normalizedFixedTargetFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input) := by
  calc
    concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
        input =
        concreteLeavesOfNormalizedLiftBlueprintFieldsComparisonW889
          (normalizedLiftBlueprintFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input) :=
      w1515ConcreteLeavesRunThroughW890W889 input
    _ =
        concreteLeavesOfNormalizedFixedTargetFieldsComparisonW888
          (normalizedFixedTargetFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input) :=
      w889ConcreteLeavesRunThroughW888W1379
        (normalizedLiftBlueprintFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input)

theorem w1515RouteDataProviderRunsThroughW889W888
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputW1515) :
    routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
        input =
      routeDataProviderOfNormalizedFixedTargetFieldsComparisonW888
        (normalizedFixedTargetFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input) := by
  calc
    routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
        input =
        routeDataProviderOfNormalizedLiftBlueprintFieldsComparisonW889
          (normalizedLiftBlueprintFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input) :=
      w1515RouteDataProviderRunsThroughW890W889 input
    _ =
        routeDataProviderOfNormalizedFixedTargetFieldsComparisonW888
          (normalizedFixedTargetFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input) :=
      w889RouteDataProviderRunsThroughW888W1379
        (normalizedLiftBlueprintFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input)

theorem w1515DirectCalculusRunsThroughW889W888
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputW1515) :
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
        input =
      directBoundedLeftCalculusOfNormalizedFixedTargetFieldsComparisonStableExactAtW888
        (normalizedFixedTargetFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input) := by
  calc
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
        input =
        directBoundedLeftCalculusOfNormalizedLiftBlueprintFieldsComparisonStableExactAtW889
          (normalizedLiftBlueprintFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input) :=
      w1515DirectCalculusRunsThroughW890W889 input
    _ =
        directBoundedLeftCalculusOfNormalizedFixedTargetFieldsComparisonStableExactAtW888
          (normalizedFixedTargetFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input) :=
      w889DirectCalculusRunsThroughW888W1379
        (normalizedLiftBlueprintFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input)

theorem w1515StablePackageRunsThroughW889W888
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputW1515) :
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
        input =
      boundedDerivedInfinityCategoryOfNormalizedFixedTargetFieldsComparisonStableExactAtW888
        (normalizedFixedTargetFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input) := by
  calc
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
        input =
        boundedDerivedInfinityCategoryOfNormalizedLiftBlueprintFieldsComparisonStableExactAtW889
          (normalizedLiftBlueprintFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input) :=
      w1515StablePackageRunsThroughW890W889 input
    _ =
        boundedDerivedInfinityCategoryOfNormalizedFixedTargetFieldsComparisonStableExactAtW888
          (normalizedFixedTargetFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input) :=
      w889StablePackageRunsThroughW888W1379
        (normalizedLiftBlueprintFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input)

/-- W1515 further composes through W888 to W887. -/
theorem w1515ConcreteLeavesRunThroughW888W887
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputW1515) :
    concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
        input =
      concreteLeavesOfLocalizedRightAdjointFieldsComparisonW887
        (localizedRightAdjointFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input) := by
  calc
    concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
        input =
        concreteLeavesOfNormalizedFixedTargetFieldsComparisonW888
          (normalizedFixedTargetFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input) :=
      w1515ConcreteLeavesRunThroughW889W888 input
    _ =
        concreteLeavesOfLocalizedRightAdjointFieldsComparisonW887
          (localizedRightAdjointFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input) :=
      w888ConcreteLeavesRunThroughW887W1379
        (normalizedFixedTargetFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input)

theorem w1515RouteDataProviderRunsThroughW888W887
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputW1515) :
    routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
        input =
      routeDataProviderOfLocalizedRightAdjointFieldsComparisonW887
        (localizedRightAdjointFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input) := by
  calc
    routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
        input =
        routeDataProviderOfNormalizedFixedTargetFieldsComparisonW888
          (normalizedFixedTargetFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input) :=
      w1515RouteDataProviderRunsThroughW889W888 input
    _ =
        routeDataProviderOfLocalizedRightAdjointFieldsComparisonW887
          (localizedRightAdjointFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input) :=
      w888RouteDataProviderRunsThroughW887W1379
        (normalizedFixedTargetFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input)

theorem w1515DirectCalculusRunsThroughW888W887
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputW1515) :
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
        input =
      directBoundedLeftCalculusOfLocalizedRightAdjointFieldsComparisonStableExactAtW887
        (localizedRightAdjointFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input) := by
  calc
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
        input =
        directBoundedLeftCalculusOfNormalizedFixedTargetFieldsComparisonStableExactAtW888
          (normalizedFixedTargetFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input) :=
      w1515DirectCalculusRunsThroughW889W888 input
    _ =
        directBoundedLeftCalculusOfLocalizedRightAdjointFieldsComparisonStableExactAtW887
          (localizedRightAdjointFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input) :=
      w888DirectCalculusRunsThroughW887W1379
        (normalizedFixedTargetFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input)

theorem w1515StablePackageRunsThroughW888W887
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputW1515) :
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
        input =
      boundedDerivedInfinityCategoryOfLocalizedRightAdjointFieldsComparisonStableExactAtW887
        (localizedRightAdjointFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input) := by
  calc
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
        input =
        boundedDerivedInfinityCategoryOfNormalizedFixedTargetFieldsComparisonStableExactAtW888
          (normalizedFixedTargetFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input) :=
      w1515StablePackageRunsThroughW889W888 input
    _ =
        boundedDerivedInfinityCategoryOfLocalizedRightAdjointFieldsComparisonStableExactAtW887
          (localizedRightAdjointFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input) :=
      w888StablePackageRunsThroughW887W1379
        (normalizedFixedTargetFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input)

/-- W1515 further composes through W887 to W886. -/
theorem w1515ConcreteLeavesRunThroughW887W886
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputW1515) :
    concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
        input =
      concreteLeavesOfEndpointFieldsComparisonW886
        (endpointStrictTopologyFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input) := by
  calc
    concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
        input =
        concreteLeavesOfLocalizedRightAdjointFieldsComparisonW887
          (localizedRightAdjointFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input) :=
      w1515ConcreteLeavesRunThroughW888W887 input
    _ =
        concreteLeavesOfEndpointFieldsComparisonW886
          (endpointStrictTopologyFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input) :=
      w887ConcreteLeavesRunThroughW886W1379
        (localizedRightAdjointFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input)

theorem w1515RouteDataProviderRunsThroughW887W886
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputW1515) :
    routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
        input =
      routeDataProviderOfEndpointFieldsComparisonW886
        (endpointStrictTopologyFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input) := by
  calc
    routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
        input =
        routeDataProviderOfLocalizedRightAdjointFieldsComparisonW887
          (localizedRightAdjointFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input) :=
      w1515RouteDataProviderRunsThroughW888W887 input
    _ =
        routeDataProviderOfEndpointFieldsComparisonW886
          (endpointStrictTopologyFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input) :=
      w887RouteDataProviderRunsThroughW886W1379
        (localizedRightAdjointFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input)

theorem w1515DirectCalculusRunsThroughW887W886
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputW1515) :
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
        input =
      directBoundedLeftCalculusOfEndpointFieldsComparisonStableExactAtW886
        (endpointStrictTopologyFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input) := by
  calc
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
        input =
        directBoundedLeftCalculusOfLocalizedRightAdjointFieldsComparisonStableExactAtW887
          (localizedRightAdjointFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input) :=
      w1515DirectCalculusRunsThroughW888W887 input
    _ =
        directBoundedLeftCalculusOfEndpointFieldsComparisonStableExactAtW886
          (endpointStrictTopologyFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input) :=
      w887DirectCalculusRunsThroughW886W1379
        (localizedRightAdjointFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input)

theorem w1515StablePackageRunsThroughW887W886
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputW1515) :
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
        input =
      boundedDerivedInfinityCategoryOfEndpointFieldsComparisonStableExactAtW886
        (endpointStrictTopologyFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input) := by
  calc
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
        input =
        boundedDerivedInfinityCategoryOfLocalizedRightAdjointFieldsComparisonStableExactAtW887
          (localizedRightAdjointFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input) :=
      w1515StablePackageRunsThroughW888W887 input
    _ =
        boundedDerivedInfinityCategoryOfEndpointFieldsComparisonStableExactAtW886
          (endpointStrictTopologyFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
            input) :=
      w887StablePackageRunsThroughW886W1379
        (localizedRightAdjointFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
          input)

/-- W1515 keeps the W1514 constructor-ledger input names. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputNamesW1515 :
    List String :=
  w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputNamesW1514

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputNamesW1515_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputNamesW1515.length =
      74 := by
  simpa [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputNamesW1515]
    using
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputNamesW1514_count

/-- Current W1515 nonterminal localized-right-adjoint convergence state. -/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceStateW1515 :
    Type where
  seed : String
  declarations : List String
  strictRepresentativeResult : String
  normalizedLiftBlueprintResult : String
  normalizedFixedTargetResult : String
  localizedRightAdjointResult : String
  remainingInputs : List String
  w890RemainingInputs : List String
  w889RemainingInputs : List String
  w888RemainingInputs : List String
  w887RemainingInputs : List String
  productSuccessClaimed : Bool

/-- W1515 records the W1514-to-W1379 localized-right-adjoint convergence bridge. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceStateW1515 :
    W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceStateW1515 where
  seed :=
    "w1515-w987-boundary-relation-target-strict-preimage-object-image-right-adjoint-target-compactness-mapped-cokernel-pi1-pi2-pi3-localized-right-adjoint-convergence"
  declarations :=
    ["W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputW1515",
      "strictRepresentativeFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515",
      "normalizedLiftBlueprintFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515",
      "normalizedFixedTargetFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515",
      "localizedRightAdjointFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515",
      "endpointStrictTopologyFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515",
      "w1515StrictRepresentativeLiftBlueprintRunsThroughW890W1379",
      "w1515NormalizedLiftBlueprintRunsThroughW889W1379",
      "w1515NormalizedFixedTargetDataRunsThroughW888W1379",
      "w1515LocalizedRightAdjointDataRunsThroughW887W1379",
      "w1515ConcreteLeavesRunThroughW890W889",
      "w1515RouteDataProviderRunsThroughW890W889",
      "w1515DirectCalculusRunsThroughW890W889",
      "w1515StablePackageRunsThroughW890W889",
      "w1515ConcreteLeavesRunThroughW889W888",
      "w1515RouteDataProviderRunsThroughW889W888",
      "w1515DirectCalculusRunsThroughW889W888",
      "w1515StablePackageRunsThroughW889W888",
      "w1515ConcreteLeavesRunThroughW888W887",
      "w1515RouteDataProviderRunsThroughW888W887",
      "w1515DirectCalculusRunsThroughW888W887",
      "w1515StablePackageRunsThroughW888W887",
      "w1515ConcreteLeavesRunThroughW887W886",
      "w1515RouteDataProviderRunsThroughW887W886",
      "w1515DirectCalculusRunsThroughW887W886",
      "w1515StablePackageRunsThroughW887W886",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputNamesW1515_count"]
  strictRepresentativeResult :=
    "proved: W1514's W890 strict-representative route specializes W1379's\
      W890-to-W889 convergence"
  normalizedLiftBlueprintResult :=
    "proved: W1515 further composes through W889 and W888"
  normalizedFixedTargetResult :=
    "proved: W1515 further composes through W888 and W887"
  localizedRightAdjointResult :=
    "proved: W1515 further composes the concrete leaves, route data, direct\
      calculus, and stable package through W887 and W886"
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputNamesW1515
  w890RemainingInputs :=
    strictRepresentativeFieldsComparisonStableExactAtInputNamesW890
  w889RemainingInputs :=
    normalizedLiftBlueprintFieldsComparisonStableExactAtInputNamesW889
  w888RemainingInputs :=
    normalizedFixedTargetFieldsComparisonStableExactAtInputNamesW888
  w887RemainingInputs :=
    localizedRightAdjointFieldsComparisonStableExactAtInputNamesW887
  productSuccessClaimed := false

theorem currentW1515W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergence_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceStateW1515.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
