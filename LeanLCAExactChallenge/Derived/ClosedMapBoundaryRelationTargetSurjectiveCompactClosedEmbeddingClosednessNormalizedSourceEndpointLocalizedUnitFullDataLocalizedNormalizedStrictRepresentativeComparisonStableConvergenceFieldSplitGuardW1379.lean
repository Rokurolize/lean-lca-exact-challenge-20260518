import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataSourceEndpointFieldsComparisonStableConvergenceFieldSplitGuardW1378
import LeanLCAExactChallenge.Derived.StrictRepresentativeLiftFieldsComparisonStableExactAtRoute

/-!
W1379 records the definitional convergence of the W887/W888/W889/W890
comparison stable ExactAt route from localized-right-adjoint fields down to
normalized fixed-target and strict-representative lift fields.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W887 localized-right-adjoint provider is assembled from its three explicit fields. -/
theorem w887LocalizedRightAdjointDataRunsThroughFieldsW1379
    (leaves : MetrizableWppLocalizedRightAdjointFieldLeavesW887) :
    localizedRightAdjointDataOfFieldsW887 leaves =
      { boundedHomotopyLocalizedRightAdjoint :=
          leaves.boundedHomotopyLocalizedRightAdjoint
        boundedHomotopyLocalizedAdjunction :=
          leaves.boundedHomotopyLocalizedAdjunction
        boundedHomotopyLocalizedUnitMem :=
          leaves.boundedHomotopyLocalizedUnitMem } :=
  rfl

/-- W887 concrete leaves delegate to W886 after localized-right-adjoint assembly. -/
theorem w887ConcreteLeavesRunThroughW886W1379
    (leaves : MetrizableWppLocalizedRightAdjointFieldLeavesW887) :
    concreteLeavesOfLocalizedRightAdjointFieldsComparisonW887 leaves =
      concreteLeavesOfEndpointFieldsComparisonW886
        (endpointStrictTopologyFieldLeavesOfLocalizedRightAdjointFieldsW887
          leaves) :=
  rfl

/-- W887 route data delegates to W886 after localized-right-adjoint assembly. -/
theorem w887RouteDataProviderRunsThroughW886W1379
    (leaves : MetrizableWppLocalizedRightAdjointFieldLeavesW887) :
    routeDataProviderOfLocalizedRightAdjointFieldsComparisonW887 leaves =
      routeDataProviderOfEndpointFieldsComparisonW886
        (endpointStrictTopologyFieldLeavesOfLocalizedRightAdjointFieldsW887
          leaves) :=
  rfl

/-- W887 direct calculus delegates to W886 after localized-right-adjoint assembly. -/
theorem w887DirectCalculusRunsThroughW886W1379
    (leaves : MetrizableWppLocalizedRightAdjointFieldLeavesW887) :
    directBoundedLeftCalculusOfLocalizedRightAdjointFieldsComparisonStableExactAtW887
        leaves =
      directBoundedLeftCalculusOfEndpointFieldsComparisonStableExactAtW886
        (endpointStrictTopologyFieldLeavesOfLocalizedRightAdjointFieldsW887
          leaves) :=
  rfl

/-- W887 stable package delegates to W886 after localized-right-adjoint assembly. -/
theorem w887StablePackageRunsThroughW886W1379
    (leaves : MetrizableWppLocalizedRightAdjointFieldLeavesW887) :
    boundedDerivedInfinityCategoryOfLocalizedRightAdjointFieldsComparisonStableExactAtW887
        leaves =
      boundedDerivedInfinityCategoryOfEndpointFieldsComparisonStableExactAtW886
        (endpointStrictTopologyFieldLeavesOfLocalizedRightAdjointFieldsW887
          leaves) :=
  rfl

/-- W888 normalized fixed-target provider is assembled from its three explicit fields. -/
theorem w888NormalizedFixedTargetDataRunsThroughFieldsW1379
    (leaves : MetrizableWppNormalizedFixedTargetFieldLeavesW888) :
    normalizedFixedTargetDataOfFieldsW888 leaves =
      { normalizedLiftBlueprint := leaves.normalizedLiftBlueprint
        targetFixedTargetUniq := leaves.targetFixedTargetUniq
        localizationModelFixedTargetUniq :=
          leaves.localizationModelFixedTargetUniq } :=
  rfl

/-- W888 concrete leaves delegate to W887 after normalized fixed-target assembly. -/
theorem w888ConcreteLeavesRunThroughW887W1379
    (leaves : MetrizableWppNormalizedFixedTargetFieldLeavesW888) :
    concreteLeavesOfNormalizedFixedTargetFieldsComparisonW888 leaves =
      concreteLeavesOfLocalizedRightAdjointFieldsComparisonW887
        (localizedRightAdjointFieldLeavesOfNormalizedFixedTargetFieldsW888
          leaves) :=
  rfl

/-- W888 route data delegates to W887 after normalized fixed-target assembly. -/
theorem w888RouteDataProviderRunsThroughW887W1379
    (leaves : MetrizableWppNormalizedFixedTargetFieldLeavesW888) :
    routeDataProviderOfNormalizedFixedTargetFieldsComparisonW888 leaves =
      routeDataProviderOfLocalizedRightAdjointFieldsComparisonW887
        (localizedRightAdjointFieldLeavesOfNormalizedFixedTargetFieldsW888
          leaves) :=
  rfl

/-- W888 direct calculus delegates to W887 after normalized fixed-target assembly. -/
theorem w888DirectCalculusRunsThroughW887W1379
    (leaves : MetrizableWppNormalizedFixedTargetFieldLeavesW888) :
    directBoundedLeftCalculusOfNormalizedFixedTargetFieldsComparisonStableExactAtW888
        leaves =
      directBoundedLeftCalculusOfLocalizedRightAdjointFieldsComparisonStableExactAtW887
        (localizedRightAdjointFieldLeavesOfNormalizedFixedTargetFieldsW888
          leaves) :=
  rfl

/-- W888 stable package delegates to W887 after normalized fixed-target assembly. -/
theorem w888StablePackageRunsThroughW887W1379
    (leaves : MetrizableWppNormalizedFixedTargetFieldLeavesW888) :
    boundedDerivedInfinityCategoryOfNormalizedFixedTargetFieldsComparisonStableExactAtW888
        leaves =
      boundedDerivedInfinityCategoryOfLocalizedRightAdjointFieldsComparisonStableExactAtW887
        (localizedRightAdjointFieldLeavesOfNormalizedFixedTargetFieldsW888
          leaves) :=
  rfl

/-- W889 normalized lift blueprint is assembled from explicit blueprint normalization fields. -/
theorem w889NormalizedLiftBlueprintRunsThroughFieldsW1379
    (leaves : MetrizableWppNormalizedLiftBlueprintFieldLeavesW889) :
    normalizedLiftBlueprintOfFieldsW889 leaves =
      { blueprint := leaves.strictRepresentativeLiftBlueprint
        obj_image := leaves.sourceImageObjectNormalization
        map_image := leaves.sourceImageMapNormalization } :=
  rfl

/-- W889 concrete leaves delegate to W888 after normalized-lift assembly. -/
theorem w889ConcreteLeavesRunThroughW888W1379
    (leaves : MetrizableWppNormalizedLiftBlueprintFieldLeavesW889) :
    concreteLeavesOfNormalizedLiftBlueprintFieldsComparisonW889 leaves =
      concreteLeavesOfNormalizedFixedTargetFieldsComparisonW888
        (normalizedFixedTargetFieldLeavesOfNormalizedLiftBlueprintFieldsW889
          leaves) :=
  rfl

/-- W889 route data delegates to W888 after normalized-lift assembly. -/
theorem w889RouteDataProviderRunsThroughW888W1379
    (leaves : MetrizableWppNormalizedLiftBlueprintFieldLeavesW889) :
    routeDataProviderOfNormalizedLiftBlueprintFieldsComparisonW889 leaves =
      routeDataProviderOfNormalizedFixedTargetFieldsComparisonW888
        (normalizedFixedTargetFieldLeavesOfNormalizedLiftBlueprintFieldsW889
          leaves) :=
  rfl

/-- W889 direct calculus delegates to W888 after normalized-lift assembly. -/
theorem w889DirectCalculusRunsThroughW888W1379
    (leaves : MetrizableWppNormalizedLiftBlueprintFieldLeavesW889) :
    directBoundedLeftCalculusOfNormalizedLiftBlueprintFieldsComparisonStableExactAtW889
        leaves =
      directBoundedLeftCalculusOfNormalizedFixedTargetFieldsComparisonStableExactAtW888
        (normalizedFixedTargetFieldLeavesOfNormalizedLiftBlueprintFieldsW889
          leaves) :=
  rfl

/-- W889 stable package delegates to W888 after normalized-lift assembly. -/
theorem w889StablePackageRunsThroughW888W1379
    (leaves : MetrizableWppNormalizedLiftBlueprintFieldLeavesW889) :
    boundedDerivedInfinityCategoryOfNormalizedLiftBlueprintFieldsComparisonStableExactAtW889
        leaves =
      boundedDerivedInfinityCategoryOfNormalizedFixedTargetFieldsComparisonStableExactAtW888
        (normalizedFixedTargetFieldLeavesOfNormalizedLiftBlueprintFieldsW889
          leaves) :=
  rfl

/-- W890 strict-representative lift blueprint is assembled from object/map/coherence fields. -/
theorem w890StrictRepresentativeLiftBlueprintRunsThroughFieldsW1379
    (leaves : MetrizableWppStrictRepresentativeLiftBlueprintFieldLeavesW890) :
    strictRepresentativeLiftBlueprintOfFieldsW890 leaves =
      { objData := leaves.strictRepresentativeObjectData
        mapData := leaves.strictRepresentativeMapData
        map_id := leaves.strictRepresentativeMapId
        map_comp := leaves.strictRepresentativeMapComp } :=
  rfl

/-- W890 concrete leaves delegate to W889 after strict-representative assembly. -/
theorem w890ConcreteLeavesRunThroughW889W1379
    (leaves : MetrizableWppStrictRepresentativeLiftBlueprintFieldLeavesW890) :
    concreteLeavesOfStrictRepresentativeFieldsComparisonW890 leaves =
      concreteLeavesOfNormalizedLiftBlueprintFieldsComparisonW889
        (normalizedLiftBlueprintFieldLeavesOfStrictRepresentativeFieldsW890
          leaves) :=
  rfl

/-- W890 route data delegates to W889 after strict-representative assembly. -/
theorem w890RouteDataProviderRunsThroughW889W1379
    (leaves : MetrizableWppStrictRepresentativeLiftBlueprintFieldLeavesW890) :
    routeDataProviderOfStrictRepresentativeFieldsComparisonW890 leaves =
      routeDataProviderOfNormalizedLiftBlueprintFieldsComparisonW889
        (normalizedLiftBlueprintFieldLeavesOfStrictRepresentativeFieldsW890
          leaves) :=
  rfl

/-- W890 direct calculus delegates to W889 after strict-representative assembly. -/
theorem w890DirectCalculusRunsThroughW889W1379
    (leaves : MetrizableWppStrictRepresentativeLiftBlueprintFieldLeavesW890) :
    directBoundedLeftCalculusOfStrictRepresentativeFieldsComparisonStableExactAtW890
        leaves =
      directBoundedLeftCalculusOfNormalizedLiftBlueprintFieldsComparisonStableExactAtW889
        (normalizedLiftBlueprintFieldLeavesOfStrictRepresentativeFieldsW890
          leaves) :=
  rfl

/-- W890 stable package delegates to W889 after strict-representative assembly. -/
theorem w890StablePackageRunsThroughW889W1379
    (leaves : MetrizableWppStrictRepresentativeLiftBlueprintFieldLeavesW890) :
    boundedDerivedInfinityCategoryOfStrictRepresentativeFieldsComparisonStableExactAtW890
        leaves =
      boundedDerivedInfinityCategoryOfNormalizedLiftBlueprintFieldsComparisonStableExactAtW889
        (normalizedLiftBlueprintFieldLeavesOfStrictRepresentativeFieldsW890
          leaves) :=
  rfl

/-- W1379 keeps the W887 localized-right-adjoint field count visible. -/
theorem w1379LocalizedRightAdjointFieldsComparisonStableExactAtInputCountMatchesW887 :
    localizedRightAdjointFieldsComparisonStableExactAtInputNamesW887.length =
      15 :=
  localizedRightAdjointFieldsComparisonStableExactAtInputNamesW887_count

/-- W1379 keeps the W888 normalized fixed-target field count visible. -/
theorem w1379NormalizedFixedTargetFieldsComparisonStableExactAtInputCountMatchesW888 :
    normalizedFixedTargetFieldsComparisonStableExactAtInputNamesW888.length =
      17 :=
  normalizedFixedTargetFieldsComparisonStableExactAtInputNamesW888_count

/-- W1379 keeps the W889 normalized-lift blueprint field count visible. -/
theorem w1379NormalizedLiftBlueprintFieldsComparisonStableExactAtInputCountMatchesW889 :
    normalizedLiftBlueprintFieldsComparisonStableExactAtInputNamesW889.length =
      19 :=
  normalizedLiftBlueprintFieldsComparisonStableExactAtInputNamesW889_count

/-- W1379 keeps the W890 strict-representative field count visible. -/
theorem w1379StrictRepresentativeFieldsComparisonStableExactAtInputCountMatchesW890 :
    strictRepresentativeFieldsComparisonStableExactAtInputNamesW890.length =
      22 :=
  strictRepresentativeFieldsComparisonStableExactAtInputNamesW890_count

/-- Current W1379 nonterminal state. -/
structure LocalizedNormalizedStrictRepresentativeComparisonStableConvergenceStateW1379 :
    Type where
  seed : String
  declarations : List String
  localizedRightAdjointResult : String
  normalizedFixedTargetResult : String
  normalizedLiftBlueprintResult : String
  strictRepresentativeResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/--
W1379 records W887-W890 convergence into the comparison stable ExactAt route.
-/
def currentLocalizedNormalizedStrictRepresentativeComparisonStableConvergenceStateW1379 :
    LocalizedNormalizedStrictRepresentativeComparisonStableConvergenceStateW1379 where
  seed := "w1379-localized-normalized-strict-representative-comparison-stable-convergence"
  declarations :=
    ["w887LocalizedRightAdjointDataRunsThroughFieldsW1379",
      "w887ConcreteLeavesRunThroughW886W1379",
      "w887RouteDataProviderRunsThroughW886W1379",
      "w887DirectCalculusRunsThroughW886W1379",
      "w887StablePackageRunsThroughW886W1379",
      "w888NormalizedFixedTargetDataRunsThroughFieldsW1379",
      "w888ConcreteLeavesRunThroughW887W1379",
      "w888RouteDataProviderRunsThroughW887W1379",
      "w888DirectCalculusRunsThroughW887W1379",
      "w888StablePackageRunsThroughW887W1379",
      "w889NormalizedLiftBlueprintRunsThroughFieldsW1379",
      "w889ConcreteLeavesRunThroughW888W1379",
      "w889RouteDataProviderRunsThroughW888W1379",
      "w889DirectCalculusRunsThroughW888W1379",
      "w889StablePackageRunsThroughW888W1379",
      "w890StrictRepresentativeLiftBlueprintRunsThroughFieldsW1379",
      "w890ConcreteLeavesRunThroughW889W1379",
      "w890RouteDataProviderRunsThroughW889W1379",
      "w890DirectCalculusRunsThroughW889W1379",
      "w890StablePackageRunsThroughW889W1379",
      "w1379LocalizedRightAdjointFieldsComparisonStableExactAtInputCountMatchesW887",
      "w1379NormalizedFixedTargetFieldsComparisonStableExactAtInputCountMatchesW888",
      "w1379NormalizedLiftBlueprintFieldsComparisonStableExactAtInputCountMatchesW889",
      "w1379StrictRepresentativeFieldsComparisonStableExactAtInputCountMatchesW890"]
  localizedRightAdjointResult :=
    "proved: W887 assembles W721 localized-right-adjoint data from explicit \
      fields and delegates to W886"
  normalizedFixedTargetResult :=
    "proved: W888 assembles W719 normalized fixed-target data from explicit \
      fields and delegates to W887"
  normalizedLiftBlueprintResult :=
    "proved: W889 assembles the normalized strict-representative lift blueprint \
      from explicit normalization fields and delegates to W888"
  strictRepresentativeResult :=
    "proved: W890 assembles the strict-representative lift blueprint from \
      object, map, identity, and composition fields and delegates to W889"
  remainingInputs :=
    strictRepresentativeFieldsComparisonStableExactAtInputNamesW890
  productSuccessClaimed := false

theorem
    currentW1379LocalizedNormalizedStrictRepresentativeComparisonStableConvergence_productSuccess :
    currentLocalizedNormalizedStrictRepresentativeComparisonStableConvergenceStateW1379.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
