import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosedMapSourceEndpointFixedTargetStableConvergenceFieldSplitGuardW1385
import LeanLCAExactChallenge.Derived.ClosedMapRelationPrimitiveFieldsSourceRawFieldsRoute

/-!
W1386 records definitional convergence for the closed-map W914-W920 route
chain, through selected-difference, target, relation, boundary,
triangle-completion, source, and primitive relation raw field surfaces.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W914 concrete leaves delegate to W913 after selected-difference field bundling. -/
theorem w914ConcreteLeavesRunThroughW913W1386
    (leaves : MetrizableWppClosedMapSelectedDifferenceFieldLeavesW914) :
    concreteLeavesOfClosedMapSelectedDifferenceFieldsW914 leaves =
      concreteLeavesOfClosedMapFixedTargetUniqFieldsW913
        (w913LeavesOfSelectedDifferenceFieldsW914 leaves) :=
  rfl

/-- W914 route data delegates to W913 after selected-difference field bundling. -/
theorem w914RouteDataProviderRunsThroughW913W1386
    (leaves : MetrizableWppClosedMapSelectedDifferenceFieldLeavesW914) :
    routeDataProviderOfClosedMapSelectedDifferenceFieldsW914 leaves =
      routeDataProviderOfClosedMapFixedTargetUniqFieldsW913
        (w913LeavesOfSelectedDifferenceFieldsW914 leaves) :=
  rfl

/-- W914 direct calculus delegates to W913 after selected-difference field bundling. -/
theorem w914DirectCalculusRunsThroughW913W1386
    (leaves : MetrizableWppClosedMapSelectedDifferenceFieldLeavesW914) :
    directBoundedLeftCalculusOfClosedMapSelectedDifferenceFieldsW914 leaves =
      directBoundedLeftCalculusOfClosedMapFixedTargetUniqFieldsW913
        (w913LeavesOfSelectedDifferenceFieldsW914 leaves) :=
  rfl

/-- W914 stable package delegates to W913 after selected-difference field bundling. -/
theorem w914StablePackageRunsThroughW913W1386
    (leaves : MetrizableWppClosedMapSelectedDifferenceFieldLeavesW914) :
    boundedDerivedInfinityCategoryOfClosedMapSelectedDifferenceFieldsW914
        leaves =
      boundedDerivedInfinityCategoryOfClosedMapFixedTargetUniqFieldsW913
        (w913LeavesOfSelectedDifferenceFieldsW914 leaves) :=
  rfl

/-- W915 concrete leaves delegate to W914 after target raw-field bundling. -/
theorem w915ConcreteLeavesRunThroughW914W1386
    (leaves : MetrizableWppClosedMapTargetRawFieldLeavesW915) :
    concreteLeavesOfClosedMapTargetRawFieldsW915 leaves =
      concreteLeavesOfClosedMapSelectedDifferenceFieldsW914
        (w914LeavesOfTargetRawFieldsW915 leaves) :=
  rfl

/-- W915 route data delegates to W914 after target raw-field bundling. -/
theorem w915RouteDataProviderRunsThroughW914W1386
    (leaves : MetrizableWppClosedMapTargetRawFieldLeavesW915) :
    routeDataProviderOfClosedMapTargetRawFieldsW915 leaves =
      routeDataProviderOfClosedMapSelectedDifferenceFieldsW914
        (w914LeavesOfTargetRawFieldsW915 leaves) :=
  rfl

/-- W915 direct calculus delegates to W914 after target raw-field bundling. -/
theorem w915DirectCalculusRunsThroughW914W1386
    (leaves : MetrizableWppClosedMapTargetRawFieldLeavesW915) :
    directBoundedLeftCalculusOfClosedMapTargetRawFieldsW915 leaves =
      directBoundedLeftCalculusOfClosedMapSelectedDifferenceFieldsW914
        (w914LeavesOfTargetRawFieldsW915 leaves) :=
  rfl

/-- W915 stable package delegates to W914 after target raw-field bundling. -/
theorem w915StablePackageRunsThroughW914W1386
    (leaves : MetrizableWppClosedMapTargetRawFieldLeavesW915) :
    boundedDerivedInfinityCategoryOfClosedMapTargetRawFieldsW915 leaves =
      boundedDerivedInfinityCategoryOfClosedMapSelectedDifferenceFieldsW914
        (w914LeavesOfTargetRawFieldsW915 leaves) :=
  rfl

/-- W916 concrete leaves delegate to W915 after relation raw-field bundling. -/
theorem w916ConcreteLeavesRunThroughW915W1386
    (leaves : MetrizableWppClosedMapRelationRawFieldLeavesW916) :
    concreteLeavesOfClosedMapRelationRawFieldsW916 leaves =
      concreteLeavesOfClosedMapTargetRawFieldsW915
        (w915LeavesOfRelationRawFieldsW916 leaves) :=
  rfl

/-- W916 route data delegates to W915 after relation raw-field bundling. -/
theorem w916RouteDataProviderRunsThroughW915W1386
    (leaves : MetrizableWppClosedMapRelationRawFieldLeavesW916) :
    routeDataProviderOfClosedMapRelationRawFieldsW916 leaves =
      routeDataProviderOfClosedMapTargetRawFieldsW915
        (w915LeavesOfRelationRawFieldsW916 leaves) :=
  rfl

/-- W916 direct calculus delegates to W915 after relation raw-field bundling. -/
theorem w916DirectCalculusRunsThroughW915W1386
    (leaves : MetrizableWppClosedMapRelationRawFieldLeavesW916) :
    directBoundedLeftCalculusOfClosedMapRelationRawFieldsW916 leaves =
      directBoundedLeftCalculusOfClosedMapTargetRawFieldsW915
        (w915LeavesOfRelationRawFieldsW916 leaves) :=
  rfl

/-- W916 stable package delegates to W915 after relation raw-field bundling. -/
theorem w916StablePackageRunsThroughW915W1386
    (leaves : MetrizableWppClosedMapRelationRawFieldLeavesW916) :
    boundedDerivedInfinityCategoryOfClosedMapRelationRawFieldsW916 leaves =
      boundedDerivedInfinityCategoryOfClosedMapTargetRawFieldsW915
        (w915LeavesOfRelationRawFieldsW916 leaves) :=
  rfl

/-- W917 concrete leaves delegate to W916 after boundary raw-field bundling. -/
theorem w917ConcreteLeavesRunThroughW916W1386
    (leaves : MetrizableWppClosedMapBoundaryRawFieldLeavesW917) :
    concreteLeavesOfClosedMapBoundaryRawFieldsW917 leaves =
      concreteLeavesOfClosedMapRelationRawFieldsW916
        (w916LeavesOfBoundaryRawFieldsW917 leaves) :=
  rfl

/-- W917 route data delegates to W916 after boundary raw-field bundling. -/
theorem w917RouteDataProviderRunsThroughW916W1386
    (leaves : MetrizableWppClosedMapBoundaryRawFieldLeavesW917) :
    routeDataProviderOfClosedMapBoundaryRawFieldsW917 leaves =
      routeDataProviderOfClosedMapRelationRawFieldsW916
        (w916LeavesOfBoundaryRawFieldsW917 leaves) :=
  rfl

/-- W917 direct calculus delegates to W916 after boundary raw-field bundling. -/
theorem w917DirectCalculusRunsThroughW916W1386
    (leaves : MetrizableWppClosedMapBoundaryRawFieldLeavesW917) :
    directBoundedLeftCalculusOfClosedMapBoundaryRawFieldsW917 leaves =
      directBoundedLeftCalculusOfClosedMapRelationRawFieldsW916
        (w916LeavesOfBoundaryRawFieldsW917 leaves) :=
  rfl

/-- W917 stable package delegates to W916 after boundary raw-field bundling. -/
theorem w917StablePackageRunsThroughW916W1386
    (leaves : MetrizableWppClosedMapBoundaryRawFieldLeavesW917) :
    boundedDerivedInfinityCategoryOfClosedMapBoundaryRawFieldsW917 leaves =
      boundedDerivedInfinityCategoryOfClosedMapRelationRawFieldsW916
        (w916LeavesOfBoundaryRawFieldsW917 leaves) :=
  rfl

/-- W918 concrete leaves delegate to W917 after triangle-completion raw-field bundling. -/
theorem w918ConcreteLeavesRunThroughW917W1386
    (leaves :
      MetrizableWppClosedMapTriangleCompletionRawFieldBoundaryRawFieldLeavesW918) :
    concreteLeavesOfClosedMapTriangleCompletionRawFieldBoundaryRawFieldsW918
        leaves =
      concreteLeavesOfClosedMapBoundaryRawFieldsW917
        (w917LeavesOfTriangleCompletionRawFieldW918 leaves) :=
  rfl

/-- W918 route data delegates to W917 after triangle-completion raw-field bundling. -/
theorem w918RouteDataProviderRunsThroughW917W1386
    (leaves :
      MetrizableWppClosedMapTriangleCompletionRawFieldBoundaryRawFieldLeavesW918) :
    routeDataProviderOfClosedMapTriangleCompletionRawFieldBoundaryRawFieldsW918
        leaves =
      routeDataProviderOfClosedMapBoundaryRawFieldsW917
        (w917LeavesOfTriangleCompletionRawFieldW918 leaves) :=
  rfl

/-- W918 direct calculus delegates to W917 after triangle-completion raw-field bundling. -/
theorem w918DirectCalculusRunsThroughW917W1386
    (leaves :
      MetrizableWppClosedMapTriangleCompletionRawFieldBoundaryRawFieldLeavesW918) :
    directBoundedLeftCalculusOfClosedMapTriangleCompletionRawFieldBoundaryRawFieldsW918
        leaves =
      directBoundedLeftCalculusOfClosedMapBoundaryRawFieldsW917
        (w917LeavesOfTriangleCompletionRawFieldW918 leaves) :=
  rfl

/-- W918 stable package delegates to W917 after triangle-completion raw-field bundling. -/
theorem w918StablePackageRunsThroughW917W1386
    (leaves :
      MetrizableWppClosedMapTriangleCompletionRawFieldBoundaryRawFieldLeavesW918) :
    boundedDerivedInfinityCategoryOfClosedMapTriangleCompletionRawFieldBoundaryRawFieldsW918
        leaves =
      boundedDerivedInfinityCategoryOfClosedMapBoundaryRawFieldsW917
        (w917LeavesOfTriangleCompletionRawFieldW918 leaves) :=
  rfl

/-- W919 concrete leaves delegate to W918 after source raw-field bundling. -/
theorem w919ConcreteLeavesRunThroughW918W1386
    (leaves : MetrizableWppClosedMapSourceRawFieldLeavesW919) :
    concreteLeavesOfClosedMapSourceRawFieldsW919 leaves =
      concreteLeavesOfClosedMapTriangleCompletionRawFieldBoundaryRawFieldsW918
        (w918LeavesOfSourceRawFieldsW919 leaves) :=
  rfl

/-- W919 route data delegates to W918 after source raw-field bundling. -/
theorem w919RouteDataProviderRunsThroughW918W1386
    (leaves : MetrizableWppClosedMapSourceRawFieldLeavesW919) :
    routeDataProviderOfClosedMapSourceRawFieldsW919 leaves =
      routeDataProviderOfClosedMapTriangleCompletionRawFieldBoundaryRawFieldsW918
        (w918LeavesOfSourceRawFieldsW919 leaves) :=
  rfl

/-- W919 direct calculus delegates to W918 after source raw-field bundling. -/
theorem w919DirectCalculusRunsThroughW918W1386
    (leaves : MetrizableWppClosedMapSourceRawFieldLeavesW919) :
    directBoundedLeftCalculusOfClosedMapSourceRawFieldsW919 leaves =
      directBoundedLeftCalculusOfClosedMapTriangleCompletionRawFieldBoundaryRawFieldsW918
        (w918LeavesOfSourceRawFieldsW919 leaves) :=
  rfl

/-- W919 stable package delegates to W918 after source raw-field bundling. -/
theorem w919StablePackageRunsThroughW918W1386
    (leaves : MetrizableWppClosedMapSourceRawFieldLeavesW919) :
    boundedDerivedInfinityCategoryOfClosedMapSourceRawFieldsW919 leaves =
      boundedDerivedInfinityCategoryOfClosedMapTriangleCompletionRawFieldBoundaryRawFieldsW918
        (w918LeavesOfSourceRawFieldsW919 leaves) :=
  rfl

/-- W920 concrete leaves delegate to W919 after primitive relation-field bundling. -/
theorem w920ConcreteLeavesRunThroughW919W1386
    (leaves : MetrizableWppClosedMapRelationPrimitiveFieldLeavesW920) :
    concreteLeavesOfClosedMapRelationPrimitiveFieldsW920 leaves =
      concreteLeavesOfClosedMapSourceRawFieldsW919
        (w919LeavesOfRelationPrimitiveFieldsW920 leaves) :=
  rfl

/-- W920 route data delegates to W919 after primitive relation-field bundling. -/
theorem w920RouteDataProviderRunsThroughW919W1386
    (leaves : MetrizableWppClosedMapRelationPrimitiveFieldLeavesW920) :
    routeDataProviderOfClosedMapRelationPrimitiveFieldsW920 leaves =
      routeDataProviderOfClosedMapSourceRawFieldsW919
        (w919LeavesOfRelationPrimitiveFieldsW920 leaves) :=
  rfl

/-- W920 direct calculus delegates to W919 after primitive relation-field bundling. -/
theorem w920DirectCalculusRunsThroughW919W1386
    (leaves : MetrizableWppClosedMapRelationPrimitiveFieldLeavesW920) :
    directBoundedLeftCalculusOfClosedMapRelationPrimitiveFieldsW920 leaves =
      directBoundedLeftCalculusOfClosedMapSourceRawFieldsW919
        (w919LeavesOfRelationPrimitiveFieldsW920 leaves) :=
  rfl

/-- W920 stable package delegates to W919 after primitive relation-field bundling. -/
theorem w920StablePackageRunsThroughW919W1386
    (leaves : MetrizableWppClosedMapRelationPrimitiveFieldLeavesW920) :
    boundedDerivedInfinityCategoryOfClosedMapRelationPrimitiveFieldsW920
        leaves =
      boundedDerivedInfinityCategoryOfClosedMapSourceRawFieldsW919
        (w919LeavesOfRelationPrimitiveFieldsW920 leaves) :=
  rfl

/-- W1386 keeps W914-W920 input counts visible. -/
theorem w1386ClosedMapW914ToW920InputCounts :
    closedMapSelectedDifferenceFieldsInputNamesW914.length = 39 ∧
      closedMapTargetRawFieldsInputNamesW915.length = 39 ∧
      closedMapRelationRawFieldsInputNamesW916.length = 39 ∧
      closedMapBoundaryRawFieldsInputNamesW917.length = 39 ∧
      closedMapTriangleCompletionRawFieldBoundaryRawFieldsInputNamesW918.length =
        39 ∧
      closedMapSourceRawFieldsInputNamesW919.length = 39 ∧
      closedMapRelationPrimitiveFieldsInputNamesW920.length = 39 :=
  ⟨closedMapSelectedDifferenceFieldsInputNamesW914_count,
    closedMapTargetRawFieldsInputNamesW915_count,
    closedMapRelationRawFieldsInputNamesW916_count,
    closedMapBoundaryRawFieldsInputNamesW917_count,
    closedMapTriangleCompletionRawFieldBoundaryRawFieldsInputNamesW918_count,
    closedMapSourceRawFieldsInputNamesW919_count,
    closedMapRelationPrimitiveFieldsInputNamesW920_count⟩

/-- Current W1386 nonterminal state. -/
structure ClosedMapRawPrimitiveStableConvergenceStateW1386 :
    Type where
  seed : String
  declarations : List String
  selectedDifferenceResult : String
  targetRawResult : String
  relationRawResult : String
  boundaryRawResult : String
  triangleCompletionRawResult : String
  sourceRawResult : String
  relationPrimitiveResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1386 records W914-W920 convergence into the closed-map stable route. -/
def currentClosedMapRawPrimitiveStableConvergenceStateW1386 :
    ClosedMapRawPrimitiveStableConvergenceStateW1386 where
  seed := "w1386-closed-map-raw-primitive-stable-convergence"
  declarations :=
    ["w914ConcreteLeavesRunThroughW913W1386",
      "w914RouteDataProviderRunsThroughW913W1386",
      "w914DirectCalculusRunsThroughW913W1386",
      "w914StablePackageRunsThroughW913W1386",
      "w915ConcreteLeavesRunThroughW914W1386",
      "w915RouteDataProviderRunsThroughW914W1386",
      "w915DirectCalculusRunsThroughW914W1386",
      "w915StablePackageRunsThroughW914W1386",
      "w916ConcreteLeavesRunThroughW915W1386",
      "w916RouteDataProviderRunsThroughW915W1386",
      "w916DirectCalculusRunsThroughW915W1386",
      "w916StablePackageRunsThroughW915W1386",
      "w917ConcreteLeavesRunThroughW916W1386",
      "w917RouteDataProviderRunsThroughW916W1386",
      "w917DirectCalculusRunsThroughW916W1386",
      "w917StablePackageRunsThroughW916W1386",
      "w918ConcreteLeavesRunThroughW917W1386",
      "w918RouteDataProviderRunsThroughW917W1386",
      "w918DirectCalculusRunsThroughW917W1386",
      "w918StablePackageRunsThroughW917W1386",
      "w919ConcreteLeavesRunThroughW918W1386",
      "w919RouteDataProviderRunsThroughW918W1386",
      "w919DirectCalculusRunsThroughW918W1386",
      "w919StablePackageRunsThroughW918W1386",
      "w920ConcreteLeavesRunThroughW919W1386",
      "w920RouteDataProviderRunsThroughW919W1386",
      "w920DirectCalculusRunsThroughW919W1386",
      "w920StablePackageRunsThroughW919W1386",
      "w1386ClosedMapW914ToW920InputCounts"]
  selectedDifferenceResult :=
    "proved: W914 selected-difference raw fields delegate into W913"
  targetRawResult :=
    "proved: W915 target raw fields delegate into W914"
  relationRawResult :=
    "proved: W916 relation raw fields delegate into W915"
  boundaryRawResult :=
    "proved: W917 boundary raw fields delegate into W916"
  triangleCompletionRawResult :=
    "proved: W918 triangle-completion raw field delegates into W917"
  sourceRawResult :=
    "proved: W919 source raw fields delegate into W918"
  relationPrimitiveResult :=
    "proved: W920 primitive relation fields delegate into W919"
  remainingInputs :=
    closedMapRelationPrimitiveFieldsInputNamesW920
  productSuccessClaimed := false

theorem currentW1386ClosedMapRawPrimitiveStableConvergence_productSuccess :
    currentClosedMapRawPrimitiveStableConvergenceStateW1386.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
