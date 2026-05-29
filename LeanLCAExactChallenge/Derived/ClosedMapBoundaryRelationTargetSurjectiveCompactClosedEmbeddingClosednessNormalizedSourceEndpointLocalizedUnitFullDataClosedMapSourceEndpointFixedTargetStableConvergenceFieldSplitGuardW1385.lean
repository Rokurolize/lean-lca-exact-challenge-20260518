import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosedMapTargetComponentRelationFieldsStableConvergenceFieldSplitGuardW1384
import LeanLCAExactChallenge.Derived.ClosedMapFixedTargetUniqFieldsLocalizedRightAdjointFieldsRoute

/-!
W1385 records the definitional convergence of the closed-map W909-W913 route
chain, bundling target fields, source fields, endpoint fields,
localized-right-adjoint fields, and fixed-target uniqueness fields.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W909 packages target surjectivity and compactness fields as the W715 target provider. -/
theorem w909TargetDataRunsThroughFieldsW1385
    (targetDifferenceSurjectiveForTargetProvider :
      TargetDifferenceSurjectiveForTargetProviderW713)
    (targetCodomainCompactSpaceProvider :
      TargetCodomainCompactSpaceProviderW601) :
    targetDataOfFieldsW909 targetDifferenceSurjectiveForTargetProvider
        targetCodomainCompactSpaceProvider =
      fun Y =>
        ⟨targetDifferenceSurjectiveForTargetProvider Y,
          targetCodomainCompactSpaceProvider Y⟩ :=
  rfl

/-- W909 concrete leaves delegate to W908 after target-field bundling. -/
theorem w909ConcreteLeavesRunThroughW908W1385
    (leaves : MetrizableWppClosedMapTargetFieldLeavesW909) :
    concreteLeavesOfClosedMapTargetFieldsW909 leaves =
      concreteLeavesOfClosedMapRelationFieldsW908
        (w908LeavesOfTargetFieldsW909 leaves) :=
  rfl

/-- W909 route data delegates to W908 after target-field bundling. -/
theorem w909RouteDataProviderRunsThroughW908W1385
    (leaves : MetrizableWppClosedMapTargetFieldLeavesW909) :
    routeDataProviderOfClosedMapTargetFieldsW909 leaves =
      routeDataProviderOfClosedMapRelationFieldsW908
        (w908LeavesOfTargetFieldsW909 leaves) :=
  rfl

/-- W909 direct calculus delegates to W908 after target-field bundling. -/
theorem w909DirectCalculusRunsThroughW908W1385
    (leaves : MetrizableWppClosedMapTargetFieldLeavesW909) :
    directBoundedLeftCalculusOfClosedMapTargetFieldsW909 leaves =
      directBoundedLeftCalculusOfClosedMapRelationFieldsW908
        (w908LeavesOfTargetFieldsW909 leaves) :=
  rfl

/-- W909 stable package delegates to W908 after target-field bundling. -/
theorem w909StablePackageRunsThroughW908W1385
    (leaves : MetrizableWppClosedMapTargetFieldLeavesW909) :
    boundedDerivedInfinityCategoryOfClosedMapTargetFieldsW909 leaves =
      boundedDerivedInfinityCategoryOfClosedMapRelationFieldsW908
        (w908LeavesOfTargetFieldsW909 leaves) :=
  rfl

/-- W910 packages source triangulation fields as the W722 source provider. -/
theorem w910SourceTriangulationRunsThroughFieldsW1385
    (sourcePretriangulated :
      letI : ∀ n : ℤ,
          (shiftFunctor (BoundedComplexCategory MetrizableLCA.{0}) n).Additive :=
        inferInstance
      Pretriangulated (BoundedComplexCategory MetrizableLCA.{0}))
    (sourceTriangulated :
      letI : ∀ n : ℤ,
          (shiftFunctor (BoundedComplexCategory MetrizableLCA.{0}) n).Additive :=
        inferInstance
      letI : Pretriangulated (BoundedComplexCategory MetrizableLCA.{0}) :=
        sourcePretriangulated
      IsTriangulated (BoundedComplexCategory MetrizableLCA.{0}))
    (triangleCompletion :
      letI : ∀ n : ℤ,
          (shiftFunctor (BoundedComplexCategory MetrizableLCA.{0}) n).Additive :=
        inferInstance
      letI : Pretriangulated (BoundedComplexCategory MetrizableLCA.{0}) :=
        sourcePretriangulated
      MetrizableBoundedExactWeakEquivalenceTriangleCompletionInputW654) :
    sourceTriangulationDataOfFieldsW910 sourcePretriangulated
        sourceTriangulated triangleCompletion =
      { sourcePretriangulated := sourcePretriangulated
        sourceTriangulated := sourceTriangulated
        triangleCompletion := triangleCompletion } :=
  rfl

/-- W910 concrete leaves delegate to W909 after source-field bundling. -/
theorem w910ConcreteLeavesRunThroughW909W1385
    (leaves : MetrizableWppClosedMapSourceFieldLeavesW910) :
    concreteLeavesOfClosedMapSourceFieldsW910 leaves =
      concreteLeavesOfClosedMapTargetFieldsW909
        (w909LeavesOfSourceFieldsW910 leaves) :=
  rfl

/-- W910 route data delegates to W909 after source-field bundling. -/
theorem w910RouteDataProviderRunsThroughW909W1385
    (leaves : MetrizableWppClosedMapSourceFieldLeavesW910) :
    routeDataProviderOfClosedMapSourceFieldsW910 leaves =
      routeDataProviderOfClosedMapTargetFieldsW909
        (w909LeavesOfSourceFieldsW910 leaves) :=
  rfl

/-- W910 direct calculus delegates to W909 after source-field bundling. -/
theorem w910DirectCalculusRunsThroughW909W1385
    (leaves : MetrizableWppClosedMapSourceFieldLeavesW910) :
    directBoundedLeftCalculusOfClosedMapSourceFieldsW910 leaves =
      directBoundedLeftCalculusOfClosedMapTargetFieldsW909
        (w909LeavesOfSourceFieldsW910 leaves) :=
  rfl

/-- W910 stable package delegates to W909 after source-field bundling. -/
theorem w910StablePackageRunsThroughW909W1385
    (leaves : MetrizableWppClosedMapSourceFieldLeavesW910) :
    boundedDerivedInfinityCategoryOfClosedMapSourceFieldsW910 leaves =
      boundedDerivedInfinityCategoryOfClosedMapTargetFieldsW909
        (w909LeavesOfSourceFieldsW910 leaves) :=
  rfl

/-- W911 packages endpoint topology fields as the W856 endpoint-facts provider. -/
theorem w911EndpointTopologyRunsThroughFieldsW1385
    (endpointClosedEmbedding :
      ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
        Topology.IsClosedEmbedding ((K.sc i).f : (K.sc i).X₁ → (K.sc i).X₂))
    (endpointOpenMap :
      ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
        IsOpenMap ((K.sc i).g : (K.sc i).X₂ → (K.sc i).X₃))
    (endpointEpiOfExactAt :
      ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
        K.ExactAt i → Epi ((K.sc i).g)) :
    endpointTopologyFactsOfFieldsW911 endpointClosedEmbedding
        endpointOpenMap endpointEpiOfExactAt =
      { endpointClosedEmbedding := endpointClosedEmbedding
        endpointOpenMap := endpointOpenMap
        endpointEpiOfExactAt := endpointEpiOfExactAt } :=
  rfl

/-- W911 concrete leaves delegate to W910 after endpoint-field bundling. -/
theorem w911ConcreteLeavesRunThroughW910W1385
    (leaves : MetrizableWppClosedMapEndpointFieldLeavesW911) :
    concreteLeavesOfClosedMapEndpointFieldsW911 leaves =
      concreteLeavesOfClosedMapSourceFieldsW910
        (w910LeavesOfEndpointFieldsW911 leaves) :=
  rfl

/-- W911 route data delegates to W910 after endpoint-field bundling. -/
theorem w911RouteDataProviderRunsThroughW910W1385
    (leaves : MetrizableWppClosedMapEndpointFieldLeavesW911) :
    routeDataProviderOfClosedMapEndpointFieldsW911 leaves =
      routeDataProviderOfClosedMapSourceFieldsW910
        (w910LeavesOfEndpointFieldsW911 leaves) :=
  rfl

/-- W911 direct calculus delegates to W910 after endpoint-field bundling. -/
theorem w911DirectCalculusRunsThroughW910W1385
    (leaves : MetrizableWppClosedMapEndpointFieldLeavesW911) :
    directBoundedLeftCalculusOfClosedMapEndpointFieldsW911 leaves =
      directBoundedLeftCalculusOfClosedMapSourceFieldsW910
        (w910LeavesOfEndpointFieldsW911 leaves) :=
  rfl

/-- W911 stable package delegates to W910 after endpoint-field bundling. -/
theorem w911StablePackageRunsThroughW910W1385
    (leaves : MetrizableWppClosedMapEndpointFieldLeavesW911) :
    boundedDerivedInfinityCategoryOfClosedMapEndpointFieldsW911 leaves =
      boundedDerivedInfinityCategoryOfClosedMapSourceFieldsW910
        (w910LeavesOfEndpointFieldsW911 leaves) :=
  rfl

/-- W912 concrete leaves delegate to W911 after localized-right-adjoint bundling. -/
theorem w912ConcreteLeavesRunThroughW911W1385
    (leaves : MetrizableWppClosedMapLocalizedRightAdjointFieldLeavesW912) :
    concreteLeavesOfClosedMapLocalizedRightAdjointFieldsW912 leaves =
      concreteLeavesOfClosedMapEndpointFieldsW911
        (w911LeavesOfLocalizedRightAdjointFieldsW912 leaves) :=
  rfl

/-- W912 route data delegates to W911 after localized-right-adjoint bundling. -/
theorem w912RouteDataProviderRunsThroughW911W1385
    (leaves : MetrizableWppClosedMapLocalizedRightAdjointFieldLeavesW912) :
    routeDataProviderOfClosedMapLocalizedRightAdjointFieldsW912 leaves =
      routeDataProviderOfClosedMapEndpointFieldsW911
        (w911LeavesOfLocalizedRightAdjointFieldsW912 leaves) :=
  rfl

/-- W912 direct calculus delegates to W911 after localized-right-adjoint bundling. -/
theorem w912DirectCalculusRunsThroughW911W1385
    (leaves : MetrizableWppClosedMapLocalizedRightAdjointFieldLeavesW912) :
    directBoundedLeftCalculusOfClosedMapLocalizedRightAdjointFieldsW912 leaves =
      directBoundedLeftCalculusOfClosedMapEndpointFieldsW911
        (w911LeavesOfLocalizedRightAdjointFieldsW912 leaves) :=
  rfl

/-- W912 stable package delegates to W911 after localized-right-adjoint bundling. -/
theorem w912StablePackageRunsThroughW911W1385
    (leaves : MetrizableWppClosedMapLocalizedRightAdjointFieldLeavesW912) :
    boundedDerivedInfinityCategoryOfClosedMapLocalizedRightAdjointFieldsW912
        leaves =
      boundedDerivedInfinityCategoryOfClosedMapEndpointFieldsW911
        (w911LeavesOfLocalizedRightAdjointFieldsW912 leaves) :=
  rfl

/-- W913 target fixed-target uniqueness is the raw quantifier field. -/
theorem w913TargetFixedTargetUniqRunsThroughFieldW1385
    (targetFixedTargetUniq :
      ∀ (F₁ F₂ :
          (WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) ⥤
            (WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0})),
        Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor ⋙ F₁ =
          Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor ⋙ F₂ →
        F₁ = F₂) :
    targetFixedTargetUniqOfFieldW913 targetFixedTargetUniq =
      targetFixedTargetUniq :=
  rfl

/-- W913 concrete leaves delegate to W912 after fixed-target uniqueness bundling. -/
theorem w913ConcreteLeavesRunThroughW912W1385
    (leaves : MetrizableWppClosedMapFixedTargetUniqFieldLeavesW913) :
    concreteLeavesOfClosedMapFixedTargetUniqFieldsW913 leaves =
      concreteLeavesOfClosedMapLocalizedRightAdjointFieldsW912
        (w912LeavesOfFixedTargetUniqFieldsW913 leaves) :=
  rfl

/-- W913 route data delegates to W912 after fixed-target uniqueness bundling. -/
theorem w913RouteDataProviderRunsThroughW912W1385
    (leaves : MetrizableWppClosedMapFixedTargetUniqFieldLeavesW913) :
    routeDataProviderOfClosedMapFixedTargetUniqFieldsW913 leaves =
      routeDataProviderOfClosedMapLocalizedRightAdjointFieldsW912
        (w912LeavesOfFixedTargetUniqFieldsW913 leaves) :=
  rfl

/-- W913 direct calculus delegates to W912 after fixed-target uniqueness bundling. -/
theorem w913DirectCalculusRunsThroughW912W1385
    (leaves : MetrizableWppClosedMapFixedTargetUniqFieldLeavesW913) :
    directBoundedLeftCalculusOfClosedMapFixedTargetUniqFieldsW913 leaves =
      directBoundedLeftCalculusOfClosedMapLocalizedRightAdjointFieldsW912
        (w912LeavesOfFixedTargetUniqFieldsW913 leaves) :=
  rfl

/-- W913 stable package delegates to W912 after fixed-target uniqueness bundling. -/
theorem w913StablePackageRunsThroughW912W1385
    (leaves : MetrizableWppClosedMapFixedTargetUniqFieldLeavesW913) :
    boundedDerivedInfinityCategoryOfClosedMapFixedTargetUniqFieldsW913 leaves =
      boundedDerivedInfinityCategoryOfClosedMapLocalizedRightAdjointFieldsW912
        (w912LeavesOfFixedTargetUniqFieldsW913 leaves) :=
  rfl

/-- W1385 keeps W909-W913 input counts visible. -/
theorem w1385ClosedMapW909ToW913InputCounts :
    closedMapTargetFieldsInputNamesW909.length = 33 ∧
      closedMapSourceFieldsInputNamesW910.length = 35 ∧
      closedMapEndpointFieldsInputNamesW911.length = 37 ∧
      closedMapLocalizedRightAdjointFieldsInputNamesW912.length = 39 ∧
      closedMapFixedTargetUniqFieldsInputNamesW913.length = 39 :=
  ⟨closedMapTargetFieldsInputNamesW909_count,
    closedMapSourceFieldsInputNamesW910_count,
    closedMapEndpointFieldsInputNamesW911_count,
    closedMapLocalizedRightAdjointFieldsInputNamesW912_count,
    closedMapFixedTargetUniqFieldsInputNamesW913_count⟩

/-- Current W1385 nonterminal state. -/
structure ClosedMapSourceEndpointFixedTargetStableConvergenceStateW1385 :
    Type where
  seed : String
  declarations : List String
  targetFieldResult : String
  sourceFieldResult : String
  endpointFieldResult : String
  localizedRightAdjointFieldResult : String
  fixedTargetUniqFieldResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1385 records W909-W913 convergence into the closed-map stable route. -/
def currentClosedMapSourceEndpointFixedTargetStableConvergenceStateW1385 :
    ClosedMapSourceEndpointFixedTargetStableConvergenceStateW1385 where
  seed := "w1385-closed-map-source-endpoint-fixed-target-stable-convergence"
  declarations :=
    ["w909TargetDataRunsThroughFieldsW1385",
      "w909ConcreteLeavesRunThroughW908W1385",
      "w909RouteDataProviderRunsThroughW908W1385",
      "w909DirectCalculusRunsThroughW908W1385",
      "w909StablePackageRunsThroughW908W1385",
      "w910SourceTriangulationRunsThroughFieldsW1385",
      "w910ConcreteLeavesRunThroughW909W1385",
      "w910RouteDataProviderRunsThroughW909W1385",
      "w910DirectCalculusRunsThroughW909W1385",
      "w910StablePackageRunsThroughW909W1385",
      "w911EndpointTopologyRunsThroughFieldsW1385",
      "w911ConcreteLeavesRunThroughW910W1385",
      "w911RouteDataProviderRunsThroughW910W1385",
      "w911DirectCalculusRunsThroughW910W1385",
      "w911StablePackageRunsThroughW910W1385",
      "w912ConcreteLeavesRunThroughW911W1385",
      "w912RouteDataProviderRunsThroughW911W1385",
      "w912DirectCalculusRunsThroughW911W1385",
      "w912StablePackageRunsThroughW911W1385",
      "w913TargetFixedTargetUniqRunsThroughFieldW1385",
      "w913ConcreteLeavesRunThroughW912W1385",
      "w913RouteDataProviderRunsThroughW912W1385",
      "w913DirectCalculusRunsThroughW912W1385",
      "w913StablePackageRunsThroughW912W1385",
      "w1385ClosedMapW909ToW913InputCounts"]
  targetFieldResult := "proved: W909 bundles target fields into W908"
  sourceFieldResult := "proved: W910 bundles source fields into W909"
  endpointFieldResult := "proved: W911 bundles endpoint fields into W910"
  localizedRightAdjointFieldResult :=
    "proved: W912 bundles localized-right-adjoint fields into W911"
  fixedTargetUniqFieldResult :=
    "proved: W913 bundles fixed-target uniqueness fields into W912"
  remainingInputs :=
    closedMapFixedTargetUniqFieldsInputNamesW913
  productSuccessClaimed := false

theorem currentW1385ClosedMapSourceEndpointFixedTargetStableConvergence_productSuccess :
    currentClosedMapSourceEndpointFixedTargetStableConvergenceStateW1385.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
