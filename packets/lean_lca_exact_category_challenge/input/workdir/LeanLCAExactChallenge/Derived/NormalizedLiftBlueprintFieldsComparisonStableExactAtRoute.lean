import LeanLCAExactChallenge.Derived.NormalizedFixedTargetFieldsComparisonStableExactAtRoute

/-!
W889 feeds the W888 normalized-fixed-target-fields comparison stable-ExactAt
route from explicit normalized strict-representative lift blueprint fields.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/--
W889 replaces the bundled normalized strict-representative lift blueprint by
its explicit blueprint, object-normalization, and map-normalization fields.
-/
structure MetrizableWppNormalizedLiftBlueprintFieldLeavesW889 :
    Type 2 where
  boundaryData :
    MetrizableWppLimitBoundaryDataW716
  relationData :
    ClosedNatTransOrdinaryRelationDataProviderW717
  targetSurjectiveCompactForTargetProvider :
    TargetSurjectiveCompactForTargetProviderW715
  diagramAndMappedCokernelClosednessData :
    MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725
  strictRepresentativeLiftBlueprint :
    Dbounded.MetrizableWalkingParallelPairLiftBlueprint
  sourceImageObjectNormalization :
    ∀ (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}),
      (strictRepresentativeLiftBlueprint.objData
        (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.obj X)).diagram = X
  sourceImageMapNormalization :
    ∀ {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}} (τ : X ⟶ Y),
      (strictRepresentativeLiftBlueprint.mapData
          (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.map τ)).natTrans ≫
        eqToHom (sourceImageObjectNormalization Y) =
      eqToHom (sourceImageObjectNormalization X) ≫ τ
  targetFixedTargetUniq :
    Dbounded.MetrizableWalkingParallelPairFixedTargetUniqObligation
      (WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0})
  localizationModelFixedTargetUniq :
    Dbounded.MetrizableWalkingParallelPairFixedTargetUniqObligation
      (((boundedExactWeakEquivalence MetrizableLCA.{0}).functorCategory
        WalkingParallelPair).Localization)
  sourcePretriangulated :
    letI : ∀ n : ℤ,
        (shiftFunctor (BoundedComplexCategory MetrizableLCA.{0}) n).Additive :=
      inferInstance
    Pretriangulated (BoundedComplexCategory MetrizableLCA.{0})
  sourceTriangulated :
    letI : ∀ n : ℤ,
        (shiftFunctor (BoundedComplexCategory MetrizableLCA.{0}) n).Additive :=
      inferInstance
    letI : Pretriangulated (BoundedComplexCategory MetrizableLCA.{0}) :=
      sourcePretriangulated
    IsTriangulated (BoundedComplexCategory MetrizableLCA.{0})
  triangleCompletion :
    letI : ∀ n : ℤ,
        (shiftFunctor (BoundedComplexCategory MetrizableLCA.{0}) n).Additive :=
      inferInstance
    letI : Pretriangulated (BoundedComplexCategory MetrizableLCA.{0}) :=
      sourcePretriangulated
    MetrizableBoundedExactWeakEquivalenceTriangleCompletionInputW654
  endpointForgetPreservesHomology :
    (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).PreservesHomology
  endpointClosedEmbedding :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      Topology.IsClosedEmbedding ((K.sc i).f : (K.sc i).X₁ → (K.sc i).X₂)
  endpointOpenMap :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      IsOpenMap ((K.sc i).g : (K.sc i).X₂ → (K.sc i).X₃)
  endpointEpiOfExactAt :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      K.ExactAt i → Epi ((K.sc i).g)
  boundedHomotopyLocalizedRightAdjoint :
    MorphismProperty.Localization
        ((exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).trW) ⥤
      BoundedComplexCategory MetrizableLCA.{0}
  boundedHomotopyLocalizedAdjunction :
    boundedHomotopyLocalizedVerdierFunctor MetrizableLCA.{0} ⊣
      boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedUnitMem :
    (boundedHomotopyExactWeakEquivalence MetrizableLCA.{0}).functorCategory
      (BoundedComplexCategory MetrizableLCA.{0})
      boundedHomotopyLocalizedAdjunction.unit

/-- W889 assembles the normalized lift blueprint from explicit fields. -/
def normalizedLiftBlueprintOfFieldsW889
    (leaves : MetrizableWppNormalizedLiftBlueprintFieldLeavesW889) :
    Dbounded.MetrizableWalkingParallelPairNormalizedLiftBlueprint
    where
  blueprint := leaves.strictRepresentativeLiftBlueprint
  obj_image := leaves.sourceImageObjectNormalization
  map_image := leaves.sourceImageMapNormalization

/-- W889 assembles the W888 leaves from normalized-lift blueprint fields. -/
def normalizedFixedTargetFieldLeavesOfNormalizedLiftBlueprintFieldsW889
    (leaves : MetrizableWppNormalizedLiftBlueprintFieldLeavesW889) :
    MetrizableWppNormalizedFixedTargetFieldLeavesW888
    where
  boundaryData := leaves.boundaryData
  relationData := leaves.relationData
  targetSurjectiveCompactForTargetProvider :=
    leaves.targetSurjectiveCompactForTargetProvider
  diagramAndMappedCokernelClosednessData :=
    leaves.diagramAndMappedCokernelClosednessData
  normalizedLiftBlueprint :=
    normalizedLiftBlueprintOfFieldsW889 leaves
  targetFixedTargetUniq := leaves.targetFixedTargetUniq
  localizationModelFixedTargetUniq :=
    leaves.localizationModelFixedTargetUniq
  sourcePretriangulated := leaves.sourcePretriangulated
  sourceTriangulated := leaves.sourceTriangulated
  triangleCompletion := leaves.triangleCompletion
  endpointForgetPreservesHomology :=
    leaves.endpointForgetPreservesHomology
  endpointClosedEmbedding := leaves.endpointClosedEmbedding
  endpointOpenMap := leaves.endpointOpenMap
  endpointEpiOfExactAt := leaves.endpointEpiOfExactAt
  boundedHomotopyLocalizedRightAdjoint :=
    leaves.boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedAdjunction :=
    leaves.boundedHomotopyLocalizedAdjunction
  boundedHomotopyLocalizedUnitMem :=
    leaves.boundedHomotopyLocalizedUnitMem

/-- W889 W733 concrete leaves from explicit normalized-lift blueprint fields. -/
def concreteLeavesOfNormalizedLiftBlueprintFieldsComparisonW889
    (leaves : MetrizableWppNormalizedLiftBlueprintFieldLeavesW889) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfNormalizedFixedTargetFieldsComparisonW888
    (normalizedFixedTargetFieldLeavesOfNormalizedLiftBlueprintFieldsW889 leaves)

/-- W889 W732 route data from explicit normalized-lift blueprint fields. -/
def routeDataProviderOfNormalizedLiftBlueprintFieldsComparisonW889
    (leaves : MetrizableWppNormalizedLiftBlueprintFieldLeavesW889) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfNormalizedFixedTargetFieldsComparisonW888
    (normalizedFixedTargetFieldLeavesOfNormalizedLiftBlueprintFieldsW889 leaves)

/--
W889 direct bounded left calculus through the latest W888 comparison stable
ExactAt route.
-/
theorem directBoundedLeftCalculusOfNormalizedLiftBlueprintFieldsComparisonStableExactAtW889
    (leaves : MetrizableWppNormalizedLiftBlueprintFieldLeavesW889) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfNormalizedFixedTargetFieldsComparisonStableExactAtW888
    (normalizedFixedTargetFieldLeavesOfNormalizedLiftBlueprintFieldsW889 leaves)

/--
W889 bounded derived infinity-category package through the latest W888
comparison stable ExactAt route.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfNormalizedLiftBlueprintFieldsComparisonStableExactAtW889
    (leaves : MetrizableWppNormalizedLiftBlueprintFieldLeavesW889) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfNormalizedFixedTargetFieldsComparisonStableExactAtW888
    (normalizedFixedTargetFieldLeavesOfNormalizedLiftBlueprintFieldsW889 leaves)

/-- W889 exposes normalized-lift blueprint fields needed by W888. -/
def normalizedLiftBlueprintFieldsComparisonStableExactAtInputNamesW889 :
    List String :=
  ["bundled WPP right-open quotient-cover and source-pi-zero boundary data",
    "bundled closed natural transformation relation data",
    "target-only target-difference surjectivity plus target-codomain compactness provider",
    "matched selected-difference component and W519 mapped-cokernel closedness branch provider",
    "coherent strict representatives for WalkingParallelPair diagrams and maps",
    "source-image object normalization for the strict-representative lift",
    "source-image map normalization for the strict-representative lift",
    "target fixed-target uniqueness obligation",
    "localization-model fixed-target uniqueness obligation",
    "Pretriangulated structure on BoundedComplexCategory MetrizableLCA",
    "IsTriangulated structure on BoundedComplexCategory MetrizableLCA",
    "bounded exact weak equivalence source-side triangle-completion data",
    "forgetful functor preserves homology for MetrizableLCA",
    "endpoint ExactAt incoming maps are closed embeddings",
    "endpoint ExactAt outgoing maps are open",
    "endpoint ExactAt outgoing maps are epis",
    "right adjoint to the bounded homotopy localized Verdier functor",
    "adjunction for the bounded homotopy localized Verdier functor",
    "unit membership in boundedHomotopyExactWeakEquivalence"]

theorem normalizedLiftBlueprintFieldsComparisonStableExactAtInputNamesW889_count :
    normalizedLiftBlueprintFieldsComparisonStableExactAtInputNamesW889.length =
      19 :=
  rfl

/-- Current checked W889 state. -/
structure MetrizableNormalizedLiftBlueprintFieldsComparisonStableExactAtRouteStateW889 :
    Type where
  seed : String
  declarations : List String
  normalizedLiftBlueprintAssemblyResult : String
  exactAtResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableNormalizedLiftBlueprintFieldsComparisonStableExactAtRouteStateW889 :
    MetrizableNormalizedLiftBlueprintFieldsComparisonStableExactAtRouteStateW889
    where
  seed :=
    "w889-normalized-lift-blueprint-fields-comparison-stable-exact-at"
  declarations :=
    ["MetrizableWppNormalizedLiftBlueprintFieldLeavesW889",
      "normalizedLiftBlueprintOfFieldsW889",
      "normalizedFixedTargetFieldLeavesOfNormalizedLiftBlueprintFieldsW889",
      "concreteLeavesOfNormalizedLiftBlueprintFieldsComparisonW889",
      "routeDataProviderOfNormalizedLiftBlueprintFieldsComparisonW889",
      "directBoundedLeftCalculusOfNormalizedLiftBlueprintFieldsComparisonStableExactAtW889",
      "boundedDerivedInfinityCategoryOfNormalizedLiftBlueprintFieldsComparisonStableExactAtW889",
      "normalizedLiftBlueprintFieldsComparisonStableExactAtInputNamesW889",
      "normalizedLiftBlueprintFieldsComparisonStableExactAtInputNamesW889_count"]
  normalizedLiftBlueprintAssemblyResult :=
    "proved: explicit normalized-lift blueprint fields assemble the normalized\
      strict-representative blueprint consumed by W888"
  exactAtResult :=
    "proved: explicit normalized-lift blueprint fields feed the W888 stable\
      ExactAt route"
  replacedInputs :=
    ["normalized strict-representative lift blueprint"]
  remainingInputs :=
    normalizedLiftBlueprintFieldsComparisonStableExactAtInputNamesW889
  productSuccessClaimed := false

theorem currentW889NormalizedLiftBlueprintFieldsComparisonStableExactAtRoute_productSuccess :
    (let state :=
        currentMetrizableNormalizedLiftBlueprintFieldsComparisonStableExactAtRouteStateW889;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
