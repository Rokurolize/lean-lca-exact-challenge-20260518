import LeanLCAExactChallenge.Derived.LocalizedRightAdjointFieldsComparisonStableExactAtRoute

/-!
W888 feeds the W887 localized-right-adjoint-fields comparison stable-ExactAt
route from explicit normalized fixed-target fields.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/--
W888 replaces the bundled W719 normalized fixed-target data provider by its
three explicit fields.
-/
structure MetrizableWppNormalizedFixedTargetFieldLeavesW888 :
    Type 2 where
  boundaryData :
    MetrizableWppLimitBoundaryDataW716
  relationData :
    ClosedNatTransOrdinaryRelationDataProviderW717
  targetSurjectiveCompactForTargetProvider :
    TargetSurjectiveCompactForTargetProviderW715
  diagramAndMappedCokernelClosednessData :
    MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725
  normalizedLiftBlueprint :
    Dbounded.MetrizableWalkingParallelPairNormalizedLiftBlueprint
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

/-- W888 assembles the W719 normalized fixed-target provider from fields. -/
def normalizedFixedTargetDataOfFieldsW888
    (leaves : MetrizableWppNormalizedFixedTargetFieldLeavesW888) :
    MetrizableWppNormalizedFixedTargetDataProviderW719
    where
  normalizedLiftBlueprint := leaves.normalizedLiftBlueprint
  targetFixedTargetUniq := leaves.targetFixedTargetUniq
  localizationModelFixedTargetUniq :=
    leaves.localizationModelFixedTargetUniq

/-- W888 assembles the W887 leaves from explicit normalized fixed-target fields. -/
def localizedRightAdjointFieldLeavesOfNormalizedFixedTargetFieldsW888
    (leaves : MetrizableWppNormalizedFixedTargetFieldLeavesW888) :
    MetrizableWppLocalizedRightAdjointFieldLeavesW887
    where
  boundaryData := leaves.boundaryData
  relationData := leaves.relationData
  targetSurjectiveCompactForTargetProvider :=
    leaves.targetSurjectiveCompactForTargetProvider
  diagramAndMappedCokernelClosednessData :=
    leaves.diagramAndMappedCokernelClosednessData
  normalizedFixedTargetData :=
    normalizedFixedTargetDataOfFieldsW888 leaves
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

/-- W888 W733 concrete leaves from explicit normalized fixed-target fields. -/
def concreteLeavesOfNormalizedFixedTargetFieldsComparisonW888
    (leaves : MetrizableWppNormalizedFixedTargetFieldLeavesW888) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfLocalizedRightAdjointFieldsComparisonW887
    (localizedRightAdjointFieldLeavesOfNormalizedFixedTargetFieldsW888 leaves)

/-- W888 W732 route data from explicit normalized fixed-target fields. -/
def routeDataProviderOfNormalizedFixedTargetFieldsComparisonW888
    (leaves : MetrizableWppNormalizedFixedTargetFieldLeavesW888) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfLocalizedRightAdjointFieldsComparisonW887
    (localizedRightAdjointFieldLeavesOfNormalizedFixedTargetFieldsW888 leaves)

/--
W888 direct bounded left calculus through the latest W887 comparison stable
ExactAt route.
-/
theorem directBoundedLeftCalculusOfNormalizedFixedTargetFieldsComparisonStableExactAtW888
    (leaves : MetrizableWppNormalizedFixedTargetFieldLeavesW888) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfLocalizedRightAdjointFieldsComparisonStableExactAtW887
    (localizedRightAdjointFieldLeavesOfNormalizedFixedTargetFieldsW888 leaves)

/--
W888 bounded derived infinity-category package through the latest W887
comparison stable ExactAt route.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfNormalizedFixedTargetFieldsComparisonStableExactAtW888
    (leaves : MetrizableWppNormalizedFixedTargetFieldLeavesW888) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfLocalizedRightAdjointFieldsComparisonStableExactAtW887
    (localizedRightAdjointFieldLeavesOfNormalizedFixedTargetFieldsW888 leaves)

/-- W888 exposes normalized fixed-target fields needed by W887. -/
def normalizedFixedTargetFieldsComparisonStableExactAtInputNamesW888 :
    List String :=
  ["bundled WPP right-open quotient-cover and source-pi-zero boundary data",
    "bundled closed natural transformation relation data",
    "target-only target-difference surjectivity plus target-codomain compactness provider",
    "matched selected-difference component and W519 mapped-cokernel closedness branch provider",
    "normalized strict-representative lift blueprint",
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

theorem normalizedFixedTargetFieldsComparisonStableExactAtInputNamesW888_count :
    normalizedFixedTargetFieldsComparisonStableExactAtInputNamesW888.length =
      17 :=
  rfl

/-- Current checked W888 state. -/
structure MetrizableNormalizedFixedTargetFieldsComparisonStableExactAtRouteStateW888 :
    Type where
  seed : String
  declarations : List String
  normalizedFixedTargetAssemblyResult : String
  exactAtResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableNormalizedFixedTargetFieldsComparisonStableExactAtRouteStateW888 :
    MetrizableNormalizedFixedTargetFieldsComparisonStableExactAtRouteStateW888
    where
  seed :=
    "w888-normalized-fixed-target-fields-comparison-stable-exact-at"
  declarations :=
    ["MetrizableWppNormalizedFixedTargetFieldLeavesW888",
      "normalizedFixedTargetDataOfFieldsW888",
      "localizedRightAdjointFieldLeavesOfNormalizedFixedTargetFieldsW888",
      "concreteLeavesOfNormalizedFixedTargetFieldsComparisonW888",
      "routeDataProviderOfNormalizedFixedTargetFieldsComparisonW888",
      "directBoundedLeftCalculusOfNormalizedFixedTargetFieldsComparisonStableExactAtW888",
      "boundedDerivedInfinityCategoryOfNormalizedFixedTargetFieldsComparisonStableExactAtW888",
      "normalizedFixedTargetFieldsComparisonStableExactAtInputNamesW888",
      "normalizedFixedTargetFieldsComparisonStableExactAtInputNamesW888_count"]
  normalizedFixedTargetAssemblyResult :=
    "proved: explicit normalized fixed-target fields assemble the W719 provider\
      consumed by the W887 comparison stable ExactAt route"
  exactAtResult :=
    "proved: explicit normalized fixed-target fields feed the W887 stable\
      ExactAt route"
  replacedInputs :=
    ["W719 normalized fixed-target data provider"]
  remainingInputs :=
    normalizedFixedTargetFieldsComparisonStableExactAtInputNamesW888
  productSuccessClaimed := false

theorem currentW888NormalizedFixedTargetFieldsComparisonStableExactAtRoute_productSuccess :
    (let state :=
        currentMetrizableNormalizedFixedTargetFieldsComparisonStableExactAtRouteStateW888;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
