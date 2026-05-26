import LeanLCAExactChallenge.Derived.NormalizedLiftBlueprintFieldsComparisonStableExactAtRoute

/-!
W890 feeds the W889 normalized-lift-blueprint-fields comparison stable-ExactAt
route from explicit strict-representative lift blueprint fields.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/--
W890 replaces the bundled coherent strict-representative lift blueprint by its
object-data, map-data, identity, and composition coherence fields.
-/
structure MetrizableWppStrictRepresentativeLiftBlueprintFieldLeavesW890 :
    Type 2 where
  boundaryData :
    MetrizableWppLimitBoundaryDataW716
  relationData :
    ClosedNatTransOrdinaryRelationDataProviderW717
  targetSurjectiveCompactForTargetProvider :
    TargetSurjectiveCompactForTargetProviderW715
  diagramAndMappedCokernelClosednessData :
    MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725
  strictRepresentativeObjectData :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      Dbounded.MetrizableWalkingParallelPairStrictPreimageData Y
  strictRepresentativeMapData :
    ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z),
      Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData
        (strictRepresentativeObjectData Y) (strictRepresentativeObjectData Z) τ
  strictRepresentativeMapId :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      (strictRepresentativeMapData (𝟙 Y)).natTrans =
        𝟙 (strictRepresentativeObjectData Y).diagram
  strictRepresentativeMapComp :
    ∀ {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
      (τ : Y ⟶ Z) (σ : Z ⟶ T),
      (strictRepresentativeMapData (τ ≫ σ)).natTrans =
        (strictRepresentativeMapData τ).natTrans ≫
          (strictRepresentativeMapData σ).natTrans
  sourceImageObjectNormalization :
    ∀ (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}),
      (strictRepresentativeObjectData
        (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.obj X)).diagram = X
  sourceImageMapNormalization :
    ∀ {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}} (τ : X ⟶ Y),
      (strictRepresentativeMapData
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

/-- W890 assembles the strict-representative lift blueprint from explicit fields. -/
def strictRepresentativeLiftBlueprintOfFieldsW890
    (leaves : MetrizableWppStrictRepresentativeLiftBlueprintFieldLeavesW890) :
    Dbounded.MetrizableWalkingParallelPairLiftBlueprint
    where
  objData := leaves.strictRepresentativeObjectData
  mapData := leaves.strictRepresentativeMapData
  map_id := leaves.strictRepresentativeMapId
  map_comp := leaves.strictRepresentativeMapComp

/-- W890 assembles the W889 leaves from strict-representative lift fields. -/
def normalizedLiftBlueprintFieldLeavesOfStrictRepresentativeFieldsW890
    (leaves : MetrizableWppStrictRepresentativeLiftBlueprintFieldLeavesW890) :
    MetrizableWppNormalizedLiftBlueprintFieldLeavesW889
    where
  boundaryData := leaves.boundaryData
  relationData := leaves.relationData
  targetSurjectiveCompactForTargetProvider :=
    leaves.targetSurjectiveCompactForTargetProvider
  diagramAndMappedCokernelClosednessData :=
    leaves.diagramAndMappedCokernelClosednessData
  strictRepresentativeLiftBlueprint :=
    strictRepresentativeLiftBlueprintOfFieldsW890 leaves
  sourceImageObjectNormalization :=
    leaves.sourceImageObjectNormalization
  sourceImageMapNormalization :=
    leaves.sourceImageMapNormalization
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

/-- W890 W733 concrete leaves from explicit strict-representative lift fields. -/
def concreteLeavesOfStrictRepresentativeFieldsComparisonW890
    (leaves : MetrizableWppStrictRepresentativeLiftBlueprintFieldLeavesW890) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfNormalizedLiftBlueprintFieldsComparisonW889
    (normalizedLiftBlueprintFieldLeavesOfStrictRepresentativeFieldsW890 leaves)

/-- W890 W732 route data from explicit strict-representative lift fields. -/
def routeDataProviderOfStrictRepresentativeFieldsComparisonW890
    (leaves : MetrizableWppStrictRepresentativeLiftBlueprintFieldLeavesW890) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfNormalizedLiftBlueprintFieldsComparisonW889
    (normalizedLiftBlueprintFieldLeavesOfStrictRepresentativeFieldsW890 leaves)

/--
W890 direct bounded left calculus through the latest W889 comparison stable
ExactAt route.
-/
theorem directBoundedLeftCalculusOfStrictRepresentativeFieldsComparisonStableExactAtW890
    (leaves : MetrizableWppStrictRepresentativeLiftBlueprintFieldLeavesW890) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfNormalizedLiftBlueprintFieldsComparisonStableExactAtW889
    (normalizedLiftBlueprintFieldLeavesOfStrictRepresentativeFieldsW890 leaves)

/--
W890 bounded derived infinity-category package through the latest W889
comparison stable ExactAt route.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfStrictRepresentativeFieldsComparisonStableExactAtW890
    (leaves : MetrizableWppStrictRepresentativeLiftBlueprintFieldLeavesW890) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfNormalizedLiftBlueprintFieldsComparisonStableExactAtW889
    (normalizedLiftBlueprintFieldLeavesOfStrictRepresentativeFieldsW890 leaves)

/-- W890 exposes strict-representative lift blueprint fields needed by W889. -/
def strictRepresentativeFieldsComparisonStableExactAtInputNamesW890 :
    List String :=
  ["bundled WPP right-open quotient-cover and source-pi-zero boundary data",
    "bundled closed natural transformation relation data",
    "target-only target-difference surjectivity plus target-codomain compactness provider",
    "matched selected-difference component and W519 mapped-cokernel closedness branch provider",
    "strict preimage object data for every WalkingParallelPair diagram",
    "strict preimage map data for every WalkingParallelPair morphism",
    "strict-representative lift identity coherence",
    "strict-representative lift composition coherence",
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

theorem strictRepresentativeFieldsComparisonStableExactAtInputNamesW890_count :
    strictRepresentativeFieldsComparisonStableExactAtInputNamesW890.length =
      22 :=
  rfl

/-- Current checked W890 state. -/
structure MetrizableStrictRepresentativeFieldsComparisonStableExactAtRouteStateW890 :
    Type where
  seed : String
  declarations : List String
  strictRepresentativeLiftAssemblyResult : String
  exactAtResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableStrictRepresentativeFieldsComparisonStableExactAtRouteStateW890 :
    MetrizableStrictRepresentativeFieldsComparisonStableExactAtRouteStateW890
    where
  seed :=
    "w890-strict-representative-lift-fields-comparison-stable-exact-at"
  declarations :=
    ["MetrizableWppStrictRepresentativeLiftBlueprintFieldLeavesW890",
      "strictRepresentativeLiftBlueprintOfFieldsW890",
      "normalizedLiftBlueprintFieldLeavesOfStrictRepresentativeFieldsW890",
      "concreteLeavesOfStrictRepresentativeFieldsComparisonW890",
      "routeDataProviderOfStrictRepresentativeFieldsComparisonW890",
      "directBoundedLeftCalculusOfStrictRepresentativeFieldsComparisonStableExactAtW890",
      "boundedDerivedInfinityCategoryOfStrictRepresentativeFieldsComparisonStableExactAtW890",
      "strictRepresentativeFieldsComparisonStableExactAtInputNamesW890",
      "strictRepresentativeFieldsComparisonStableExactAtInputNamesW890_count"]
  strictRepresentativeLiftAssemblyResult :=
    "proved: explicit object, map, identity, and composition fields assemble\
      the strict-representative lift blueprint consumed by W889"
  exactAtResult :=
    "proved: explicit strict-representative lift fields feed the W889 stable\
      ExactAt route"
  replacedInputs :=
    ["coherent strict representatives for WalkingParallelPair diagrams and maps"]
  remainingInputs :=
    strictRepresentativeFieldsComparisonStableExactAtInputNamesW890
  productSuccessClaimed := false

theorem currentW890StrictRepresentativeFieldsComparisonStableExactAtRoute_productSuccess :
    (let state :=
        currentMetrizableStrictRepresentativeFieldsComparisonStableExactAtRouteStateW890;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
