import LeanLCAExactChallenge.Derived.StrictRepresentativeLiftFieldsComparisonStableExactAtRoute

/-!
W891 feeds the W890 strict-representative-lift-fields comparison stable-ExactAt
route from explicit strict preimage object fields.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W891 assembles one strict preimage object datum from its constructor fields. -/
def strictPreimageObjectDataOfFieldsW891
    (zeroSrc :
      ∀ (_Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
        BoundedComplexCategory MetrizableLCA.{0})
    (oneSrc :
      ∀ (_Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
        BoundedComplexCategory MetrizableLCA.{0})
    (zeroIso :
      ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
        (Dbounded.localization MetrizableLCA.{0}).obj (zeroSrc Y) ≅
          Y.obj WalkingParallelPair.zero)
    (oneIso :
      ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
        (Dbounded.localization MetrizableLCA.{0}).obj (oneSrc Y) ≅
          Y.obj WalkingParallelPair.one)
    (leftSrc :
      ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
        zeroSrc Y ⟶ oneSrc Y)
    (rightSrc :
      ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
        zeroSrc Y ⟶ oneSrc Y)
    (left_fac :
      ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
        (Dbounded.localization MetrizableLCA.{0}).map (leftSrc Y) =
          (zeroIso Y).hom ≫ Y.map WalkingParallelPairHom.left ≫ (oneIso Y).inv)
    (right_fac :
      ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
        (Dbounded.localization MetrizableLCA.{0}).map (rightSrc Y) =
          (zeroIso Y).hom ≫ Y.map WalkingParallelPairHom.right ≫ (oneIso Y).inv)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    Dbounded.MetrizableWalkingParallelPairStrictPreimageData Y
    where
  zeroSrc := zeroSrc Y
  oneSrc := oneSrc Y
  zeroIso := zeroIso Y
  oneIso := oneIso Y
  leftSrc := leftSrc Y
  rightSrc := rightSrc Y
  left_fac := left_fac Y
  right_fac := right_fac Y

/--
W891 replaces the bundled strict preimage object-data family by its eight
constructor fields.
-/
structure MetrizableWppStrictPreimageObjectFieldLeavesW891 :
    Type 2 where
  boundaryData :
    MetrizableWppLimitBoundaryDataW716
  relationData :
    ClosedNatTransOrdinaryRelationDataProviderW717
  targetSurjectiveCompactForTargetProvider :
    TargetSurjectiveCompactForTargetProviderW715
  diagramAndMappedCokernelClosednessData :
    MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725
  strictPreimageZeroSrc :
    ∀ (_Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      BoundedComplexCategory MetrizableLCA.{0}
  strictPreimageOneSrc :
    ∀ (_Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      BoundedComplexCategory MetrizableLCA.{0}
  strictPreimageZeroIso :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      (Dbounded.localization MetrizableLCA.{0}).obj (strictPreimageZeroSrc Y) ≅
        Y.obj WalkingParallelPair.zero
  strictPreimageOneIso :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      (Dbounded.localization MetrizableLCA.{0}).obj (strictPreimageOneSrc Y) ≅
        Y.obj WalkingParallelPair.one
  strictPreimageLeftSrc :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      strictPreimageZeroSrc Y ⟶ strictPreimageOneSrc Y
  strictPreimageRightSrc :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      strictPreimageZeroSrc Y ⟶ strictPreimageOneSrc Y
  strictPreimageLeftFac :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      (Dbounded.localization MetrizableLCA.{0}).map
          (strictPreimageLeftSrc Y) =
        (strictPreimageZeroIso Y).hom ≫
          Y.map WalkingParallelPairHom.left ≫
            (strictPreimageOneIso Y).inv
  strictPreimageRightFac :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      (Dbounded.localization MetrizableLCA.{0}).map
          (strictPreimageRightSrc Y) =
        (strictPreimageZeroIso Y).hom ≫
          Y.map WalkingParallelPairHom.right ≫
            (strictPreimageOneIso Y).inv
  strictRepresentativeMapData :
    ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z),
      Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData
        (strictPreimageObjectDataOfFieldsW891 strictPreimageZeroSrc
          strictPreimageOneSrc strictPreimageZeroIso strictPreimageOneIso
          strictPreimageLeftSrc strictPreimageRightSrc strictPreimageLeftFac
          strictPreimageRightFac Y)
        (strictPreimageObjectDataOfFieldsW891 strictPreimageZeroSrc
          strictPreimageOneSrc strictPreimageZeroIso strictPreimageOneIso
          strictPreimageLeftSrc strictPreimageRightSrc strictPreimageLeftFac
          strictPreimageRightFac Z)
        τ
  strictRepresentativeMapId :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      (strictRepresentativeMapData (𝟙 Y)).natTrans =
        𝟙 (strictPreimageObjectDataOfFieldsW891 strictPreimageZeroSrc
          strictPreimageOneSrc strictPreimageZeroIso strictPreimageOneIso
          strictPreimageLeftSrc strictPreimageRightSrc strictPreimageLeftFac
          strictPreimageRightFac Y).diagram
  strictRepresentativeMapComp :
    ∀ {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
      (τ : Y ⟶ Z) (σ : Z ⟶ T),
      (strictRepresentativeMapData (τ ≫ σ)).natTrans =
        (strictRepresentativeMapData τ).natTrans ≫
          (strictRepresentativeMapData σ).natTrans
  sourceImageObjectNormalization :
    ∀ (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}),
      (strictPreimageObjectDataOfFieldsW891 strictPreimageZeroSrc
        strictPreimageOneSrc strictPreimageZeroIso strictPreimageOneIso
        strictPreimageLeftSrc strictPreimageRightSrc strictPreimageLeftFac
        strictPreimageRightFac
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

/-- W891 assembles the strict preimage object-data family from explicit fields. -/
def strictRepresentativeObjectDataOfFieldsW891
    (leaves : MetrizableWppStrictPreimageObjectFieldLeavesW891) :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      Dbounded.MetrizableWalkingParallelPairStrictPreimageData Y :=
  fun Y =>
    strictPreimageObjectDataOfFieldsW891 leaves.strictPreimageZeroSrc
      leaves.strictPreimageOneSrc leaves.strictPreimageZeroIso
      leaves.strictPreimageOneIso leaves.strictPreimageLeftSrc
      leaves.strictPreimageRightSrc leaves.strictPreimageLeftFac
      leaves.strictPreimageRightFac Y

/-- W891 assembles the W890 leaves from strict preimage object fields. -/
def strictRepresentativeFieldLeavesOfObjectFieldsW891
    (leaves : MetrizableWppStrictPreimageObjectFieldLeavesW891) :
    MetrizableWppStrictRepresentativeLiftBlueprintFieldLeavesW890
    where
  boundaryData := leaves.boundaryData
  relationData := leaves.relationData
  targetSurjectiveCompactForTargetProvider :=
    leaves.targetSurjectiveCompactForTargetProvider
  diagramAndMappedCokernelClosednessData :=
    leaves.diagramAndMappedCokernelClosednessData
  strictRepresentativeObjectData :=
    strictRepresentativeObjectDataOfFieldsW891 leaves
  strictRepresentativeMapData := leaves.strictRepresentativeMapData
  strictRepresentativeMapId := leaves.strictRepresentativeMapId
  strictRepresentativeMapComp := leaves.strictRepresentativeMapComp
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

/-- W891 W733 concrete leaves from explicit strict preimage object fields. -/
def concreteLeavesOfStrictPreimageObjectFieldsComparisonW891
    (leaves : MetrizableWppStrictPreimageObjectFieldLeavesW891) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfStrictRepresentativeFieldsComparisonW890
    (strictRepresentativeFieldLeavesOfObjectFieldsW891 leaves)

/-- W891 W732 route data from explicit strict preimage object fields. -/
def routeDataProviderOfStrictPreimageObjectFieldsComparisonW891
    (leaves : MetrizableWppStrictPreimageObjectFieldLeavesW891) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfStrictRepresentativeFieldsComparisonW890
    (strictRepresentativeFieldLeavesOfObjectFieldsW891 leaves)

/--
W891 direct bounded left calculus through the latest W890 comparison stable
ExactAt route.
-/
theorem directBoundedLeftCalculusOfStrictPreimageObjectFieldsComparisonStableExactAtW891
    (leaves : MetrizableWppStrictPreimageObjectFieldLeavesW891) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfStrictRepresentativeFieldsComparisonStableExactAtW890
    (strictRepresentativeFieldLeavesOfObjectFieldsW891 leaves)

/--
W891 bounded derived infinity-category package through the latest W890
comparison stable ExactAt route.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfStrictPreimageObjectFieldsComparisonStableExactAtW891
    (leaves : MetrizableWppStrictPreimageObjectFieldLeavesW891) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfStrictRepresentativeFieldsComparisonStableExactAtW890
    (strictRepresentativeFieldLeavesOfObjectFieldsW891 leaves)

/-- W891 exposes strict preimage object fields needed by W890. -/
def strictPreimageObjectFieldsComparisonStableExactAtInputNamesW891 :
    List String :=
  ["bundled WPP right-open quotient-cover and source-pi-zero boundary data",
    "bundled closed natural transformation relation data",
    "target-only target-difference surjectivity plus target-codomain compactness provider",
    "matched selected-difference component and W519 mapped-cokernel closedness branch provider",
    "strict preimage zero object source for every WalkingParallelPair diagram",
    "strict preimage one object source for every WalkingParallelPair diagram",
    "strict preimage zero object localization isomorphism",
    "strict preimage one object localization isomorphism",
    "strict preimage left source map",
    "strict preimage right source map",
    "strict preimage left localization factorization",
    "strict preimage right localization factorization",
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

theorem strictPreimageObjectFieldsComparisonStableExactAtInputNamesW891_count :
    strictPreimageObjectFieldsComparisonStableExactAtInputNamesW891.length =
      29 :=
  rfl

/-- Current checked W891 state. -/
structure MetrizableStrictPreimageObjectFieldsComparisonStableExactAtRouteStateW891 :
    Type where
  seed : String
  declarations : List String
  strictPreimageObjectAssemblyResult : String
  exactAtResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableStrictPreimageObjectFieldsComparisonStableExactAtRouteStateW891 :
    MetrizableStrictPreimageObjectFieldsComparisonStableExactAtRouteStateW891
    where
  seed :=
    "w891-strict-preimage-object-fields-comparison-stable-exact-at"
  declarations :=
    ["MetrizableWppStrictPreimageObjectFieldLeavesW891",
      "strictPreimageObjectDataOfFieldsW891",
      "strictRepresentativeObjectDataOfFieldsW891",
      "strictRepresentativeFieldLeavesOfObjectFieldsW891",
      "concreteLeavesOfStrictPreimageObjectFieldsComparisonW891",
      "routeDataProviderOfStrictPreimageObjectFieldsComparisonW891",
      "directBoundedLeftCalculusOfStrictPreimageObjectFieldsComparisonStableExactAtW891",
      "boundedDerivedInfinityCategoryOfStrictPreimageObjectFieldsComparisonStableExactAtW891",
      "strictPreimageObjectFieldsComparisonStableExactAtInputNamesW891",
      "strictPreimageObjectFieldsComparisonStableExactAtInputNamesW891_count"]
  strictPreimageObjectAssemblyResult :=
    "proved: explicit zero/one source, localization isomorphism, source map,\
      and factorization fields assemble the strict preimage object data\
      consumed by W890"
  exactAtResult :=
    "proved: explicit strict preimage object fields feed the W890 stable\
      ExactAt route"
  replacedInputs :=
    ["strict preimage object data for every WalkingParallelPair diagram"]
  remainingInputs :=
    strictPreimageObjectFieldsComparisonStableExactAtInputNamesW891
  productSuccessClaimed := false

theorem currentW891StrictPreimageObjectFieldsComparisonStableExactAtRoute_productSuccess :
    (let state :=
        currentMetrizableStrictPreimageObjectFieldsComparisonStableExactAtRouteStateW891;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
