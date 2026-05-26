import LeanLCAExactChallenge.Derived.ClosedMapEndpointFactsLocalizedRightAdjointComparisonStableExactAtRoute

/-!
W901 feeds the W900 closed-map endpoint-facts localized-right-adjoint comparison
stable-ExactAt route while bundling the source triangulation and triangle
completion data through the existing W722 provider.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

/-- W901 projects the source pretriangulated structure from W722 data. -/
@[reducible]
def sourcePretriangulatedOfSourceTriangulationW901
    (sourceData : MetrizableWppSourceTriangulationDataProviderW722) :
    letI : ∀ n : ℤ,
        (shiftFunctor (BoundedComplexCategory MetrizableLCA.{0}) n).Additive :=
      inferInstance
    Pretriangulated (BoundedComplexCategory MetrizableLCA.{0}) :=
  sourcePretriangulated_of_sourceTriangulationDataW722 sourceData

/-- W901 projects the source triangulated structure from W722 data. -/
@[reducible]
def sourceTriangulatedOfSourceTriangulationW901
    (sourceData : MetrizableWppSourceTriangulationDataProviderW722) :
    letI : ∀ n : ℤ,
        (shiftFunctor (BoundedComplexCategory MetrizableLCA.{0}) n).Additive :=
      inferInstance
    letI : Pretriangulated (BoundedComplexCategory MetrizableLCA.{0}) :=
      sourcePretriangulatedOfSourceTriangulationW901 sourceData
    IsTriangulated (BoundedComplexCategory MetrizableLCA.{0}) :=
  sourceTriangulated_of_sourceTriangulationDataW722 sourceData

/-- W901 projects source-side triangle completion from W722 data. -/
def triangleCompletionOfSourceTriangulationW901
    (sourceData : MetrizableWppSourceTriangulationDataProviderW722) :
    letI : ∀ n : ℤ,
        (shiftFunctor (BoundedComplexCategory MetrizableLCA.{0}) n).Additive :=
      inferInstance
    letI : Pretriangulated (BoundedComplexCategory MetrizableLCA.{0}) :=
      sourcePretriangulatedOfSourceTriangulationW901 sourceData
    MetrizableBoundedExactWeakEquivalenceTriangleCompletionInputW654 :=
  triangleCompletion_of_sourceTriangulationDataW722 sourceData

/--
W901 replaces W900's three source triangulation fields with the existing W722
source-triangulation data provider.
-/
structure MetrizableWppClosedMapSourceTriangulationEndpointFactsLeavesW901 :
    Type 2 where
  rightOpenBoundary :
    Dbounded.MetrizableWppLimitRightOpenClosedQuotientCoverBoundary
  sourcePiZeroBoundary :
    Dbounded.MetrizableWppLimitSourceDifferenceCokernelPiZeroBoundary
  relationPullbackProvider :
    ClosedNatTransOrdinaryRelationPullbackProviderW712
  targetRelationLiftsProvider :
    ClosedNatTransOrdinaryTargetRelationLiftsProviderW712
  targetDifferenceSurjectiveForTargetProvider :
    TargetDifferenceSurjectiveForTargetProviderW713
  targetCodomainCompactSpaceProvider :
    TargetCodomainCompactSpaceProviderW601
  globalClosedMapComponents :
    SelectedDifferenceClosedMapDiagramComponentProviderW718
  mappedCokernelClosedMapProvider :
    MappedExplicitCokernelClosedMapProviderW519
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
  strictPreimageZeroMap :
    ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (_τ : Y ⟶ Z),
      strictPreimageZeroSrc Y ⟶ strictPreimageZeroSrc Z
  strictPreimageOneMap :
    ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (_τ : Y ⟶ Z),
      strictPreimageOneSrc Y ⟶ strictPreimageOneSrc Z
  strictPreimageZeroMapFac :
    ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z),
      (Dbounded.localization MetrizableLCA.{0}).map
          (strictPreimageZeroMap τ) =
        (strictPreimageZeroIso Y).hom ≫
          τ.app WalkingParallelPair.zero ≫
            (strictPreimageZeroIso Z).inv
  strictPreimageOneMapFac :
    ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z),
      (Dbounded.localization MetrizableLCA.{0}).map
          (strictPreimageOneMap τ) =
        (strictPreimageOneIso Y).hom ≫
          τ.app WalkingParallelPair.one ≫
            (strictPreimageOneIso Z).inv
  strictPreimageLeftNaturality :
    ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z),
      strictPreimageLeftSrc Y ≫ strictPreimageOneMap τ =
        strictPreimageZeroMap τ ≫ strictPreimageLeftSrc Z
  strictPreimageRightNaturality :
    ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z),
      strictPreimageRightSrc Y ≫ strictPreimageOneMap τ =
        strictPreimageZeroMap τ ≫ strictPreimageRightSrc Z
  strictRepresentativeMapId :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      (strictPreimageMapDataOfFieldsW892 strictPreimageZeroSrc
          strictPreimageOneSrc strictPreimageZeroIso strictPreimageOneIso
          strictPreimageLeftSrc strictPreimageRightSrc strictPreimageLeftFac
          strictPreimageRightFac strictPreimageZeroMap strictPreimageOneMap
          strictPreimageZeroMapFac strictPreimageOneMapFac
          strictPreimageLeftNaturality strictPreimageRightNaturality (𝟙 Y)).natTrans =
        𝟙 (strictPreimageObjectDataOfFieldsW891 strictPreimageZeroSrc
          strictPreimageOneSrc strictPreimageZeroIso strictPreimageOneIso
          strictPreimageLeftSrc strictPreimageRightSrc strictPreimageLeftFac
          strictPreimageRightFac Y).diagram
  strictRepresentativeMapComp :
    ∀ {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
      (τ : Y ⟶ Z) (σ : Z ⟶ T),
      (strictPreimageMapDataOfFieldsW892 strictPreimageZeroSrc
          strictPreimageOneSrc strictPreimageZeroIso strictPreimageOneIso
          strictPreimageLeftSrc strictPreimageRightSrc strictPreimageLeftFac
          strictPreimageRightFac strictPreimageZeroMap strictPreimageOneMap
          strictPreimageZeroMapFac strictPreimageOneMapFac
          strictPreimageLeftNaturality strictPreimageRightNaturality (τ ≫ σ)).natTrans =
        (strictPreimageMapDataOfFieldsW892 strictPreimageZeroSrc
          strictPreimageOneSrc strictPreimageZeroIso strictPreimageOneIso
          strictPreimageLeftSrc strictPreimageRightSrc strictPreimageLeftFac
          strictPreimageRightFac strictPreimageZeroMap strictPreimageOneMap
          strictPreimageZeroMapFac strictPreimageOneMapFac
          strictPreimageLeftNaturality strictPreimageRightNaturality τ).natTrans ≫
            (strictPreimageMapDataOfFieldsW892 strictPreimageZeroSrc
              strictPreimageOneSrc strictPreimageZeroIso strictPreimageOneIso
              strictPreimageLeftSrc strictPreimageRightSrc strictPreimageLeftFac
              strictPreimageRightFac strictPreimageZeroMap strictPreimageOneMap
              strictPreimageZeroMapFac strictPreimageOneMapFac
              strictPreimageLeftNaturality strictPreimageRightNaturality σ).natTrans
  sourceImageObjectNormalization :
    ∀ (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}),
      (strictPreimageObjectDataOfFieldsW891 strictPreimageZeroSrc
        strictPreimageOneSrc strictPreimageZeroIso strictPreimageOneIso
        strictPreimageLeftSrc strictPreimageRightSrc strictPreimageLeftFac
        strictPreimageRightFac
        (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.obj X)).diagram = X
  sourceImageMapNormalization :
    ∀ {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}} (τ : X ⟶ Y),
      (strictPreimageMapDataOfFieldsW892 strictPreimageZeroSrc
          strictPreimageOneSrc strictPreimageZeroIso strictPreimageOneIso
          strictPreimageLeftSrc strictPreimageRightSrc strictPreimageLeftFac
          strictPreimageRightFac strictPreimageZeroMap strictPreimageOneMap
          strictPreimageZeroMapFac strictPreimageOneMapFac
          strictPreimageLeftNaturality strictPreimageRightNaturality
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
  sourceTriangulationData :
    MetrizableWppSourceTriangulationDataProviderW722
  endpointTopologyFacts :
    MetrizableWppEndpointTopologyFactsProviderW856
  localizedRightAdjointData :
    MetrizableWppLocalizedRightAdjointDataProviderW721

/-- W901 projects W900 leaves from the W722 source-triangulation provider. -/
def closedMapEndpointLocalizedAdjointLeavesOfSourceTriangulationW901
    (leaves : MetrizableWppClosedMapSourceTriangulationEndpointFactsLeavesW901) :
    MetrizableWppClosedMapEndpointFactsLocalizedRightAdjointLeavesW900
    where
  rightOpenBoundary := leaves.rightOpenBoundary
  sourcePiZeroBoundary := leaves.sourcePiZeroBoundary
  relationPullbackProvider := leaves.relationPullbackProvider
  targetRelationLiftsProvider := leaves.targetRelationLiftsProvider
  targetDifferenceSurjectiveForTargetProvider :=
    leaves.targetDifferenceSurjectiveForTargetProvider
  targetCodomainCompactSpaceProvider :=
    leaves.targetCodomainCompactSpaceProvider
  globalClosedMapComponents := leaves.globalClosedMapComponents
  mappedCokernelClosedMapProvider :=
    leaves.mappedCokernelClosedMapProvider
  strictPreimageZeroSrc := leaves.strictPreimageZeroSrc
  strictPreimageOneSrc := leaves.strictPreimageOneSrc
  strictPreimageZeroIso := leaves.strictPreimageZeroIso
  strictPreimageOneIso := leaves.strictPreimageOneIso
  strictPreimageLeftSrc := leaves.strictPreimageLeftSrc
  strictPreimageRightSrc := leaves.strictPreimageRightSrc
  strictPreimageLeftFac := leaves.strictPreimageLeftFac
  strictPreimageRightFac := leaves.strictPreimageRightFac
  strictPreimageZeroMap := leaves.strictPreimageZeroMap
  strictPreimageOneMap := leaves.strictPreimageOneMap
  strictPreimageZeroMapFac := leaves.strictPreimageZeroMapFac
  strictPreimageOneMapFac := leaves.strictPreimageOneMapFac
  strictPreimageLeftNaturality := leaves.strictPreimageLeftNaturality
  strictPreimageRightNaturality := leaves.strictPreimageRightNaturality
  strictRepresentativeMapId := leaves.strictRepresentativeMapId
  strictRepresentativeMapComp := leaves.strictRepresentativeMapComp
  sourceImageObjectNormalization :=
    leaves.sourceImageObjectNormalization
  sourceImageMapNormalization :=
    leaves.sourceImageMapNormalization
  targetFixedTargetUniq := leaves.targetFixedTargetUniq
  localizationModelFixedTargetUniq :=
    leaves.localizationModelFixedTargetUniq
  sourcePretriangulated :=
    sourcePretriangulatedOfSourceTriangulationW901
      leaves.sourceTriangulationData
  sourceTriangulated :=
    sourceTriangulatedOfSourceTriangulationW901
      leaves.sourceTriangulationData
  triangleCompletion :=
    triangleCompletionOfSourceTriangulationW901
      leaves.sourceTriangulationData
  endpointTopologyFacts := leaves.endpointTopologyFacts
  localizedRightAdjointData := leaves.localizedRightAdjointData

/-- W901 W733 concrete leaves after projecting W900 leaves. -/
def concreteLeavesOfClosedMapSourceTriangulationEndpointFactsW901
    (leaves : MetrizableWppClosedMapSourceTriangulationEndpointFactsLeavesW901) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfClosedMapEndpointFactsLocalizedRightAdjointComparisonW900
    (closedMapEndpointLocalizedAdjointLeavesOfSourceTriangulationW901 leaves)

/-- W901 W732 route data after projecting W900 leaves. -/
def routeDataProviderOfClosedMapSourceTriangulationEndpointFactsW901
    (leaves : MetrizableWppClosedMapSourceTriangulationEndpointFactsLeavesW901) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfClosedMapEndpointFactsLocalizedRightAdjointComparisonW900
    (closedMapEndpointLocalizedAdjointLeavesOfSourceTriangulationW901 leaves)

/--
W901 direct bounded left calculus through the latest W900 comparison stable
ExactAt route.
-/
theorem directBoundedLeftCalculusOfClosedMapSourceTriangulationEndpointFactsW901
    (leaves : MetrizableWppClosedMapSourceTriangulationEndpointFactsLeavesW901) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapEndpointLocalizedAdjointW900
    (closedMapEndpointLocalizedAdjointLeavesOfSourceTriangulationW901 leaves)

/--
W901 bounded derived infinity-category package through the latest W900
comparison stable ExactAt route.
-/
noncomputable def boundedDerivedInfinityCategoryOfClosedMapSourceTriangulationEndpointFactsW901
    (leaves : MetrizableWppClosedMapSourceTriangulationEndpointFactsLeavesW901) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapEndpointLocalizedAdjointW900
    (closedMapEndpointLocalizedAdjointLeavesOfSourceTriangulationW901 leaves)

/-- W901 exposes W900's fields with source triangulation bundled through W722. -/
def closedMapSourceTriangulationEndpointFactsInputNamesW901 :
    List String :=
  ["WPP right-open quotient-cover boundary data",
    "WPP source-pi-zero boundary data",
    "closed natural transformation relation-pullback provider",
    "closed natural transformation target-relation-lift provider",
    "target-difference surjectivity provider",
    "target-codomain compactness provider",
    "selected-difference closed-map diagram component provider",
    "W519 mapped explicit cokernel closed-map provider",
    "strict preimage zero object source for every WalkingParallelPair diagram",
    "strict preimage one object source for every WalkingParallelPair diagram",
    "strict preimage zero object localization isomorphism",
    "strict preimage one object localization isomorphism",
    "strict preimage left source map",
    "strict preimage right source map",
    "strict preimage left localization factorization",
    "strict preimage right localization factorization",
    "strict preimage zero component map for every WalkingParallelPair morphism",
    "strict preimage one component map for every WalkingParallelPair morphism",
    "strict preimage zero component map factorization",
    "strict preimage one component map factorization",
    "strict preimage left naturality square",
    "strict preimage right naturality square",
    "strict-representative lift identity coherence",
    "strict-representative lift composition coherence",
    "source-image object normalization for the strict-representative lift",
    "source-image map normalization for the strict-representative lift",
    "target fixed-target uniqueness obligation",
    "localization-model fixed-target uniqueness obligation",
    "W722 source triangulation and triangle-completion data provider",
    "W856 endpoint topology facts provider",
    "W721 bounded homotopy localized right-adjoint data provider"]

theorem closedMapSourceTriangulationEndpointFactsInputNamesW901_count :
    closedMapSourceTriangulationEndpointFactsInputNamesW901.length =
      31 :=
  rfl

/-- Current checked W901 state. -/
structure MetrizableClosedMapSourceTriangulationEndpointFactsRouteStateW901 :
    Type where
  seed : String
  declarations : List String
  sourceTriangulationResult : String
  exactAtResult : String
  removedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedMapSourceTriangulationEndpointFactsRouteStateW901 :
    MetrizableClosedMapSourceTriangulationEndpointFactsRouteStateW901
    where
  seed :=
    "w901-closed-map-source-triangulation-endpoint-facts-localized-right-adjoint"
  declarations :=
    ["MetrizableWppClosedMapSourceTriangulationEndpointFactsLeavesW901",
      "sourcePretriangulatedOfSourceTriangulationW901",
      "sourceTriangulatedOfSourceTriangulationW901",
      "triangleCompletionOfSourceTriangulationW901",
      "closedMapEndpointLocalizedAdjointLeavesOfSourceTriangulationW901",
      "concreteLeavesOfClosedMapSourceTriangulationEndpointFactsW901",
      "routeDataProviderOfClosedMapSourceTriangulationEndpointFactsW901",
      "directBoundedLeftCalculusOfClosedMapSourceTriangulationEndpointFactsW901",
      "boundedDerivedInfinityCategoryOfClosedMapSourceTriangulationEndpointFactsW901",
      "closedMapSourceTriangulationEndpointFactsInputNamesW901",
      "closedMapSourceTriangulationEndpointFactsInputNamesW901_count"]
  sourceTriangulationResult :=
    "proved: W722 source-triangulation data supplies W900's source\
      Pretriangulated, IsTriangulated, and triangle-completion fields"
  exactAtResult :=
    "proved: closed-map source-triangulation endpoint-facts fields feed the W900\
      stable ExactAt route"
  removedInputs :=
    ["Pretriangulated structure on BoundedComplexCategory MetrizableLCA",
      "IsTriangulated structure on BoundedComplexCategory MetrizableLCA",
      "bounded exact weak equivalence source-side triangle-completion data"]
  remainingInputs :=
    closedMapSourceTriangulationEndpointFactsInputNamesW901
  productSuccessClaimed := false

theorem currentW901ClosedMapSourceTriangulationEndpointFactsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedMapSourceTriangulationEndpointFactsRouteStateW901;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
