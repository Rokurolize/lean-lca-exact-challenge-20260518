import LeanLCAExactChallenge.Derived.ClosedMapRelationFieldsBoundaryFieldsComponentFieldsRoute

/-!
W909 feeds the W908 closed-map relation-fields boundary-fields component-fields
mapped-cokernel-field source-triangulation endpoint-facts localized
right-adjoint route while exposing the W715 target-surjective-compact provider
as target-difference-surjectivity and target-codomain compactness fields.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W909 assembles the W715 target provider from its two fields. -/
def targetDataOfFieldsW909
    (targetDifferenceSurjectiveForTargetProvider :
      TargetDifferenceSurjectiveForTargetProviderW713)
    (targetCodomainCompactSpaceProvider :
      TargetCodomainCompactSpaceProviderW601) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  fun Y =>
    ⟨targetDifferenceSurjectiveForTargetProvider Y,
      targetCodomainCompactSpaceProvider Y⟩

/--
W909 replaces W908's W715 target provider with the target-surjectivity and
target-compactness fields it packages.
-/
structure MetrizableWppClosedMapTargetFieldLeavesW909 :
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
  closedMapPi1 :
    SelectedDifferenceClosedMapPi1DiagramFieldW714
  closedMapPi2 :
    SelectedDifferenceClosedMapPi2DiagramFieldW714
  closedMapPi3 :
    SelectedDifferenceClosedMapPi3DiagramFieldW714
  mappedCokernelClosedMap :
    ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y), IsClosedMap (f : X → Y)
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

/-- W909 projects W908 leaves from the two target fields. -/
def w908LeavesOfTargetFieldsW909
    (leaves :
      MetrizableWppClosedMapTargetFieldLeavesW909) :
    MetrizableWppClosedMapRelationFieldLeavesW908
    where
  rightOpenBoundary := leaves.rightOpenBoundary
  sourcePiZeroBoundary := leaves.sourcePiZeroBoundary
  relationPullbackProvider := leaves.relationPullbackProvider
  targetRelationLiftsProvider := leaves.targetRelationLiftsProvider
  targetSurjectiveCompactForTargetProvider :=
    targetDataOfFieldsW909 leaves.targetDifferenceSurjectiveForTargetProvider
      leaves.targetCodomainCompactSpaceProvider
  closedMapPi1 := leaves.closedMapPi1
  closedMapPi2 := leaves.closedMapPi2
  closedMapPi3 := leaves.closedMapPi3
  mappedCokernelClosedMap := leaves.mappedCokernelClosedMap
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
  sourceTriangulationData := leaves.sourceTriangulationData
  endpointTopologyFacts := leaves.endpointTopologyFacts
  localizedRightAdjointData := leaves.localizedRightAdjointData

/-- W909 W733 concrete leaves after projecting W908 leaves. -/
def concreteLeavesOfClosedMapTargetFieldsW909
    (leaves : MetrizableWppClosedMapTargetFieldLeavesW909) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfClosedMapRelationFieldsW908
    (w908LeavesOfTargetFieldsW909 leaves)

/-- W909 W732 route data after projecting W908 leaves. -/
def routeDataProviderOfClosedMapTargetFieldsW909
    (leaves : MetrizableWppClosedMapTargetFieldLeavesW909) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfClosedMapRelationFieldsW908
    (w908LeavesOfTargetFieldsW909 leaves)

theorem directBoundedLeftCalculusOfClosedMapTargetFieldsW909
    (leaves : MetrizableWppClosedMapTargetFieldLeavesW909) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapRelationFieldsW908
    (w908LeavesOfTargetFieldsW909 leaves)

noncomputable def boundedDerivedInfinityCategoryOfClosedMapTargetFieldsW909
    (leaves : MetrizableWppClosedMapTargetFieldLeavesW909) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapRelationFieldsW908
    (w908LeavesOfTargetFieldsW909 leaves)

/-- W909 exposes W908's W715 target provider as its two fields. -/
def closedMapTargetFieldsInputNamesW909 :
    List String :=
  ["right-open closed-quotient-cover boundary field",
    "source-difference cokernel pi-zero boundary field",
    "closed natural transformation relation-pullback provider",
    "closed natural transformation target-relation-lift provider",
    "target-difference surjectivity for every target diagram",
    "target-codomain compactness for every target diagram",
    "selected-difference pi1 closed-map diagram component field",
    "selected-difference pi2 closed-map diagram component field",
    "selected-difference pi3 closed-map diagram component field",
    "mapped explicit cokernel maps are closed maps",
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

theorem closedMapTargetFieldsInputNamesW909_count :
    closedMapTargetFieldsInputNamesW909.length =
      33 :=
  rfl

/-- Current checked W909 state. -/
structure MetrizableClosedMapTargetFieldsRouteStateW909 :
    Type where
  seed : String
  declarations : List String
  targetFieldResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedMapTargetFieldsRouteStateW909 :
    MetrizableClosedMapTargetFieldsRouteStateW909
    where
  seed :=
    "w909-closed-map-target-fields-relation-fields-boundary-fields-\
      component-fields-mapped-cokernel-field-source-triangulation-\
      endpoint-facts-localized-right-adjoint"
  declarations :=
    ["MetrizableWppClosedMapTargetFieldLeavesW909",
      "targetDataOfFieldsW909",
      "w908LeavesOfTargetFieldsW909",
      "concreteLeavesOfClosedMapTargetFieldsW909",
      "routeDataProviderOfClosedMapTargetFieldsW909",
      "directBoundedLeftCalculusOfClosedMapTargetFieldsW909",
      "boundedDerivedInfinityCategoryOfClosedMapTargetFieldsW909",
      "closedMapTargetFieldsInputNamesW909",
      "closedMapTargetFieldsInputNamesW909_count"]
  targetFieldResult :=
    "proved: target-surjectivity and target-compactness fields supply W908's\
      W715 target-surjective-compact provider"
  exactAtResult :=
    "proved: closed-map target-fields relation-fields boundary-fields\
      component-fields mapped-cokernel-field source-triangulation\
      endpoint-facts fields feed the W908 stable ExactAt route"
  refinedInputs :=
    ["W715 bundled target-difference surjectivity and target-codomain\
      compactness provider"]
  remainingInputs :=
    closedMapTargetFieldsInputNamesW909
  productSuccessClaimed := false

theorem currentW909ClosedMapTargetFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedMapTargetFieldsRouteStateW909;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
