import LeanLCAExactChallenge.Derived.ClosedMapRelationDataBoundaryDataSourceTriangulationEndpointFactsLocalizedRightAdjointComparisonStableExactAtRoute

/-!
W904 feeds the W903 closed-map relation-data boundary-data
source-triangulation endpoint-facts localized right-adjoint comparison
stable-ExactAt route while bundling the two target facts through the existing
W715 target-surjective-compact provider.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

/-- W904 projects target-difference surjectivity from W715 data. -/
def targetDifferenceProviderOfTargetDataW904
    (targetData : TargetSurjectiveCompactForTargetProviderW715) :
    TargetDifferenceSurjectiveForTargetProviderW713 :=
  targetDifferenceSurjectiveForTargetProvider_of_surjectiveCompactW715
    targetData

/-- W904 projects target-codomain compactness from W715 data. -/
@[reducible]
def targetCodomainCompactProviderOfTargetDataW904
    (targetData : TargetSurjectiveCompactForTargetProviderW715) :
    TargetCodomainCompactSpaceProviderW601 :=
  targetCodomainCompactSpaceProvider_of_surjectiveCompactW715 targetData

/--
W904 replaces W903's separate target-difference-surjectivity and
target-codomain-compactness fields with the existing W715 paired provider.
-/
structure MetrizableWppClosedMapTargetDataEndpointFactsLeavesW904 :
    Type 2 where
  boundaryData :
    MetrizableWppLimitBoundaryDataW716
  relationData :
    ClosedNatTransOrdinaryRelationDataProviderW717
  targetSurjectiveCompactForTargetProvider :
    TargetSurjectiveCompactForTargetProviderW715
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

/-- W904 projects W903 leaves from the W715 target-data provider. -/
def w903LeavesOfTargetDataW904
    (leaves :
      MetrizableWppClosedMapTargetDataEndpointFactsLeavesW904) :
    MetrizableWppClosedMapRelationDataBoundaryEndpointFactsLeavesW903
    where
  boundaryData := leaves.boundaryData
  relationData := leaves.relationData
  targetDifferenceSurjectiveForTargetProvider :=
    targetDifferenceProviderOfTargetDataW904
      leaves.targetSurjectiveCompactForTargetProvider
  targetCodomainCompactSpaceProvider :=
    targetCodomainCompactProviderOfTargetDataW904
      leaves.targetSurjectiveCompactForTargetProvider
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
  sourceTriangulationData := leaves.sourceTriangulationData
  endpointTopologyFacts := leaves.endpointTopologyFacts
  localizedRightAdjointData := leaves.localizedRightAdjointData

/-- W904 W733 concrete leaves after projecting W903 leaves. -/
def concreteLeavesOfClosedMapTargetDataEndpointFactsW904
    (leaves :
      MetrizableWppClosedMapTargetDataEndpointFactsLeavesW904) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfClosedMapRelationDataBoundaryEndpointFactsW903
    (w903LeavesOfTargetDataW904 leaves)

/-- W904 W732 route data after projecting W903 leaves. -/
def routeDataProviderOfClosedMapTargetDataEndpointFactsW904
    (leaves :
      MetrizableWppClosedMapTargetDataEndpointFactsLeavesW904) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfClosedMapRelationDataBoundaryEndpointFactsW903
    (w903LeavesOfTargetDataW904 leaves)

theorem
    directBoundedLeftCalculusOfClosedMapTargetDataEndpointFactsW904
    (leaves :
      MetrizableWppClosedMapTargetDataEndpointFactsLeavesW904) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapRelationDataBoundaryEndpointFactsW903
    (w903LeavesOfTargetDataW904 leaves)

noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapTargetDataEndpointFactsW904
    (leaves :
      MetrizableWppClosedMapTargetDataEndpointFactsLeavesW904) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapRelationDataBoundaryEndpointFactsW903
    (w903LeavesOfTargetDataW904 leaves)

/-- W904 exposes W903's fields with target data bundled through W715. -/
def closedMapTargetDataEndpointFactsInputNamesW904 :
    List String :=
  ["W716 bundled WPP right-open/source-pi-zero boundary data provider",
    "W717 bundled closed natural transformation ordinary relation data provider",
    "W715 bundled target-difference surjectivity and target-codomain compactness provider",
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

theorem closedMapTargetDataEndpointFactsInputNamesW904_count :
    closedMapTargetDataEndpointFactsInputNamesW904.length =
      28 :=
  rfl

/-- Current checked W904 state. -/
structure MetrizableClosedMapTargetDataEndpointFactsRouteStateW904 :
    Type where
  seed : String
  declarations : List String
  targetDataResult : String
  exactAtResult : String
  removedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedMapTargetDataEndpointFactsRouteStateW904 :
    MetrizableClosedMapTargetDataEndpointFactsRouteStateW904
    where
  seed :=
    "w904-closed-map-target-data-relation-data-boundary-data-source-\
      triangulation-endpoint-facts-localized-right-adjoint"
  declarations :=
    ["MetrizableWppClosedMapTargetDataEndpointFactsLeavesW904",
      "targetDifferenceProviderOfTargetDataW904",
      "targetCodomainCompactProviderOfTargetDataW904",
      "w903LeavesOfTargetDataW904",
      "concreteLeavesOfClosedMapTargetDataEndpointFactsW904",
      "routeDataProviderOfClosedMapTargetDataEndpointFactsW904",
      "directBoundedLeftCalculusOfClosedMapTargetDataEndpointFactsW904",
      "boundedDerivedInfinityCategoryOfClosedMapTargetDataEndpointFactsW904",
      "closedMapTargetDataEndpointFactsInputNamesW904",
      "closedMapTargetDataEndpointFactsInputNamesW904_count"]
  targetDataResult :=
    "proved: W715 target data supplies W903's target-difference\
      surjectivity and target-codomain compactness provider fields"
  exactAtResult :=
    "proved: closed-map target-data relation-data boundary-data\
      source-triangulation endpoint-facts fields feed the W903 stable\
      ExactAt route"
  removedInputs :=
    ["target-difference surjectivity provider",
      "target-codomain compactness provider"]
  remainingInputs :=
    closedMapTargetDataEndpointFactsInputNamesW904
  productSuccessClaimed := false

theorem
    currentW904ClosedMapTargetDataEndpointFactsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedMapTargetDataEndpointFactsRouteStateW904;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
