import LeanLCAExactChallenge.Derived.ClosedMapSourceTriangulationEndpointFactsLocalizedRightAdjointComparisonStableExactAtRoute

/-!
W902 feeds the W901 closed-map source-triangulation endpoint-facts localized
right-adjoint comparison stable-ExactAt route while bundling the two WPP
boundary fields through the existing W716 provider.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

/-- W902 projects the right-open boundary from W716 data. -/
@[reducible]
def rightOpenBoundaryOfBoundaryDataW902
    (boundaryData : MetrizableWppLimitBoundaryDataW716) :
    Dbounded.MetrizableWppLimitRightOpenClosedQuotientCoverBoundary :=
  rightOpenBoundary_of_boundaryDataW716 boundaryData

/-- W902 projects the source-pi-zero boundary from W716 data. -/
def sourcePiZeroBoundaryOfBoundaryDataW902
    (boundaryData : MetrizableWppLimitBoundaryDataW716) :
    Dbounded.MetrizableWppLimitSourceDifferenceCokernelPiZeroBoundary :=
  sourcePiZeroBoundary_of_boundaryDataW716 boundaryData

/--
W902 replaces W901's separate WPP boundary fields with the existing W716
boundary-data provider.
-/
structure MetrizableWppClosedMapBoundaryDataSourceTriangulationEndpointFactsLeavesW902 :
    Type 2 where
  boundaryData :
    MetrizableWppLimitBoundaryDataW716
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

/-- W902 projects W901 leaves from the W716 boundary-data provider. -/
def closedMapSourceTriangulationEndpointFactsLeavesOfBoundaryDataW902
    (leaves : MetrizableWppClosedMapBoundaryDataSourceTriangulationEndpointFactsLeavesW902) :
    MetrizableWppClosedMapSourceTriangulationEndpointFactsLeavesW901
    where
  rightOpenBoundary :=
    rightOpenBoundaryOfBoundaryDataW902 leaves.boundaryData
  sourcePiZeroBoundary :=
    sourcePiZeroBoundaryOfBoundaryDataW902 leaves.boundaryData
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
  sourceTriangulationData := leaves.sourceTriangulationData
  endpointTopologyFacts := leaves.endpointTopologyFacts
  localizedRightAdjointData := leaves.localizedRightAdjointData

/-- W902 W733 concrete leaves after projecting W901 leaves. -/
def concreteLeavesOfClosedMapBoundaryDataSourceTriangulationEndpointFactsW902
    (leaves : MetrizableWppClosedMapBoundaryDataSourceTriangulationEndpointFactsLeavesW902) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfClosedMapSourceTriangulationEndpointFactsW901
    (closedMapSourceTriangulationEndpointFactsLeavesOfBoundaryDataW902 leaves)

/-- W902 W732 route data after projecting W901 leaves. -/
def routeDataProviderOfClosedMapBoundaryDataSourceTriangulationEndpointFactsW902
    (leaves : MetrizableWppClosedMapBoundaryDataSourceTriangulationEndpointFactsLeavesW902) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfClosedMapSourceTriangulationEndpointFactsW901
    (closedMapSourceTriangulationEndpointFactsLeavesOfBoundaryDataW902 leaves)

theorem directBoundedLeftCalculusOfClosedMapBoundaryDataSourceTriangulationEndpointFactsW902
    (leaves : MetrizableWppClosedMapBoundaryDataSourceTriangulationEndpointFactsLeavesW902) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapSourceTriangulationEndpointFactsW901
    (closedMapSourceTriangulationEndpointFactsLeavesOfBoundaryDataW902 leaves)

noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapBoundaryDataSourceTriangulationEndpointFactsW902
    (leaves : MetrizableWppClosedMapBoundaryDataSourceTriangulationEndpointFactsLeavesW902) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapSourceTriangulationEndpointFactsW901
    (closedMapSourceTriangulationEndpointFactsLeavesOfBoundaryDataW902 leaves)

/-- W902 exposes W901's fields with WPP boundary data bundled through W716. -/
def closedMapBoundaryDataSourceTriangulationEndpointFactsInputNamesW902 :
    List String :=
  ["W716 bundled WPP right-open/source-pi-zero boundary data provider",
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

theorem closedMapBoundaryDataSourceTriangulationEndpointFactsInputNamesW902_count :
    closedMapBoundaryDataSourceTriangulationEndpointFactsInputNamesW902.length =
      30 :=
  rfl

/-- Current checked W902 state. -/
structure MetrizableClosedMapBoundaryDataSourceTriangulationEndpointFactsRouteStateW902 :
    Type where
  seed : String
  declarations : List String
  boundaryDataResult : String
  exactAtResult : String
  removedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedMapBoundaryDataSourceTriangulationEndpointFactsRouteStateW902 :
    MetrizableClosedMapBoundaryDataSourceTriangulationEndpointFactsRouteStateW902
    where
  seed :=
    "w902-closed-map-boundary-data-source-triangulation-endpoint-facts-localized-right-adjoint"
  declarations :=
    ["MetrizableWppClosedMapBoundaryDataSourceTriangulationEndpointFactsLeavesW902",
      "rightOpenBoundaryOfBoundaryDataW902",
      "sourcePiZeroBoundaryOfBoundaryDataW902",
      "closedMapSourceTriangulationEndpointFactsLeavesOfBoundaryDataW902",
      "concreteLeavesOfClosedMapBoundaryDataSourceTriangulationEndpointFactsW902",
      "routeDataProviderOfClosedMapBoundaryDataSourceTriangulationEndpointFactsW902",
      "directBoundedLeftCalculusOfClosedMapBoundaryDataSourceTriangulationEndpointFactsW902",
      "boundedDerivedInfinityCategoryOfClosedMapBoundaryDataSourceTriangulationEndpointFactsW902",
      "closedMapBoundaryDataSourceTriangulationEndpointFactsInputNamesW902",
      "closedMapBoundaryDataSourceTriangulationEndpointFactsInputNamesW902_count"]
  boundaryDataResult :=
    "proved: W716 boundary data supplies W901's right-open and\
      source-pi-zero boundary fields"
  exactAtResult :=
    "proved: closed-map boundary-data source-triangulation endpoint-facts\
      fields feed the W901 stable ExactAt route"
  removedInputs :=
    ["WPP right-open quotient-cover boundary data",
      "WPP source-pi-zero boundary data"]
  remainingInputs :=
    closedMapBoundaryDataSourceTriangulationEndpointFactsInputNamesW902
  productSuccessClaimed := false

theorem currentW902ClosedMapBoundaryDataSourceTriangulationEndpointFactsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedMapBoundaryDataSourceTriangulationEndpointFactsRouteStateW902;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
