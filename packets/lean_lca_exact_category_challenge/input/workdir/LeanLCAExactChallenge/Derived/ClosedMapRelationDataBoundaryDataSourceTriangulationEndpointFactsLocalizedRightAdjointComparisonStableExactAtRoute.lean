import LeanLCAExactChallenge.Derived.ClosedMapBoundaryDataSourceTriangulationEndpointFactsLocalizedRightAdjointComparisonStableExactAtRoute

/-!
W903 feeds the W902 closed-map boundary-data source-triangulation endpoint-facts
localized right-adjoint comparison stable-ExactAt route while bundling the two
closed natural transformation relation providers through the existing W717
provider.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

/-- W903 projects the relation-pullback provider from W717 data. -/
def relationPullbackProviderOfRelationDataW903
    (relationData : ClosedNatTransOrdinaryRelationDataProviderW717) :
    ClosedNatTransOrdinaryRelationPullbackProviderW712 :=
  relationPullbackProvider_of_relationDataW717 relationData

/-- W903 projects the target-relation-lift provider from W717 data. -/
def targetRelationLiftsProviderOfRelationDataW903
    (relationData : ClosedNatTransOrdinaryRelationDataProviderW717) :
    ClosedNatTransOrdinaryTargetRelationLiftsProviderW712 :=
  targetRelationLiftsProvider_of_relationDataW717 relationData

/--
W903 replaces W902's separate closed-natural-transformation relation fields
with the existing W717 relation-data provider.
-/
structure MetrizableWppClosedMapRelationDataBoundaryEndpointFactsLeavesW903 :
    Type 2 where
  boundaryData :
    MetrizableWppLimitBoundaryDataW716
  relationData :
    ClosedNatTransOrdinaryRelationDataProviderW717
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

/-- W903 projects W902 leaves from the W717 relation-data provider. -/
def closedMapBoundaryEndpointFactsLeavesOfRelationDataW903
    (leaves :
      MetrizableWppClosedMapRelationDataBoundaryEndpointFactsLeavesW903) :
    MetrizableWppClosedMapBoundaryDataSourceTriangulationEndpointFactsLeavesW902
    where
  boundaryData := leaves.boundaryData
  relationPullbackProvider :=
    relationPullbackProviderOfRelationDataW903 leaves.relationData
  targetRelationLiftsProvider :=
    targetRelationLiftsProviderOfRelationDataW903 leaves.relationData
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

/-- W903 W733 concrete leaves after projecting W902 leaves. -/
def concreteLeavesOfClosedMapRelationDataBoundaryEndpointFactsW903
    (leaves :
      MetrizableWppClosedMapRelationDataBoundaryEndpointFactsLeavesW903) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfClosedMapBoundaryDataSourceTriangulationEndpointFactsW902
    (closedMapBoundaryEndpointFactsLeavesOfRelationDataW903 leaves)

/-- W903 W732 route data after projecting W902 leaves. -/
def routeDataProviderOfClosedMapRelationDataBoundaryEndpointFactsW903
    (leaves :
      MetrizableWppClosedMapRelationDataBoundaryEndpointFactsLeavesW903) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfClosedMapBoundaryDataSourceTriangulationEndpointFactsW902
    (closedMapBoundaryEndpointFactsLeavesOfRelationDataW903 leaves)

theorem
    directBoundedLeftCalculusOfClosedMapRelationDataBoundaryEndpointFactsW903
    (leaves :
      MetrizableWppClosedMapRelationDataBoundaryEndpointFactsLeavesW903) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapBoundaryDataSourceTriangulationEndpointFactsW902
    (closedMapBoundaryEndpointFactsLeavesOfRelationDataW903 leaves)

noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapRelationDataBoundaryEndpointFactsW903
    (leaves :
      MetrizableWppClosedMapRelationDataBoundaryEndpointFactsLeavesW903) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapBoundaryDataSourceTriangulationEndpointFactsW902
    (closedMapBoundaryEndpointFactsLeavesOfRelationDataW903 leaves)

/-- W903 exposes W902's fields with relation data bundled through W717. -/
def closedMapRelationDataBoundaryEndpointFactsInputNamesW903 :
    List String :=
  ["W716 bundled WPP right-open/source-pi-zero boundary data provider",
    "W717 bundled closed natural transformation ordinary relation data provider",
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

theorem closedMapRelationDataBoundaryEndpointFactsInputNamesW903_count :
    closedMapRelationDataBoundaryEndpointFactsInputNamesW903.length =
      29 :=
  rfl

/-- Current checked W903 state. -/
structure MetrizableClosedMapRelationDataBoundaryEndpointFactsRouteStateW903 :
    Type where
  seed : String
  declarations : List String
  relationDataResult : String
  exactAtResult : String
  removedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedMapRelationDataBoundaryEndpointFactsRouteStateW903 :
    MetrizableClosedMapRelationDataBoundaryEndpointFactsRouteStateW903
    where
  seed :=
    "w903-closed-map-relation-data-boundary-data-source-triangulation-\
      endpoint-facts-localized-right-adjoint"
  declarations :=
    ["MetrizableWppClosedMapRelationDataBoundaryEndpointFactsLeavesW903",
      "relationPullbackProviderOfRelationDataW903",
      "targetRelationLiftsProviderOfRelationDataW903",
      "closedMapBoundaryEndpointFactsLeavesOfRelationDataW903",
      "concreteLeavesOfClosedMapRelationDataBoundaryEndpointFactsW903",
      "routeDataProviderOfClosedMapRelationDataBoundaryEndpointFactsW903",
      "directBoundedLeftCalculusOfClosedMapRelationDataBoundaryEndpointFactsW903",
      "boundedDerivedInfinityCategoryOfClosedMapRelationDataBoundaryEndpointFactsW903",
      "closedMapRelationDataBoundaryEndpointFactsInputNamesW903",
      "closedMapRelationDataBoundaryEndpointFactsInputNamesW903_count"]
  relationDataResult :=
    "proved: W717 relation data supplies W902's relation-pullback and\
      target-relation-lift provider fields"
  exactAtResult :=
    "proved: closed-map relation-data boundary-data source-triangulation\
      endpoint-facts fields feed the W902 stable ExactAt route"
  removedInputs :=
    ["closed natural transformation relation-pullback provider",
      "closed natural transformation target-relation-lift provider"]
  remainingInputs :=
    closedMapRelationDataBoundaryEndpointFactsInputNamesW903
  productSuccessClaimed := false

theorem
    currentW903ClosedMapRelationDataBoundaryEndpointFactsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedMapRelationDataBoundaryEndpointFactsRouteStateW903;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
