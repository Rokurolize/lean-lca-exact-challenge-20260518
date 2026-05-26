import LeanLCAExactChallenge.Derived.ClosedMapTargetSurjectiveCompactRelationDataBoundaryDataSourceTriangulationEndpointFactsLocalizedRightAdjointComparisonStableExactAtRoute

/-!
W905 feeds the W904 closed-map target-data relation-data boundary-data
source-triangulation endpoint-facts localized right-adjoint comparison
stable-ExactAt route while exposing the W519 mapped-cokernel closed-map
provider as its raw `IsClosedMap` field.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

/-- W905 assembles the W519 mapped-cokernel closed-map provider from its field. -/
def mappedCokernelClosedMapProviderOfFieldW905
    (mappedCokernelClosedMap :
      ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y), IsClosedMap (f : X → Y)) :
    MappedExplicitCokernelClosedMapProviderW519 where
  isClosedMap := mappedCokernelClosedMap

/--
W905 replaces W904's W519 mapped-cokernel closed-map provider with the raw
closed-map field it packages.
-/
structure MetrizableWppClosedMapMappedCokernelFieldTargetDataLeavesW905 :
    Type 2 where
  boundaryData :
    MetrizableWppLimitBoundaryDataW716
  relationData :
    ClosedNatTransOrdinaryRelationDataProviderW717
  targetSurjectiveCompactForTargetProvider :
    TargetSurjectiveCompactForTargetProviderW715
  globalClosedMapComponents :
    SelectedDifferenceClosedMapDiagramComponentProviderW718
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

/-- W905 projects W904 leaves from the raw mapped-cokernel closed-map field. -/
def w904LeavesOfMappedCokernelFieldW905
    (leaves :
      MetrizableWppClosedMapMappedCokernelFieldTargetDataLeavesW905) :
    MetrizableWppClosedMapTargetDataEndpointFactsLeavesW904
    where
  boundaryData := leaves.boundaryData
  relationData := leaves.relationData
  targetSurjectiveCompactForTargetProvider :=
    leaves.targetSurjectiveCompactForTargetProvider
  globalClosedMapComponents := leaves.globalClosedMapComponents
  mappedCokernelClosedMapProvider :=
    mappedCokernelClosedMapProviderOfFieldW905 leaves.mappedCokernelClosedMap
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

/-- W905 W733 concrete leaves after projecting W904 leaves. -/
def concreteLeavesOfClosedMapMappedCokernelFieldTargetDataW905
    (leaves :
      MetrizableWppClosedMapMappedCokernelFieldTargetDataLeavesW905) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfClosedMapTargetDataEndpointFactsW904
    (w904LeavesOfMappedCokernelFieldW905 leaves)

/-- W905 W732 route data after projecting W904 leaves. -/
def routeDataProviderOfClosedMapMappedCokernelFieldTargetDataW905
    (leaves :
      MetrizableWppClosedMapMappedCokernelFieldTargetDataLeavesW905) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfClosedMapTargetDataEndpointFactsW904
    (w904LeavesOfMappedCokernelFieldW905 leaves)

theorem directBoundedLeftCalculusOfClosedMapMappedCokernelFieldTargetDataW905
    (leaves :
      MetrizableWppClosedMapMappedCokernelFieldTargetDataLeavesW905) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapTargetDataEndpointFactsW904
    (w904LeavesOfMappedCokernelFieldW905 leaves)

noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapMappedCokernelFieldTargetDataW905
    (leaves :
      MetrizableWppClosedMapMappedCokernelFieldTargetDataLeavesW905) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapTargetDataEndpointFactsW904
    (w904LeavesOfMappedCokernelFieldW905 leaves)

/-- W905 exposes W904's W519 provider as its raw closed-map field. -/
def closedMapMappedCokernelFieldTargetDataInputNamesW905 :
    List String :=
  ["W716 bundled WPP right-open/source-pi-zero boundary data provider",
    "W717 bundled closed natural transformation ordinary relation data provider",
    "W715 bundled target-difference surjectivity and target-codomain compactness provider",
    "selected-difference closed-map diagram component provider",
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

theorem closedMapMappedCokernelFieldTargetDataInputNamesW905_count :
    closedMapMappedCokernelFieldTargetDataInputNamesW905.length =
      28 :=
  rfl

/-- Current checked W905 state. -/
structure MetrizableClosedMapMappedCokernelFieldTargetDataRouteStateW905 :
    Type where
  seed : String
  declarations : List String
  mappedCokernelFieldResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedMapMappedCokernelFieldTargetDataRouteStateW905 :
    MetrizableClosedMapMappedCokernelFieldTargetDataRouteStateW905
    where
  seed :=
    "w905-closed-map-mapped-cokernel-field-target-data-relation-data-\
      boundary-data-source-triangulation-endpoint-facts-localized-right-adjoint"
  declarations :=
    ["MetrizableWppClosedMapMappedCokernelFieldTargetDataLeavesW905",
      "mappedCokernelClosedMapProviderOfFieldW905",
      "w904LeavesOfMappedCokernelFieldW905",
      "concreteLeavesOfClosedMapMappedCokernelFieldTargetDataW905",
      "routeDataProviderOfClosedMapMappedCokernelFieldTargetDataW905",
      "directBoundedLeftCalculusOfClosedMapMappedCokernelFieldTargetDataW905",
      "boundedDerivedInfinityCategoryOfClosedMapMappedCokernelFieldTargetDataW905",
      "closedMapMappedCokernelFieldTargetDataInputNamesW905",
      "closedMapMappedCokernelFieldTargetDataInputNamesW905_count"]
  mappedCokernelFieldResult :=
    "proved: the raw mapped-cokernel IsClosedMap field supplies W904's\
      W519 mapped-cokernel closed-map provider"
  exactAtResult :=
    "proved: closed-map mapped-cokernel-field target-data relation-data\
      boundary-data source-triangulation endpoint-facts fields feed the\
      W904 stable ExactAt route"
  refinedInputs :=
    ["W519 mapped explicit cokernel closed-map provider"]
  remainingInputs :=
    closedMapMappedCokernelFieldTargetDataInputNamesW905
  productSuccessClaimed := false

theorem currentW905ClosedMapMappedCokernelFieldTargetDataRoute_productSuccess :
    (let state :=
        currentMetrizableClosedMapMappedCokernelFieldTargetDataRouteStateW905;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
