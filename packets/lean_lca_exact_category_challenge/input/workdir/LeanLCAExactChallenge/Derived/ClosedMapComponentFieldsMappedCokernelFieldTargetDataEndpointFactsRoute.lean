import LeanLCAExactChallenge.Derived.ClosedMapMappedCokernelFieldTargetDataEndpointFactsRoute

/-!
W906 feeds the W905 closed-map mapped-cokernel-field target-data
relation-data boundary-data source-triangulation endpoint-facts localized
right-adjoint route while exposing the W718 selected-difference closed-map
component provider as its three W714 diagram component fields.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W906 assembles the W718 closed-map component provider from its fields. -/
def closedMapDiagramComponentProviderOfFieldsW906
    (closedMapPi1 : SelectedDifferenceClosedMapPi1DiagramFieldW714)
    (closedMapPi2 : SelectedDifferenceClosedMapPi2DiagramFieldW714)
    (closedMapPi3 : SelectedDifferenceClosedMapPi3DiagramFieldW714) :
    SelectedDifferenceClosedMapDiagramComponentProviderW718 where
  pi1 := closedMapPi1
  pi2 := closedMapPi2
  pi3 := closedMapPi3

/--
W906 replaces W905's W718 selected-difference closed-map component provider
with the three diagram component fields it packages.
-/
structure MetrizableWppClosedMapComponentFieldsMappedCokernelFieldTargetDataLeavesW906 :
    Type 2 where
  boundaryData :
    MetrizableWppLimitBoundaryDataW716
  relationData :
    ClosedNatTransOrdinaryRelationDataProviderW717
  targetSurjectiveCompactForTargetProvider :
    TargetSurjectiveCompactForTargetProviderW715
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

/-- W906 projects W905 leaves from the three closed-map component fields. -/
def w905LeavesOfClosedMapComponentFieldsW906
    (leaves :
      MetrizableWppClosedMapComponentFieldsMappedCokernelFieldTargetDataLeavesW906) :
    MetrizableWppClosedMapMappedCokernelFieldTargetDataLeavesW905
    where
  boundaryData := leaves.boundaryData
  relationData := leaves.relationData
  targetSurjectiveCompactForTargetProvider :=
    leaves.targetSurjectiveCompactForTargetProvider
  globalClosedMapComponents :=
    closedMapDiagramComponentProviderOfFieldsW906 leaves.closedMapPi1
      leaves.closedMapPi2 leaves.closedMapPi3
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

/-- W906 W733 concrete leaves after projecting W905 leaves. -/
def concreteLeavesOfClosedMapComponentFieldsMappedCokernelFieldTargetDataW906
    (leaves :
      MetrizableWppClosedMapComponentFieldsMappedCokernelFieldTargetDataLeavesW906) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfClosedMapMappedCokernelFieldTargetDataW905
    (w905LeavesOfClosedMapComponentFieldsW906 leaves)

/-- W906 W732 route data after projecting W905 leaves. -/
def routeDataProviderOfClosedMapComponentFieldsMappedCokernelFieldTargetDataW906
    (leaves :
      MetrizableWppClosedMapComponentFieldsMappedCokernelFieldTargetDataLeavesW906) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfClosedMapMappedCokernelFieldTargetDataW905
    (w905LeavesOfClosedMapComponentFieldsW906 leaves)

theorem directBoundedLeftCalculusOfClosedMapComponentFieldsMappedCokernelFieldTargetDataW906
    (leaves :
      MetrizableWppClosedMapComponentFieldsMappedCokernelFieldTargetDataLeavesW906) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapMappedCokernelFieldTargetDataW905
    (w905LeavesOfClosedMapComponentFieldsW906 leaves)

noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapComponentFieldsMappedCokernelFieldTargetDataW906
    (leaves :
      MetrizableWppClosedMapComponentFieldsMappedCokernelFieldTargetDataLeavesW906) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapMappedCokernelFieldTargetDataW905
    (w905LeavesOfClosedMapComponentFieldsW906 leaves)

/-- W906 exposes W905's W718 provider as its three diagram fields. -/
def closedMapComponentFieldsMappedCokernelFieldTargetDataInputNamesW906 :
    List String :=
  ["W716 bundled WPP right-open/source-pi-zero boundary data provider",
    "W717 bundled closed natural transformation ordinary relation data provider",
    "W715 bundled target-difference surjectivity and target-codomain compactness provider",
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

theorem closedMapComponentFieldsMappedCokernelFieldTargetDataInputNamesW906_count :
    closedMapComponentFieldsMappedCokernelFieldTargetDataInputNamesW906.length =
      30 :=
  rfl

/-- Current checked W906 state. -/
structure MetrizableClosedMapComponentFieldsMappedCokernelFieldTargetDataRouteStateW906 :
    Type where
  seed : String
  declarations : List String
  componentFieldResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedMapComponentFieldsMappedCokernelFieldTargetDataRouteStateW906 :
    MetrizableClosedMapComponentFieldsMappedCokernelFieldTargetDataRouteStateW906
    where
  seed :=
    "w906-closed-map-component-fields-mapped-cokernel-field-target-data-\
      relation-data-boundary-data-source-triangulation-endpoint-facts-\
      localized-right-adjoint"
  declarations :=
    ["MetrizableWppClosedMapComponentFieldsMappedCokernelFieldTargetDataLeavesW906",
      "closedMapDiagramComponentProviderOfFieldsW906",
      "w905LeavesOfClosedMapComponentFieldsW906",
      "concreteLeavesOfClosedMapComponentFieldsMappedCokernelFieldTargetDataW906",
      "routeDataProviderOfClosedMapComponentFieldsMappedCokernelFieldTargetDataW906",
      "directBoundedLeftCalculusOfClosedMapComponentFieldsMappedCokernelFieldTargetDataW906",
      "boundedDerivedInfinityCategoryOfClosedMapComponentFieldsMappedCokernelFieldTargetDataW906",
      "closedMapComponentFieldsMappedCokernelFieldTargetDataInputNamesW906",
      "closedMapComponentFieldsMappedCokernelFieldTargetDataInputNamesW906_count"]
  componentFieldResult :=
    "proved: the three selected-difference W714 closed-map diagram component\
      fields supply W905's W718 closed-map component provider"
  exactAtResult :=
    "proved: closed-map component-fields mapped-cokernel-field target-data\
      relation-data boundary-data source-triangulation endpoint-facts fields\
      feed the W905 stable ExactAt route"
  refinedInputs :=
    ["W718 selected-difference closed-map diagram component provider"]
  remainingInputs :=
    closedMapComponentFieldsMappedCokernelFieldTargetDataInputNamesW906
  productSuccessClaimed := false

theorem currentW906ClosedMapComponentFieldsMappedCokernelFieldTargetDataRoute_productSuccess :
    (let state :=
        currentMetrizableClosedMapComponentFieldsMappedCokernelFieldTargetDataRouteStateW906;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
