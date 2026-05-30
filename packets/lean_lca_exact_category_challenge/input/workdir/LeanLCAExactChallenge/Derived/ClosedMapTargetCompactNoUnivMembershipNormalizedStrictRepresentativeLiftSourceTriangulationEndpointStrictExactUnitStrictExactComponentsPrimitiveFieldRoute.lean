import LeanLCAExactChallenge.Derived.ClosedMapTargetCompactNoUnivMembershipSourceTriangulationDataEndpointStrictExactUnitStrictExactComponentsPrimitiveFieldRoute

/-!
W940 feeds the W939/W937 closed-map target-compact endpoint-strict-exact
unit-strict-exact-components route while replacing the raw strict-preimage
object, map, coherence, and source-image normalization fields by the existing
normalized strict-representative lift blueprint from `BoundedFiniteProducts`.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology
open DirectWppLimitFiniteShapeTransfer
open WppOpW426W318LegCompatibilityAlignmentV370SupportW439
open WppOpSelectedW461TransportedPointIsoProviderV370SupportW506
open WppOpClosedNatTransOrdinaryRelationTopologyV370SupportW511
open WppOpClosedNatTransOrdinaryRelationFieldsV370SupportW512
open WppOpW461BridgeComponentwiseClosedRangeProjectionV370SupportW481
open WppOpClosedRangeOnlyComponentwiseProjectionV370SupportW484

namespace Dbounded

/--
W940 preserves W939's source-triangulation, endpoint strict short-exact, and
unit mapping-cone strict component fields, while requiring the strict
representative lift through the existing normalized blueprint boundary.
-/
structure MetrizableWppClosedMapTargetCompactNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW940 :
    Type 2 where
  rightOpenBoundary :
    ∀ (X Y : WalkingParallelPair ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
      (cx : Cone X) (cy : Cone Y) (φ : cx.pt ⟶ cy.pt),
        IsLimit cx →
          IsLimit cy →
            (∀ j : WalkingParallelPair,
              IsOpenMap (α.app j : X.obj j → Y.obj j)) →
              (∀ j : WalkingParallelPair,
                φ ≫ cy.π.app j = cx.π.app j ≫ α.app j) →
                Nonempty
                  (WppLimitLcaClosedQuotientCoverData X Y α cx cy φ)
  sourcePiZeroBoundary :
    ∀ (X : WalkingParallelPair ⥤ MetrizableLCA.{0}) (cx : Cone X),
      IsLimit cx →
        let δ : X.obj WalkingParallelPair.zero ⟶ X.obj WalkingParallelPair.one :=
          X.map WalkingParallelPairHom.left - X.map WalkingParallelPairHom.right
        IsOpenMap (δ : X.obj WalkingParallelPair.zero → X.obj WalkingParallelPair.one) ∧
          MetrizableLCA.cokernelπ δ = 0
  relationPullbackProvider :
    ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y),
      (∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
        relationPullbackPrimitiveW920 α
  targetRelationLiftsProvider :
    ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y),
      (∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
        targetRelationLiftsPrimitiveW920 α
  targetDifferenceSurjectiveForTargetProvider :
    ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}),
      targetDifferenceSurjectivePrimitiveW923 Y
  targetCodomainCompactSpaceProvider :
    ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}),
      targetCodomainCompactNoUnivMembershipPrimitiveW930 Y
  closedMapPi1 :
    ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}),
      selectedDifferenceClosedMapPi1PrimitiveW922 S
  closedMapPi2 :
    ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}),
      selectedDifferenceClosedMapPi2PrimitiveW922 S
  closedMapPi3 :
    ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}),
      selectedDifferenceClosedMapPi3PrimitiveW922 S
  mappedCokernelClosedMap :
    ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
      mappedCokernelClosedMapPrimitiveW921 f
  normalizedStrictRepresentativeLiftBlueprint :
    Dbounded.MetrizableWalkingParallelPairNormalizedLiftBlueprint
  targetFixedTargetUniq :
    Dbounded.MetrizableWalkingParallelPairFixedTargetUniqObligation
      (WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0})
  localizationModelFixedTargetUniq :
    Dbounded.MetrizableWalkingParallelPairFixedTargetUniqObligation
      (((boundedExactWeakEquivalence MetrizableLCA.{0}).functorCategory
        WalkingParallelPair).Localization)
  sourceTriangulationData :
    MetrizableWppSourceTriangulationDataProviderW722
  endpointStrictExact :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i)
  boundedHomotopyLocalizedRightAdjoint :
    MorphismProperty.Localization
        ((exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).trW) ⥤
      BoundedComplexCategory MetrizableLCA.{0}
  boundedHomotopyLocalizedAdjunction :
    boundedHomotopyLocalizedVerdierFunctor MetrizableLCA.{0} ⊣
      boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents :
    boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponentsPrimitiveW939
      boundedHomotopyLocalizedRightAdjoint
      boundedHomotopyLocalizedAdjunction

/--
W940 projects W937 leaves from normalized strict-representative lift data,
W722 source-triangulation data, and the endpoint strict-exact field.
-/
def w937LeavesOfNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW940
    (leaves :
      MetrizableWppClosedMapTargetCompactNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW940) :
    MetrizableWppClosedMapTargetCompactEndpointShortExactUnitStrictExactComponentsFieldLeavesW937
    where
  rightOpenBoundary := leaves.rightOpenBoundary
  sourcePiZeroBoundary := leaves.sourcePiZeroBoundary
  relationPullbackProvider := leaves.relationPullbackProvider
  targetRelationLiftsProvider := leaves.targetRelationLiftsProvider
  targetDifferenceSurjectiveForTargetProvider :=
    leaves.targetDifferenceSurjectiveForTargetProvider
  targetCodomainCompactSpaceProvider :=
    leaves.targetCodomainCompactSpaceProvider
  closedMapPi1 := leaves.closedMapPi1
  closedMapPi2 := leaves.closedMapPi2
  closedMapPi3 := leaves.closedMapPi3
  mappedCokernelClosedMap := leaves.mappedCokernelClosedMap
  strictPreimageZeroSrc := fun Y =>
    (leaves.normalizedStrictRepresentativeLiftBlueprint.blueprint.objData Y).zeroSrc
  strictPreimageOneSrc := fun Y =>
    (leaves.normalizedStrictRepresentativeLiftBlueprint.blueprint.objData Y).oneSrc
  strictPreimageZeroIso := fun Y =>
    (leaves.normalizedStrictRepresentativeLiftBlueprint.blueprint.objData Y).zeroIso
  strictPreimageOneIso := fun Y =>
    (leaves.normalizedStrictRepresentativeLiftBlueprint.blueprint.objData Y).oneIso
  strictPreimageLeftSrc := fun Y =>
    (leaves.normalizedStrictRepresentativeLiftBlueprint.blueprint.objData Y).leftSrc
  strictPreimageRightSrc := fun Y =>
    (leaves.normalizedStrictRepresentativeLiftBlueprint.blueprint.objData Y).rightSrc
  strictPreimageLeftFac := fun Y =>
    (leaves.normalizedStrictRepresentativeLiftBlueprint.blueprint.objData Y).left_fac
  strictPreimageRightFac := fun Y =>
    (leaves.normalizedStrictRepresentativeLiftBlueprint.blueprint.objData Y).right_fac
  strictPreimageZeroMap := fun {Y Z} τ =>
    (leaves.normalizedStrictRepresentativeLiftBlueprint.blueprint.mapData
      (Y := Y) (Z := Z) τ).zeroMap
  strictPreimageOneMap := fun {Y Z} τ =>
    (leaves.normalizedStrictRepresentativeLiftBlueprint.blueprint.mapData
      (Y := Y) (Z := Z) τ).oneMap
  strictPreimageZeroMapFac := fun {Y Z} τ =>
    (leaves.normalizedStrictRepresentativeLiftBlueprint.blueprint.mapData
      (Y := Y) (Z := Z) τ).zero_fac
  strictPreimageOneMapFac := fun {Y Z} τ =>
    (leaves.normalizedStrictRepresentativeLiftBlueprint.blueprint.mapData
      (Y := Y) (Z := Z) τ).one_fac
  strictPreimageLeftNaturality := fun {Y Z} τ =>
    (leaves.normalizedStrictRepresentativeLiftBlueprint.blueprint.mapData
      (Y := Y) (Z := Z) τ).left_naturality
  strictPreimageRightNaturality := fun {Y Z} τ =>
    (leaves.normalizedStrictRepresentativeLiftBlueprint.blueprint.mapData
      (Y := Y) (Z := Z) τ).right_naturality
  strictRepresentativeMapId := by
    intro Y
    simpa [strictPreimageMapDataOfFieldsW892, strictPreimageObjectDataOfFieldsW891]
      using leaves.normalizedStrictRepresentativeLiftBlueprint.blueprint.map_id Y
  strictRepresentativeMapComp := by
    intro Y Z T τ σ
    simpa [strictPreimageMapDataOfFieldsW892, strictPreimageObjectDataOfFieldsW891]
      using leaves.normalizedStrictRepresentativeLiftBlueprint.blueprint.map_comp
        (Y := Y) (Z := Z) (T := T) τ σ
  sourceImageObjectNormalization := by
    intro X
    simpa [strictPreimageObjectDataOfFieldsW891]
      using leaves.normalizedStrictRepresentativeLiftBlueprint.obj_image X
  sourceImageMapNormalization := by
    intro X Y τ
    simpa [strictPreimageMapDataOfFieldsW892, strictPreimageObjectDataOfFieldsW891]
      using leaves.normalizedStrictRepresentativeLiftBlueprint.map_image
        (X := X) (Y := Y) τ
  targetFixedTargetUniq := leaves.targetFixedTargetUniq
  localizationModelFixedTargetUniq :=
    leaves.localizationModelFixedTargetUniq
  sourcePretriangulated :=
    sourcePretriangulated_of_sourceTriangulationDataW722
      leaves.sourceTriangulationData
  sourceTriangulated :=
    sourceTriangulated_of_sourceTriangulationDataW722
      leaves.sourceTriangulationData
  triangleCompletion :=
    triangleCompletion_of_sourceTriangulationDataW722
      leaves.sourceTriangulationData
  endpointClosedEmbedding := fun K i => (leaves.endpointStrictExact K i).closed_inclusion
  endpointOpenMap := fun K i => (leaves.endpointStrictExact K i).open_map
  endpointShortExactOfExactAt :=
    endpointShortExactOfEndpointStrictExactPrimitiveW939 leaves.endpointStrictExact
  boundedHomotopyLocalizedRightAdjoint :=
    leaves.boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedAdjunction :=
    leaves.boundedHomotopyLocalizedAdjunction
  boundedHomotopyLocalizedEndpointShortExactUnitStrictExactComponents :=
    leaves.boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents

/-- W940 W733 concrete leaves after projecting W937 leaves. -/
def concreteLeavesOfClosedMapTargetCompactNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW940
    (leaves :
      MetrizableWppClosedMapTargetCompactNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW940) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfClosedMapTargetCompactEndpointShortExactUnitStrictExactComponentsFieldsW937
    (w937LeavesOfNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW940
      leaves)

/-- W940 W732 route data after projecting W937 leaves. -/
def routeDataProviderOfClosedMapTargetCompactNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW940
    (leaves :
      MetrizableWppClosedMapTargetCompactNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW940) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfClosedMapTargetCompactEndpointShortExactUnitStrictExactComponentsFieldsW937
    (w937LeavesOfNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW940
      leaves)

theorem
    directBoundedLeftCalculusOfClosedMapTargetCompactNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW940
    (leaves :
      MetrizableWppClosedMapTargetCompactNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW940) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapTargetCompactEndpointShortExactUnitStrictExactComponentsFieldsW937
    (w937LeavesOfNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW940
      leaves)

noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapTargetCompactNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW940
    (leaves :
      MetrizableWppClosedMapTargetCompactNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW940) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapTargetCompactEndpointShortExactUnitStrictExactComponentsFieldsW937
    (w937LeavesOfNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW940
      leaves)

/--
W940 exposes the strict-representative object/map/coherence/normalization
cluster as one normalized lift blueprint while retaining W939's source and
endpoint strict fields.
-/
def closedMapTargetCompactNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW940 :
    List String :=
  ["raw right-open closed-quotient-cover WPP-limit boundary proposition",
    "raw source-difference cokernel-pi-zero WPP-limit boundary proposition",
    "primitive relation-pullback AddSubgroup comap equality",
    "primitive target-relation lift quantifier through the codomain component",
    "primitive target-difference preimage quantifier for every target diagram",
    "primitive target-codomain compactness filter nonbottom and point meet nonbottom\
      for every target diagram",
    "primitive selected-difference pi1 closed-set image condition",
    "primitive selected-difference pi2 closed-set image condition",
    "primitive selected-difference pi3 closed-set image condition",
    "primitive mapped explicit cokernel closed-set image condition for every morphism",
    "normalized strict-representative lift blueprint: object data, map data,\
      identity and composition coherence, and source-image normalization",
    "target fixed-target uniqueness quantifier for objectwise localization",
    "localization-model fixed-target uniqueness quantifier for objectwise localization",
    "bundled W722 source-triangulation data provider: pretriangulated,\
      triangulated, and source-side triangle-completion data",
    "endpoint strict short-exact witnesses for closed embeddings, open maps,\
      and outgoing epi data",
    "right adjoint to the bounded homotopy localized Verdier functor",
    "adjunction for the bounded homotopy localized Verdier functor",
    "unit mapping-cone iso-closure witness: degreewise strict components\
      (closed inclusion, open map, surjectivity, algebraic exactness) plus\
      isomorphism"]

theorem closedMapTargetCompactNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW940_count :
    closedMapTargetCompactNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW940.length =
      18 :=
  rfl

/-- Current checked W940 state. -/
structure MetrizableClosedMapTargetCompactNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsRouteStateW940 :
    Type where
  seed : String
  declarations : List String
  normalizedLiftBlueprintResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedMapTargetCompactNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsRouteStateW940 :
    MetrizableClosedMapTargetCompactNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsRouteStateW940
    where
  seed :=
    "w940-closed-map-target-compact-no-univ-membership-normalized-strict-\
      representative-lift-source-triangulation-endpoint-strict-exact-unit-\
      strict-exact-components-primitive-field-route"
  declarations :=
    ["MetrizableWppClosedMapTargetCompactNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW940",
      "w937LeavesOfNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW940",
      "concreteLeavesOfClosedMapTargetCompactNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW940",
      "routeDataProviderOfClosedMapTargetCompactNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW940",
      "directBoundedLeftCalculusOfClosedMapTargetCompactNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW940",
      "boundedDerivedInfinityCategoryOfClosedMapTargetCompactNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW940",
      "closedMapTargetCompactNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW940",
      "closedMapTargetCompactNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW940_count"]
  normalizedLiftBlueprintResult :=
    "proved: the existing normalized strict-representative lift blueprint\
      supplies W937's strict preimage object data, map data, identity and\
      composition coherence, and source-image object/map normalization fields"
  exactAtResult :=
    "proved: closed-map target-compact-no-univ-membership-normalized-strict-\
      representative-lift-source-triangulation-data-endpoint-strict-exact-\
      unit-strict-exact-components route feeds the W937/W936/W935/W934/W933/\
      W932/W931/W930 stable ExactAt route"
  refinedInputs :=
    ["strict preimage object source, object localization isomorphism,\
      source-map, and localization-factorization leaves replaced by the\
      normalized strict-representative lift blueprint",
      "strict preimage component maps, map factorizations, and naturality\
      leaves replaced by the normalized strict-representative lift blueprint",
      "strict-representative identity, composition, and source-image\
      normalization leaves replaced by the normalized strict-representative\
      lift blueprint",
      "raw source Pretriangulated, IsTriangulated, and triangle-completion\
      leaves remain consolidated into the W722 source-triangulation data\
      provider",
      "endpoint closed-embedding, open-map, and ShortExact leaves remain\
      consolidated into one endpoint strict MetrizableLCA short exact witness"]
  remainingInputs :=
    closedMapTargetCompactNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW940
  productSuccessClaimed := false

theorem currentW940ClosedMapTargetCompactNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedMapTargetCompactNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsRouteStateW940;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
