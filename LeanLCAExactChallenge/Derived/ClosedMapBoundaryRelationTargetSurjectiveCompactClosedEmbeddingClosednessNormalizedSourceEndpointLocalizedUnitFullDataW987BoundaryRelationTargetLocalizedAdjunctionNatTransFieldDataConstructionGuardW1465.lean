import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionGuardW1464

/-!
W1465 refines W1464 by constructing the localized-adjunction unit and counit
natural transformations from component maps and naturality proofs, then running
the resulting data through the W1464 W987 construction.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace Dbounded

noncomputable section

/-- W1465 constructs the localized-adjunction unit from component maps. -/
def localizedAdjunctionUnitOfW1465
    (boundedHomotopyLocalizedRightAdjoint :
      BoundedHomotopyLocalizedCategoryW1461 ⥤
        BoundedComplexCategory MetrizableLCA.{0})
    (unitApp :
      ∀ X : BoundedComplexCategory MetrizableLCA.{0},
        X ⟶
          (boundedHomotopyLocalizedVerdierFunctorW1461 ⋙
            boundedHomotopyLocalizedRightAdjoint).obj X)
    (unitNaturality :
      ∀ {X Y : BoundedComplexCategory MetrizableLCA.{0}} (f : X ⟶ Y),
        f ≫ unitApp Y =
          unitApp X ≫
            (boundedHomotopyLocalizedVerdierFunctorW1461 ⋙
              boundedHomotopyLocalizedRightAdjoint).map f) :
    𝟭 (BoundedComplexCategory MetrizableLCA.{0}) ⟶
      boundedHomotopyLocalizedVerdierFunctorW1461 ⋙
        boundedHomotopyLocalizedRightAdjoint where
  app := unitApp
  naturality := by
    intro X Y f
    simpa using unitNaturality f

/-- W1465 constructs the localized-adjunction counit from component maps. -/
def localizedAdjunctionCounitOfW1465
    (boundedHomotopyLocalizedRightAdjoint :
      BoundedHomotopyLocalizedCategoryW1461 ⥤
        BoundedComplexCategory MetrizableLCA.{0})
    (counitApp :
      ∀ Y : BoundedHomotopyLocalizedCategoryW1461,
        (boundedHomotopyLocalizedRightAdjoint ⋙
          boundedHomotopyLocalizedVerdierFunctorW1461).obj Y ⟶
          Y)
    (counitNaturality :
      ∀ {X Y : BoundedHomotopyLocalizedCategoryW1461} (f : X ⟶ Y),
        (boundedHomotopyLocalizedRightAdjoint ⋙
          boundedHomotopyLocalizedVerdierFunctorW1461).map f ≫
            counitApp Y =
          counitApp X ≫ f) :
    boundedHomotopyLocalizedRightAdjoint ⋙
        boundedHomotopyLocalizedVerdierFunctorW1461 ⟶
      𝟭 BoundedHomotopyLocalizedCategoryW1461 where
  app := counitApp
  naturality := by
    intro X Y f
    simpa using counitNaturality f

/--
W1465 replaces W1464's bundled localized-adjunction unit and counit natural
transformations by component maps and naturality proofs.
-/
structure W987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionInputW1465 :
    Type 2 where
  rightOpenBoundary :
    Dbounded.MetrizableWppLimitRightOpenClosedQuotientCoverBoundary
  sourcePiZeroBoundary :
    Dbounded.MetrizableWppLimitSourceDifferenceCokernelPiZeroBoundary
  relationPullbackProvider :
    ClosedNatTransOrdinaryRelationPullbackProviderW712
  targetRelationLiftsProvider :
    ClosedNatTransOrdinaryTargetRelationLiftsProviderW712
  targetNoUnivData :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944
  closedEmbeddingClosednessData :
    ClosedEmbeddingClosednessDataProviderW973
  normalizedLiftBlueprint :
    Dbounded.MetrizableWalkingParallelPairNormalizedLiftBlueprint
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
  endpointClosedEmbedding :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      IsClosedEmbedding ((K.sc i).f : (K.sc i).X₁ → (K.sc i).X₂)
  endpointOpenMap :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      IsOpenMap ((K.sc i).g : (K.sc i).X₂ → (K.sc i).X₃)
  endpointCokernelTop :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.cokernelSubgroup (K.sc i).g = ⊤
  endpointKernelEquality :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ)
      (x₂ : (K.sc i).X₂),
        (K.sc i).g x₂ = 0 ↔
          ∃ x₁ : (K.sc i).X₁, (K.sc i).f x₁ = x₂
  boundedHomotopyLocalizedRightAdjoint :
    BoundedHomotopyLocalizedCategoryW1461 ⥤
      BoundedComplexCategory MetrizableLCA.{0}
  boundedHomotopyLocalizedAdjunctionUnitApp :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      X ⟶
        (boundedHomotopyLocalizedVerdierFunctorW1461 ⋙
          boundedHomotopyLocalizedRightAdjoint).obj X
  boundedHomotopyLocalizedAdjunctionUnitNaturality :
    ∀ {X Y : BoundedComplexCategory MetrizableLCA.{0}} (f : X ⟶ Y),
      f ≫ boundedHomotopyLocalizedAdjunctionUnitApp Y =
        boundedHomotopyLocalizedAdjunctionUnitApp X ≫
          (boundedHomotopyLocalizedVerdierFunctorW1461 ⋙
            boundedHomotopyLocalizedRightAdjoint).map f
  boundedHomotopyLocalizedAdjunctionCounitApp :
    ∀ Y : BoundedHomotopyLocalizedCategoryW1461,
      (boundedHomotopyLocalizedRightAdjoint ⋙
        boundedHomotopyLocalizedVerdierFunctorW1461).obj Y ⟶
        Y
  boundedHomotopyLocalizedAdjunctionCounitNaturality :
    ∀ {X Y : BoundedHomotopyLocalizedCategoryW1461} (f : X ⟶ Y),
      (boundedHomotopyLocalizedRightAdjoint ⋙
        boundedHomotopyLocalizedVerdierFunctorW1461).map f ≫
          boundedHomotopyLocalizedAdjunctionCounitApp Y =
        boundedHomotopyLocalizedAdjunctionCounitApp X ≫ f
  boundedHomotopyLocalizedAdjunctionLeftTriangle :
    Functor.whiskerRight
          (localizedAdjunctionUnitOfW1465
            boundedHomotopyLocalizedRightAdjoint
            boundedHomotopyLocalizedAdjunctionUnitApp
            boundedHomotopyLocalizedAdjunctionUnitNaturality)
          boundedHomotopyLocalizedVerdierFunctorW1461 ≫
        (Functor.associator boundedHomotopyLocalizedVerdierFunctorW1461
          boundedHomotopyLocalizedRightAdjoint
          boundedHomotopyLocalizedVerdierFunctorW1461).hom ≫
      Functor.whiskerLeft boundedHomotopyLocalizedVerdierFunctorW1461
        (localizedAdjunctionCounitOfW1465
          boundedHomotopyLocalizedRightAdjoint
          boundedHomotopyLocalizedAdjunctionCounitApp
          boundedHomotopyLocalizedAdjunctionCounitNaturality) =
      NatTrans.id
        (𝟭 (BoundedComplexCategory MetrizableLCA.{0}) ⋙
          boundedHomotopyLocalizedVerdierFunctorW1461)
  boundedHomotopyLocalizedAdjunctionRightTriangle :
    Functor.whiskerLeft boundedHomotopyLocalizedRightAdjoint
          (localizedAdjunctionUnitOfW1465
            boundedHomotopyLocalizedRightAdjoint
            boundedHomotopyLocalizedAdjunctionUnitApp
            boundedHomotopyLocalizedAdjunctionUnitNaturality) ≫
        (Functor.associator boundedHomotopyLocalizedRightAdjoint
          boundedHomotopyLocalizedVerdierFunctorW1461
          boundedHomotopyLocalizedRightAdjoint).inv ≫
      Functor.whiskerRight
        (localizedAdjunctionCounitOfW1465
          boundedHomotopyLocalizedRightAdjoint
          boundedHomotopyLocalizedAdjunctionCounitApp
          boundedHomotopyLocalizedAdjunctionCounitNaturality)
        boundedHomotopyLocalizedRightAdjoint =
      NatTrans.id
        (boundedHomotopyLocalizedRightAdjoint ⋙
          𝟭 (BoundedComplexCategory MetrizableLCA.{0}))
  unitMappingConeModel :
    UnitMappingConeModelW962
  unitMappingConeClosedEmbedding :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      IsClosedEmbedding (((unitMappingConeModel X).as.sc i).f :
        ((unitMappingConeModel X).as.sc i).X₁ →
          ((unitMappingConeModel X).as.sc i).X₂)
  unitMappingConeOpenMap :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      IsOpenMap (((unitMappingConeModel X).as.sc i).g :
        ((unitMappingConeModel X).as.sc i).X₂ →
          ((unitMappingConeModel X).as.sc i).X₃)
  unitMappingConeCokernelTop :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.cokernelSubgroup (((unitMappingConeModel X).as.sc i).g) =
        ⊤
  unitMappingConeKernelEquality :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ : ((unitMappingConeModel X).as.sc i).X₂),
        ((unitMappingConeModel X).as.sc i).g x₂ = 0 ↔
          ∃ x₁ : ((unitMappingConeModel X).as.sc i).X₁,
            ((unitMappingConeModel X).as.sc i).f x₁ = x₂
  unitMappingConeIsoHom :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      unitMappingConeIsoSourceW1464
          boundedHomotopyLocalizedRightAdjoint
          (localizedAdjunctionUnitOfW1465
            boundedHomotopyLocalizedRightAdjoint
            boundedHomotopyLocalizedAdjunctionUnitApp
            boundedHomotopyLocalizedAdjunctionUnitNaturality)
          X ⟶
        unitMappingConeModel X
  unitMappingConeIsoInv :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      unitMappingConeModel X ⟶
        unitMappingConeIsoSourceW1464
          boundedHomotopyLocalizedRightAdjoint
          (localizedAdjunctionUnitOfW1465
            boundedHomotopyLocalizedRightAdjoint
            boundedHomotopyLocalizedAdjunctionUnitApp
            boundedHomotopyLocalizedAdjunctionUnitNaturality)
          X
  unitMappingConeIsoHomInvId :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      unitMappingConeIsoHom X ≫ unitMappingConeIsoInv X =
        𝟙 (unitMappingConeIsoSourceW1464
          boundedHomotopyLocalizedRightAdjoint
          (localizedAdjunctionUnitOfW1465
            boundedHomotopyLocalizedRightAdjoint
            boundedHomotopyLocalizedAdjunctionUnitApp
            boundedHomotopyLocalizedAdjunctionUnitNaturality)
          X)
  unitMappingConeIsoInvHomId :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      unitMappingConeIsoInv X ≫ unitMappingConeIsoHom X =
        𝟙 (unitMappingConeModel X)

/-- W1465 reconstructs the localized-adjunction unit for an input package. -/
def localizedAdjunctionUnitOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionInputW1465) :
    𝟭 (BoundedComplexCategory MetrizableLCA.{0}) ⟶
      boundedHomotopyLocalizedVerdierFunctorW1461 ⋙
        input.boundedHomotopyLocalizedRightAdjoint :=
  localizedAdjunctionUnitOfW1465
    input.boundedHomotopyLocalizedRightAdjoint
    input.boundedHomotopyLocalizedAdjunctionUnitApp
    input.boundedHomotopyLocalizedAdjunctionUnitNaturality

/-- W1465 reconstructs the localized-adjunction counit for an input package. -/
def localizedAdjunctionCounitOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionInputW1465) :
    input.boundedHomotopyLocalizedRightAdjoint ⋙
        boundedHomotopyLocalizedVerdierFunctorW1461 ⟶
      𝟭 BoundedHomotopyLocalizedCategoryW1461 :=
  localizedAdjunctionCounitOfW1465
    input.boundedHomotopyLocalizedRightAdjoint
    input.boundedHomotopyLocalizedAdjunctionCounitApp
    input.boundedHomotopyLocalizedAdjunctionCounitNaturality

/-- W1465 builds the W1464 input after constructing the localized unit/counit. -/
def w1464InputOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionInputW1465) :
    W987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionInputW1464 where
  rightOpenBoundary := input.rightOpenBoundary
  sourcePiZeroBoundary := input.sourcePiZeroBoundary
  relationPullbackProvider := input.relationPullbackProvider
  targetRelationLiftsProvider := input.targetRelationLiftsProvider
  targetNoUnivData := input.targetNoUnivData
  closedEmbeddingClosednessData := input.closedEmbeddingClosednessData
  normalizedLiftBlueprint := input.normalizedLiftBlueprint
  targetFixedTargetUniq := input.targetFixedTargetUniq
  localizationModelFixedTargetUniq := input.localizationModelFixedTargetUniq
  sourcePretriangulated := input.sourcePretriangulated
  sourceTriangulated := input.sourceTriangulated
  triangleCompletion := input.triangleCompletion
  endpointClosedEmbedding := input.endpointClosedEmbedding
  endpointOpenMap := input.endpointOpenMap
  endpointCokernelTop := input.endpointCokernelTop
  endpointKernelEquality := input.endpointKernelEquality
  boundedHomotopyLocalizedRightAdjoint :=
    input.boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedAdjunctionUnit :=
    localizedAdjunctionUnitOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
      input
  boundedHomotopyLocalizedAdjunctionCounit :=
    localizedAdjunctionCounitOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
      input
  boundedHomotopyLocalizedAdjunctionLeftTriangle :=
    input.boundedHomotopyLocalizedAdjunctionLeftTriangle
  boundedHomotopyLocalizedAdjunctionRightTriangle :=
    input.boundedHomotopyLocalizedAdjunctionRightTriangle
  unitMappingConeModel := input.unitMappingConeModel
  unitMappingConeClosedEmbedding := input.unitMappingConeClosedEmbedding
  unitMappingConeOpenMap := input.unitMappingConeOpenMap
  unitMappingConeCokernelTop := input.unitMappingConeCokernelTop
  unitMappingConeKernelEquality := input.unitMappingConeKernelEquality
  unitMappingConeIsoHom := input.unitMappingConeIsoHom
  unitMappingConeIsoInv := input.unitMappingConeIsoInv
  unitMappingConeIsoHomInvId := input.unitMappingConeIsoHomInvId
  unitMappingConeIsoInvHomId := input.unitMappingConeIsoInvHomId

/-- W1465 builds W981 unit strict-exact/isomorphism data through W1464. -/
def unitStrictExactIsoDataOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionInputW1465) :
    UnitMappingConeStrictExactIsoDataProviderW981
      (localizedAdjunctionDataOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
        (w1463InputOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464
          (w1464InputOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
            input))) :=
  unitStrictExactIsoDataOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464
    (w1464InputOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
      input)

/-- W1465 builds W945 localized-unit data through W1464. -/
def localizedUnitDataOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionInputW1465) :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945 :=
  localizedUnitDataOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464
    (w1464InputOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
      input)

/-- W1465 builds W730 boundary/relation data through W1464. -/
def boundaryRelationDataOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionInputW1465) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464
    (w1464InputOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
      input)

/-- W1465 builds W986 target/endpoint data through W1464. -/
def targetNormalizedEndpointDataOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionInputW1465) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetNormalizedEndpointDataOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464
    (w1464InputOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
      input)

/-- W1465 builds W987 full data through W1464. -/
noncomputable def fullDataOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionInputW1465) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464
    (w1464InputOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
      input)

/-- W1465's constructed localized unit keeps the component map. -/
theorem w1465LocalizedAdjunctionUnitKeepsApp
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionInputW1465)
    (X : BoundedComplexCategory MetrizableLCA.{0}) :
    (localizedAdjunctionUnitOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
        input).app X =
      input.boundedHomotopyLocalizedAdjunctionUnitApp X :=
  rfl

/-- W1465's constructed localized counit keeps the component map. -/
theorem w1465LocalizedAdjunctionCounitKeepsApp
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionInputW1465)
    (Y : BoundedHomotopyLocalizedCategoryW1461) :
    (localizedAdjunctionCounitOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
        input).app Y =
      input.boundedHomotopyLocalizedAdjunctionCounitApp Y :=
  rfl

/-- W1465's W1464 input keeps the constructed localized unit. -/
theorem w1465W1464InputKeepsConstructedLocalizedUnit
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionInputW1465) :
    (w1464InputOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
        input).boundedHomotopyLocalizedAdjunctionUnit =
      localizedAdjunctionUnitOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
        input :=
  rfl

/-- W1465's W1464 input keeps the constructed localized counit. -/
theorem w1465W1464InputKeepsConstructedLocalizedCounit
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionInputW1465) :
    (w1464InputOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
        input).boundedHomotopyLocalizedAdjunctionCounit =
      localizedAdjunctionCounitOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
        input :=
  rfl

/-- W1465's W1464 input keeps the unit mapping-cone model. -/
theorem w1465W1464InputKeepsUnitMappingConeModel
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionInputW1465) :
    (w1464InputOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
        input).unitMappingConeModel =
      input.unitMappingConeModel :=
  rfl

/-- W1465's constructed W945 data keeps the localized right adjoint. -/
theorem w1465LocalizedUnitDataKeepsLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionInputW1465) :
    boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
        (localizedUnitDataOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
          input) =
      input.boundedHomotopyLocalizedRightAdjoint :=
  rfl

/-- W1465's constructed W987 provider projects to the constructed W730 data. -/
theorem w1465FullDataKeepsConstructedBoundaryRelation
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionInputW1465) :
    boundaryRelationDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
          input) =
      boundaryRelationDataOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
        input :=
  rfl

/-- W1465's constructed W987 provider projects to the constructed W986 data. -/
theorem w1465FullDataKeepsConstructedTargetNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionInputW1465) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
          input) =
      targetNormalizedEndpointDataOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
        input :=
  rfl

def w987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionInputNamesW1465 :
    List String :=
  ["raw right-open closed-quotient-cover WPP-limit boundary field",
    "raw source-difference cokernel-pi-zero WPP-limit boundary field",
    "raw closed-natural-transformation relation-pullback provider",
    "raw closed-natural-transformation target-relation-lifts provider",
    "W944 target no-univ data",
    "W973 closed-embedding closedness data",
    "normalized lift blueprint",
    "target fixed-target uniqueness",
    "localization-model fixed-target uniqueness",
    "source pretriangulated structure",
    "source triangulated structure",
    "source triangle-completion input",
    "endpoint closed-embedding family",
    "endpoint open-map family",
    "endpoint cokernel-top family",
    "endpoint kernel-equality family",
    "bounded homotopy localized right adjoint",
    "localized adjunction unit component family",
    "localized adjunction unit naturality proof",
    "localized adjunction counit component family",
    "localized adjunction counit naturality proof",
    "localized adjunction left triangle identity",
    "localized adjunction right triangle identity",
    "unit mapping-cone model",
    "unit mapping-cone closed-embedding family",
    "unit mapping-cone open-map family",
    "unit mapping-cone cokernel-top family",
    "unit mapping-cone kernel-equality family",
    "unit mapping-cone isomorphism hom",
    "unit mapping-cone isomorphism inv",
    "unit mapping-cone isomorphism hom-inv identity",
    "unit mapping-cone isomorphism inv-hom identity"]

theorem w987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionInputNamesW1465_count :
    w987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionInputNamesW1465.length =
      32 :=
  rfl

def w987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionNatTransInputNamesW1465 :
    List String :=
  ["localized adjunction unit natural transformation",
    "localized adjunction counit natural transformation"]

theorem w987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionNatTransInputNamesW1465_count :
    w987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionNatTransInputNamesW1465.length =
      2 :=
  rfl

def w987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionComponentInputNamesW1465 :
    List String :=
  ["localized adjunction unit component family",
    "localized adjunction unit naturality proof",
    "localized adjunction counit component family",
    "localized adjunction counit naturality proof"]

theorem w987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionComponentInputNamesW1465_count :
    w987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionComponentInputNamesW1465.length =
      4 :=
  rfl

/-- W1465 splits W1464's two localized unit/counit transformations into four fields. -/
theorem w1465BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionSplitsNatTransInputs :
    w987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionNatTransInputNamesW1465.length <
      w987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionComponentInputNamesW1465.length := by
  rw [
    w987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionNatTransInputNamesW1465_count,
    w987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionComponentInputNamesW1465_count]
  norm_num

/-- W1465 replaces the thirty W1464 inputs by thirty-two named inputs. -/
theorem w1465BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionExpandsW1464InputCount :
    w987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionInputNamesW1464.length <
      w987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionInputNamesW1465.length := by
  rw [w987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionInputNamesW1464_count,
    w987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionInputNamesW1465_count]
  norm_num

/-- Current W1465 nonterminal localized-adjunction natural-transformation construction state. -/
structure W987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionStateW1465 :
    Type where
  seed : String
  declarations : List String
  constructionResult : String
  projectionResult : String
  natTransComponentInputNames : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1465 records the localized unit/counit component construction path. -/
def currentW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionStateW1465 :
    W987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionStateW1465 where
  seed :=
    "w1465-w987-boundary-relation-target-localized-adjunction-nattrans-field-data-construction"
  declarations :=
    ["localizedAdjunctionUnitOfW1465",
      "localizedAdjunctionCounitOfW1465",
      "W987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionInputW1465",
      "localizedAdjunctionUnitOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465",
      "localizedAdjunctionCounitOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465",
      "w1464InputOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465",
      "unitStrictExactIsoDataOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465",
      "localizedUnitDataOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465",
      "boundaryRelationDataOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465",
      "targetNormalizedEndpointDataOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465",
      "fullDataOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465",
      "w1465LocalizedAdjunctionUnitKeepsApp",
      "w1465LocalizedAdjunctionCounitKeepsApp",
      "w1465W1464InputKeepsConstructedLocalizedUnit",
      "w1465W1464InputKeepsConstructedLocalizedCounit",
      "w1465W1464InputKeepsUnitMappingConeModel",
      "w1465LocalizedUnitDataKeepsLocalizedRightAdjoint",
      "w1465FullDataKeepsConstructedBoundaryRelation",
      "w1465FullDataKeepsConstructedTargetNormalizedEndpoint",
      "w987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionInputNamesW1465_count",
      "w987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionNatTransInputNamesW1465_count",
      "w987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionComponentInputNamesW1465_count",
      "w1465BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionSplitsNatTransInputs",
      "w1465BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionExpandsW1464InputCount"]
  constructionResult :=
    "proved: W1465 constructs the localized-adjunction unit and counit natural\
      transformations from component and naturality fields, then feeds them\
      into W1464"
  projectionResult :=
    "proved: the constructed localized unit and counit feed W1464 while\
      preserving localized-unit, boundary, and target/endpoint projections;\
      product success is still not claimed"
  natTransComponentInputNames :=
    w987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionComponentInputNamesW1465
  remainingInputs :=
    w987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionInputNamesW1465
  productSuccessClaimed := false

theorem currentW1465W987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstruction_productSuccess :
    currentW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionStateW1465.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
