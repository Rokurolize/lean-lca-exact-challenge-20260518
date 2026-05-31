import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionGuardW1465

/-!
W1466 refines W1465 by constructing the localized-adjunction triangle
natural-transformation identities from objectwise component identities, then
running the resulting data through the W1465 W987 construction.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace Dbounded

noncomputable section

/-- W1466 names the left triangle composite natural transformation. -/
def localizedAdjunctionLeftTriangleNatTransOfW1466
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
              boundedHomotopyLocalizedRightAdjoint).map f)
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
    𝟭 (BoundedComplexCategory MetrizableLCA.{0}) ⋙
        boundedHomotopyLocalizedVerdierFunctorW1461 ⟶
      𝟭 (BoundedComplexCategory MetrizableLCA.{0}) ⋙
        boundedHomotopyLocalizedVerdierFunctorW1461 :=
  Functor.whiskerRight
        (localizedAdjunctionUnitOfW1465
          boundedHomotopyLocalizedRightAdjoint
          unitApp
          unitNaturality)
        boundedHomotopyLocalizedVerdierFunctorW1461 ≫
      (Functor.associator boundedHomotopyLocalizedVerdierFunctorW1461
        boundedHomotopyLocalizedRightAdjoint
        boundedHomotopyLocalizedVerdierFunctorW1461).hom ≫
    Functor.whiskerLeft boundedHomotopyLocalizedVerdierFunctorW1461
      (localizedAdjunctionCounitOfW1465
        boundedHomotopyLocalizedRightAdjoint
        counitApp
        counitNaturality)

/-- W1466 names the right triangle composite natural transformation. -/
def localizedAdjunctionRightTriangleNatTransOfW1466
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
              boundedHomotopyLocalizedRightAdjoint).map f)
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
        𝟭 (BoundedComplexCategory MetrizableLCA.{0}) ⟶
      boundedHomotopyLocalizedRightAdjoint ⋙
        𝟭 (BoundedComplexCategory MetrizableLCA.{0}) :=
  Functor.whiskerLeft boundedHomotopyLocalizedRightAdjoint
        (localizedAdjunctionUnitOfW1465
          boundedHomotopyLocalizedRightAdjoint
          unitApp
          unitNaturality) ≫
      (Functor.associator boundedHomotopyLocalizedRightAdjoint
        boundedHomotopyLocalizedVerdierFunctorW1461
        boundedHomotopyLocalizedRightAdjoint).inv ≫
    Functor.whiskerRight
      (localizedAdjunctionCounitOfW1465
        boundedHomotopyLocalizedRightAdjoint
        counitApp
        counitNaturality)
      boundedHomotopyLocalizedRightAdjoint

/--
W1466 replaces W1465's full localized-adjunction triangle identities by
objectwise component identities used to reconstruct those identities.
-/
structure W987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionInputW1466 :
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
  boundedHomotopyLocalizedAdjunctionLeftTriangleApp :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      (localizedAdjunctionLeftTriangleNatTransOfW1466
          boundedHomotopyLocalizedRightAdjoint
          boundedHomotopyLocalizedAdjunctionUnitApp
          boundedHomotopyLocalizedAdjunctionUnitNaturality
          boundedHomotopyLocalizedAdjunctionCounitApp
          boundedHomotopyLocalizedAdjunctionCounitNaturality).app X =
        (NatTrans.id
          (𝟭 (BoundedComplexCategory MetrizableLCA.{0}) ⋙
            boundedHomotopyLocalizedVerdierFunctorW1461)).app X
  boundedHomotopyLocalizedAdjunctionRightTriangleApp :
    ∀ Y : BoundedHomotopyLocalizedCategoryW1461,
      (localizedAdjunctionRightTriangleNatTransOfW1466
          boundedHomotopyLocalizedRightAdjoint
          boundedHomotopyLocalizedAdjunctionUnitApp
          boundedHomotopyLocalizedAdjunctionUnitNaturality
          boundedHomotopyLocalizedAdjunctionCounitApp
          boundedHomotopyLocalizedAdjunctionCounitNaturality).app Y =
        (NatTrans.id
          (boundedHomotopyLocalizedRightAdjoint ⋙
            𝟭 (BoundedComplexCategory MetrizableLCA.{0}))).app Y
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

/-- W1466 exposes the left triangle composite for an input package. -/
def localizedAdjunctionLeftTriangleNatTransOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionInputW1466) :
    𝟭 (BoundedComplexCategory MetrizableLCA.{0}) ⋙
        boundedHomotopyLocalizedVerdierFunctorW1461 ⟶
      𝟭 (BoundedComplexCategory MetrizableLCA.{0}) ⋙
        boundedHomotopyLocalizedVerdierFunctorW1461 :=
  localizedAdjunctionLeftTriangleNatTransOfW1466
    input.boundedHomotopyLocalizedRightAdjoint
    input.boundedHomotopyLocalizedAdjunctionUnitApp
    input.boundedHomotopyLocalizedAdjunctionUnitNaturality
    input.boundedHomotopyLocalizedAdjunctionCounitApp
    input.boundedHomotopyLocalizedAdjunctionCounitNaturality

/-- W1466 exposes the right triangle composite for an input package. -/
def localizedAdjunctionRightTriangleNatTransOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionInputW1466) :
    input.boundedHomotopyLocalizedRightAdjoint ⋙
        𝟭 (BoundedComplexCategory MetrizableLCA.{0}) ⟶
      input.boundedHomotopyLocalizedRightAdjoint ⋙
        𝟭 (BoundedComplexCategory MetrizableLCA.{0}) :=
  localizedAdjunctionRightTriangleNatTransOfW1466
    input.boundedHomotopyLocalizedRightAdjoint
    input.boundedHomotopyLocalizedAdjunctionUnitApp
    input.boundedHomotopyLocalizedAdjunctionUnitNaturality
    input.boundedHomotopyLocalizedAdjunctionCounitApp
    input.boundedHomotopyLocalizedAdjunctionCounitNaturality

/-- W1466 constructs the left triangle identity from component identities. -/
def localizedAdjunctionLeftTriangleOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionInputW1466) :
    localizedAdjunctionLeftTriangleNatTransOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
        input =
      NatTrans.id
        (𝟭 (BoundedComplexCategory MetrizableLCA.{0}) ⋙
          boundedHomotopyLocalizedVerdierFunctorW1461) := by
  apply NatTrans.ext
  funext X
  exact input.boundedHomotopyLocalizedAdjunctionLeftTriangleApp X

/-- W1466 constructs the right triangle identity from component identities. -/
def localizedAdjunctionRightTriangleOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionInputW1466) :
    localizedAdjunctionRightTriangleNatTransOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
        input =
      NatTrans.id
        (input.boundedHomotopyLocalizedRightAdjoint ⋙
          𝟭 (BoundedComplexCategory MetrizableLCA.{0})) := by
  apply NatTrans.ext
  funext Y
  exact input.boundedHomotopyLocalizedAdjunctionRightTriangleApp Y

/-- W1466 builds the W1465 input after constructing the two triangle identities. -/
def w1465InputOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionInputW1466) :
    W987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionInputW1465 where
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
  boundedHomotopyLocalizedAdjunctionUnitApp :=
    input.boundedHomotopyLocalizedAdjunctionUnitApp
  boundedHomotopyLocalizedAdjunctionUnitNaturality :=
    input.boundedHomotopyLocalizedAdjunctionUnitNaturality
  boundedHomotopyLocalizedAdjunctionCounitApp :=
    input.boundedHomotopyLocalizedAdjunctionCounitApp
  boundedHomotopyLocalizedAdjunctionCounitNaturality :=
    input.boundedHomotopyLocalizedAdjunctionCounitNaturality
  boundedHomotopyLocalizedAdjunctionLeftTriangle :=
    localizedAdjunctionLeftTriangleOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
      input
  boundedHomotopyLocalizedAdjunctionRightTriangle :=
    localizedAdjunctionRightTriangleOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
      input
  unitMappingConeModel := input.unitMappingConeModel
  unitMappingConeClosedEmbedding := input.unitMappingConeClosedEmbedding
  unitMappingConeOpenMap := input.unitMappingConeOpenMap
  unitMappingConeCokernelTop := input.unitMappingConeCokernelTop
  unitMappingConeKernelEquality := input.unitMappingConeKernelEquality
  unitMappingConeIsoHom := input.unitMappingConeIsoHom
  unitMappingConeIsoInv := input.unitMappingConeIsoInv
  unitMappingConeIsoHomInvId := input.unitMappingConeIsoHomInvId
  unitMappingConeIsoInvHomId := input.unitMappingConeIsoInvHomId

/-- W1466 builds W981 unit strict-exact/isomorphism data through W1465. -/
def unitStrictExactIsoDataOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionInputW1466) :
    UnitMappingConeStrictExactIsoDataProviderW981
      (localizedAdjunctionDataOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
        (w1463InputOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464
          (w1464InputOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
            (w1465InputOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
              input)))) :=
  unitStrictExactIsoDataOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
    (w1465InputOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
      input)

/-- W1466 builds W945 localized-unit data through W1465. -/
def localizedUnitDataOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionInputW1466) :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945 :=
  localizedUnitDataOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
    (w1465InputOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
      input)

/-- W1466 builds W730 boundary/relation data through W1465. -/
def boundaryRelationDataOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionInputW1466) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
    (w1465InputOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
      input)

/-- W1466 builds W986 target/endpoint data through W1465. -/
def targetNormalizedEndpointDataOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionInputW1466) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetNormalizedEndpointDataOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
    (w1465InputOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
      input)

/-- W1466 builds W987 full data through W1465. -/
noncomputable def fullDataOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionInputW1466) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfW987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataW1465
    (w1465InputOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
      input)

/-- W1466's left triangle composite keeps the component identity family. -/
theorem w1466LocalizedAdjunctionLeftTriangleKeepsApp
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionInputW1466)
    (X : BoundedComplexCategory MetrizableLCA.{0}) :
    (localizedAdjunctionLeftTriangleNatTransOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
        input).app X =
      (NatTrans.id
        (𝟭 (BoundedComplexCategory MetrizableLCA.{0}) ⋙
          boundedHomotopyLocalizedVerdierFunctorW1461)).app X :=
  input.boundedHomotopyLocalizedAdjunctionLeftTriangleApp X

/-- W1466's right triangle composite keeps the component identity family. -/
theorem w1466LocalizedAdjunctionRightTriangleKeepsApp
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionInputW1466)
    (Y : BoundedHomotopyLocalizedCategoryW1461) :
    (localizedAdjunctionRightTriangleNatTransOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
        input).app Y =
      (NatTrans.id
        (input.boundedHomotopyLocalizedRightAdjoint ⋙
          𝟭 (BoundedComplexCategory MetrizableLCA.{0}))).app Y :=
  input.boundedHomotopyLocalizedAdjunctionRightTriangleApp Y

/-- W1466's W1465 input keeps the localized unit component family. -/
theorem w1466W1465InputKeepsLocalizedUnitApp
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionInputW1466) :
    (w1465InputOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
        input).boundedHomotopyLocalizedAdjunctionUnitApp =
      input.boundedHomotopyLocalizedAdjunctionUnitApp :=
  rfl

/-- W1466's W1465 input keeps the localized counit component family. -/
theorem w1466W1465InputKeepsLocalizedCounitApp
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionInputW1466) :
    (w1465InputOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
        input).boundedHomotopyLocalizedAdjunctionCounitApp =
      input.boundedHomotopyLocalizedAdjunctionCounitApp :=
  rfl

/-- W1466's W1465 input keeps the unit mapping-cone model. -/
theorem w1466W1465InputKeepsUnitMappingConeModel
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionInputW1466) :
    (w1465InputOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
        input).unitMappingConeModel =
      input.unitMappingConeModel :=
  rfl

/-- W1466's constructed W945 data keeps the localized right adjoint. -/
theorem w1466LocalizedUnitDataKeepsLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionInputW1466) :
    boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
        (localizedUnitDataOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
          input) =
      input.boundedHomotopyLocalizedRightAdjoint :=
  rfl

/-- W1466's constructed W987 provider projects to the constructed W730 data. -/
theorem w1466FullDataKeepsConstructedBoundaryRelation
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionInputW1466) :
    boundaryRelationDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
          input) =
      boundaryRelationDataOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
        input :=
  rfl

/-- W1466's constructed W987 provider projects to the constructed W986 data. -/
theorem w1466FullDataKeepsConstructedTargetNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionInputW1466) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
          input) =
      targetNormalizedEndpointDataOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
        input :=
  rfl

def w987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionInputNamesW1466 :
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
    "localized adjunction left triangle component identity family",
    "localized adjunction right triangle component identity family",
    "unit mapping-cone model",
    "unit mapping-cone closed-embedding family",
    "unit mapping-cone open-map family",
    "unit mapping-cone cokernel-top family",
    "unit mapping-cone kernel-equality family",
    "unit mapping-cone isomorphism hom",
    "unit mapping-cone isomorphism inv",
    "unit mapping-cone isomorphism hom-inv identity",
    "unit mapping-cone isomorphism inv-hom identity"]

theorem w987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionInputNamesW1466_count :
    w987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionInputNamesW1466.length =
      32 :=
  rfl

def w987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionTriangleInputNamesW1466 :
    List String :=
  ["localized adjunction left triangle natural-transformation identity",
    "localized adjunction right triangle natural-transformation identity"]

theorem w987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionTriangleInputNamesW1466_count :
    w987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionTriangleInputNamesW1466.length =
      2 :=
  rfl

def w987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionComponentInputNamesW1466 :
    List String :=
  ["localized adjunction left triangle component identity family",
    "localized adjunction right triangle component identity family"]

theorem w987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionComponentInputNamesW1466_count :
    w987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionComponentInputNamesW1466.length =
      2 :=
  rfl

/-- W1466 replaces two triangle identities by two component identity families. -/
theorem w1466BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionPreservesTriangleInputCount :
    w987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionTriangleInputNamesW1466.length =
      w987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionComponentInputNamesW1466.length := by
  rw [
    w987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionTriangleInputNamesW1466_count,
    w987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionComponentInputNamesW1466_count]

/-- W1466 preserves the thirty-two W1465 input count while lowering triangle identity evidence to components. -/
theorem w1466BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionPreservesW1465InputCount :
    w987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionInputNamesW1466.length =
      w987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionInputNamesW1465.length := by
  rw [
    w987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionInputNamesW1466_count,
    w987BoundaryRelationTargetLocalizedAdjunctionNatTransFieldDataConstructionInputNamesW1465_count]

/-- Current W1466 nonterminal localized-adjunction triangle component construction state. -/
structure W987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionStateW1466 :
    Type where
  seed : String
  declarations : List String
  constructionResult : String
  projectionResult : String
  triangleComponentInputNames : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1466 records the component-to-triangle-identity construction path. -/
def currentW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionStateW1466 :
    W987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionStateW1466 where
  seed :=
    "w1466-w987-boundary-relation-target-localized-adjunction-triangle-component-field-data-construction"
  declarations :=
    ["localizedAdjunctionLeftTriangleNatTransOfW1466",
      "localizedAdjunctionRightTriangleNatTransOfW1466",
      "W987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionInputW1466",
      "localizedAdjunctionLeftTriangleNatTransOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466",
      "localizedAdjunctionRightTriangleNatTransOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466",
      "localizedAdjunctionLeftTriangleOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466",
      "localizedAdjunctionRightTriangleOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466",
      "w1465InputOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466",
      "unitStrictExactIsoDataOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466",
      "localizedUnitDataOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466",
      "boundaryRelationDataOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466",
      "targetNormalizedEndpointDataOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466",
      "fullDataOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466",
      "w1466LocalizedAdjunctionLeftTriangleKeepsApp",
      "w1466LocalizedAdjunctionRightTriangleKeepsApp",
      "w1466W1465InputKeepsLocalizedUnitApp",
      "w1466W1465InputKeepsLocalizedCounitApp",
      "w1466W1465InputKeepsUnitMappingConeModel",
      "w1466LocalizedUnitDataKeepsLocalizedRightAdjoint",
      "w1466FullDataKeepsConstructedBoundaryRelation",
      "w1466FullDataKeepsConstructedTargetNormalizedEndpoint",
      "w987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionInputNamesW1466_count",
      "w987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionTriangleInputNamesW1466_count",
      "w987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionComponentInputNamesW1466_count",
      "w1466BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionPreservesTriangleInputCount",
      "w1466BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionPreservesW1465InputCount"]
  constructionResult :=
    "proved: W1466 constructs the localized-adjunction left and right triangle\
      natural-transformation identities from objectwise component identities,\
      then feeds those identities into W1465"
  projectionResult :=
    "proved: the constructed triangle identities feed W1465 while preserving\
      localized-unit, boundary, and target/endpoint projections; product\
      success is still not claimed"
  triangleComponentInputNames :=
    w987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionComponentInputNamesW1466
  remainingInputs :=
    w987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionInputNamesW1466
  productSuccessClaimed := false

theorem currentW1466W987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstruction_productSuccess :
    currentW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionStateW1466.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
