import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionGuardW1466

/-!
W1467 refines W1466 by constructing the localized right-adjoint functor from
object and morphism map fields, then running the resulting data through the
W1466 W987 construction.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace Dbounded

noncomputable section

/-- W1467 packages the raw functor fields for the localized right adjoint. -/
structure LocalizedRightAdjointFunctorFieldsW1467 : Type 2 where
  obj :
    BoundedHomotopyLocalizedCategoryW1461 →
      BoundedComplexCategory MetrizableLCA.{0}
  map :
    ∀ {X Y : BoundedHomotopyLocalizedCategoryW1461},
      (X ⟶ Y) → (obj X ⟶ obj Y)
  map_id :
    ∀ X : BoundedHomotopyLocalizedCategoryW1461,
      map (𝟙 X : X ⟶ X) = 𝟙 (obj X)
  map_comp :
    ∀ {X Y Z : BoundedHomotopyLocalizedCategoryW1461}
      (f : X ⟶ Y) (g : Y ⟶ Z),
        map (f ≫ g) = map f ≫ map g

/-- W1467 reconstructs the localized right-adjoint functor from raw fields. -/
def localizedRightAdjointOfW1467
    (fields : LocalizedRightAdjointFunctorFieldsW1467) :
    BoundedHomotopyLocalizedCategoryW1461 ⥤
      BoundedComplexCategory MetrizableLCA.{0} where
  obj X := fields.obj X
  map f := fields.map f
  map_id X := fields.map_id X
  map_comp f g := fields.map_comp f g

/-- W1467's reconstructed localized right adjoint keeps the object map. -/
theorem w1467LocalizedRightAdjointKeepsObj
    (fields : LocalizedRightAdjointFunctorFieldsW1467)
    (X : BoundedHomotopyLocalizedCategoryW1461) :
    (localizedRightAdjointOfW1467 fields).obj X = fields.obj X :=
  rfl

/-- W1467's reconstructed localized right adjoint keeps the morphism map. -/
theorem w1467LocalizedRightAdjointKeepsMap
    (fields : LocalizedRightAdjointFunctorFieldsW1467)
    {X Y : BoundedHomotopyLocalizedCategoryW1461} (f : X ⟶ Y) :
    (localizedRightAdjointOfW1467 fields).map f = fields.map f :=
  rfl

/-- W1467 names the left triangle composite natural transformation. -/
def localizedAdjunctionLeftTriangleNatTransOfW1467
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
  localizedAdjunctionLeftTriangleNatTransOfW1466
    boundedHomotopyLocalizedRightAdjoint
    unitApp
    unitNaturality
    counitApp
    counitNaturality

/-- W1467 names the right triangle composite natural transformation. -/
def localizedAdjunctionRightTriangleNatTransOfW1467
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
  localizedAdjunctionRightTriangleNatTransOfW1466
    boundedHomotopyLocalizedRightAdjoint
    unitApp
    unitNaturality
    counitApp
    counitNaturality

/--
W1467 replaces W1466's localized right-adjoint functor input by explicit
object and morphism map fields used to reconstruct that functor.
-/
structure W987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionInputW1467 :
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
  boundedHomotopyLocalizedRightAdjointFields :
    LocalizedRightAdjointFunctorFieldsW1467
  boundedHomotopyLocalizedAdjunctionUnitApp :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      X ⟶
        (boundedHomotopyLocalizedVerdierFunctorW1461 ⋙
          localizedRightAdjointOfW1467
            boundedHomotopyLocalizedRightAdjointFields).obj X
  boundedHomotopyLocalizedAdjunctionUnitNaturality :
    ∀ {X Y : BoundedComplexCategory MetrizableLCA.{0}} (f : X ⟶ Y),
      f ≫ boundedHomotopyLocalizedAdjunctionUnitApp Y =
        boundedHomotopyLocalizedAdjunctionUnitApp X ≫
          (boundedHomotopyLocalizedVerdierFunctorW1461 ⋙
            localizedRightAdjointOfW1467
              boundedHomotopyLocalizedRightAdjointFields).map f
  boundedHomotopyLocalizedAdjunctionCounitApp :
    ∀ Y : BoundedHomotopyLocalizedCategoryW1461,
      ((localizedRightAdjointOfW1467
          boundedHomotopyLocalizedRightAdjointFields) ⋙
        boundedHomotopyLocalizedVerdierFunctorW1461).obj Y ⟶
        Y
  boundedHomotopyLocalizedAdjunctionCounitNaturality :
    ∀ {X Y : BoundedHomotopyLocalizedCategoryW1461} (f : X ⟶ Y),
      ((localizedRightAdjointOfW1467
          boundedHomotopyLocalizedRightAdjointFields) ⋙
        boundedHomotopyLocalizedVerdierFunctorW1461).map f ≫
          boundedHomotopyLocalizedAdjunctionCounitApp Y =
        boundedHomotopyLocalizedAdjunctionCounitApp X ≫ f
  boundedHomotopyLocalizedAdjunctionLeftTriangleApp :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      (localizedAdjunctionLeftTriangleNatTransOfW1467
          (localizedRightAdjointOfW1467
            boundedHomotopyLocalizedRightAdjointFields)
          boundedHomotopyLocalizedAdjunctionUnitApp
          boundedHomotopyLocalizedAdjunctionUnitNaturality
          boundedHomotopyLocalizedAdjunctionCounitApp
          boundedHomotopyLocalizedAdjunctionCounitNaturality).app X =
        (NatTrans.id
          (𝟭 (BoundedComplexCategory MetrizableLCA.{0}) ⋙
            boundedHomotopyLocalizedVerdierFunctorW1461)).app X
  boundedHomotopyLocalizedAdjunctionRightTriangleApp :
    ∀ Y : BoundedHomotopyLocalizedCategoryW1461,
      (localizedAdjunctionRightTriangleNatTransOfW1467
          (localizedRightAdjointOfW1467
            boundedHomotopyLocalizedRightAdjointFields)
          boundedHomotopyLocalizedAdjunctionUnitApp
          boundedHomotopyLocalizedAdjunctionUnitNaturality
          boundedHomotopyLocalizedAdjunctionCounitApp
          boundedHomotopyLocalizedAdjunctionCounitNaturality).app Y =
        (NatTrans.id
          ((localizedRightAdjointOfW1467
            boundedHomotopyLocalizedRightAdjointFields) ⋙
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
          (localizedRightAdjointOfW1467
            boundedHomotopyLocalizedRightAdjointFields)
          (localizedAdjunctionUnitOfW1465
            (localizedRightAdjointOfW1467
              boundedHomotopyLocalizedRightAdjointFields)
            boundedHomotopyLocalizedAdjunctionUnitApp
            boundedHomotopyLocalizedAdjunctionUnitNaturality)
          X ⟶
        unitMappingConeModel X
  unitMappingConeIsoInv :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      unitMappingConeModel X ⟶
        unitMappingConeIsoSourceW1464
          (localizedRightAdjointOfW1467
            boundedHomotopyLocalizedRightAdjointFields)
          (localizedAdjunctionUnitOfW1465
            (localizedRightAdjointOfW1467
              boundedHomotopyLocalizedRightAdjointFields)
            boundedHomotopyLocalizedAdjunctionUnitApp
            boundedHomotopyLocalizedAdjunctionUnitNaturality)
          X
  unitMappingConeIsoHomInvId :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      unitMappingConeIsoHom X ≫ unitMappingConeIsoInv X =
        𝟙 (unitMappingConeIsoSourceW1464
          (localizedRightAdjointOfW1467
            boundedHomotopyLocalizedRightAdjointFields)
          (localizedAdjunctionUnitOfW1465
            (localizedRightAdjointOfW1467
              boundedHomotopyLocalizedRightAdjointFields)
            boundedHomotopyLocalizedAdjunctionUnitApp
            boundedHomotopyLocalizedAdjunctionUnitNaturality)
          X)
  unitMappingConeIsoInvHomId :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      unitMappingConeIsoInv X ≫ unitMappingConeIsoHom X =
        𝟙 (unitMappingConeModel X)

/-- W1467 names the reconstructed localized right adjoint for an input package. -/
def boundedHomotopyLocalizedRightAdjointOfW1467
    (input :
      W987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionInputW1467) :
    BoundedHomotopyLocalizedCategoryW1461 ⥤
      BoundedComplexCategory MetrizableLCA.{0} :=
  localizedRightAdjointOfW1467
    input.boundedHomotopyLocalizedRightAdjointFields

/-- W1467 exposes the left triangle composite for an input package. -/
def localizedAdjunctionLeftTriangleNatTransOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467
    (input :
      W987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionInputW1467) :
    𝟭 (BoundedComplexCategory MetrizableLCA.{0}) ⋙
        boundedHomotopyLocalizedVerdierFunctorW1461 ⟶
      𝟭 (BoundedComplexCategory MetrizableLCA.{0}) ⋙
          boundedHomotopyLocalizedVerdierFunctorW1461 :=
  localizedAdjunctionLeftTriangleNatTransOfW1467
    (boundedHomotopyLocalizedRightAdjointOfW1467 input)
    input.boundedHomotopyLocalizedAdjunctionUnitApp
    input.boundedHomotopyLocalizedAdjunctionUnitNaturality
    input.boundedHomotopyLocalizedAdjunctionCounitApp
    input.boundedHomotopyLocalizedAdjunctionCounitNaturality

/-- W1467 exposes the right triangle composite for an input package. -/
def localizedAdjunctionRightTriangleNatTransOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467
    (input :
      W987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionInputW1467) :
    boundedHomotopyLocalizedRightAdjointOfW1467 input ⋙
        𝟭 (BoundedComplexCategory MetrizableLCA.{0}) ⟶
      boundedHomotopyLocalizedRightAdjointOfW1467 input ⋙
        𝟭 (BoundedComplexCategory MetrizableLCA.{0}) :=
  localizedAdjunctionRightTriangleNatTransOfW1467
    (boundedHomotopyLocalizedRightAdjointOfW1467 input)
    input.boundedHomotopyLocalizedAdjunctionUnitApp
    input.boundedHomotopyLocalizedAdjunctionUnitNaturality
    input.boundedHomotopyLocalizedAdjunctionCounitApp
    input.boundedHomotopyLocalizedAdjunctionCounitNaturality

/-- W1467 constructs the left triangle identity from component identities. -/
def localizedAdjunctionLeftTriangleOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467
    (input :
      W987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionInputW1467) :
    localizedAdjunctionLeftTriangleNatTransOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467
        input =
      NatTrans.id
        (𝟭 (BoundedComplexCategory MetrizableLCA.{0}) ⋙
          boundedHomotopyLocalizedVerdierFunctorW1461) := by
  apply NatTrans.ext
  funext X
  exact input.boundedHomotopyLocalizedAdjunctionLeftTriangleApp X

/-- W1467 constructs the right triangle identity from component identities. -/
def localizedAdjunctionRightTriangleOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467
    (input :
      W987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionInputW1467) :
    localizedAdjunctionRightTriangleNatTransOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467
        input =
      NatTrans.id
        (boundedHomotopyLocalizedRightAdjointOfW1467 input ⋙
          𝟭 (BoundedComplexCategory MetrizableLCA.{0})) := by
  apply NatTrans.ext
  funext Y
  exact input.boundedHomotopyLocalizedAdjunctionRightTriangleApp Y

/-- W1467 builds the W1466 input after reconstructing the right-adjoint functor. -/
def w1466InputOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467
    (input :
      W987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionInputW1467) :
    W987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionInputW1466 where
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
    boundedHomotopyLocalizedRightAdjointOfW1467 input
  boundedHomotopyLocalizedAdjunctionUnitApp :=
    input.boundedHomotopyLocalizedAdjunctionUnitApp
  boundedHomotopyLocalizedAdjunctionUnitNaturality :=
    input.boundedHomotopyLocalizedAdjunctionUnitNaturality
  boundedHomotopyLocalizedAdjunctionCounitApp :=
    input.boundedHomotopyLocalizedAdjunctionCounitApp
  boundedHomotopyLocalizedAdjunctionCounitNaturality :=
    input.boundedHomotopyLocalizedAdjunctionCounitNaturality
  boundedHomotopyLocalizedAdjunctionLeftTriangleApp :=
    input.boundedHomotopyLocalizedAdjunctionLeftTriangleApp
  boundedHomotopyLocalizedAdjunctionRightTriangleApp :=
    input.boundedHomotopyLocalizedAdjunctionRightTriangleApp
  unitMappingConeModel := input.unitMappingConeModel
  unitMappingConeClosedEmbedding := input.unitMappingConeClosedEmbedding
  unitMappingConeOpenMap := input.unitMappingConeOpenMap
  unitMappingConeCokernelTop := input.unitMappingConeCokernelTop
  unitMappingConeKernelEquality := input.unitMappingConeKernelEquality
  unitMappingConeIsoHom := input.unitMappingConeIsoHom
  unitMappingConeIsoInv := input.unitMappingConeIsoInv
  unitMappingConeIsoHomInvId := input.unitMappingConeIsoHomInvId
  unitMappingConeIsoInvHomId := input.unitMappingConeIsoInvHomId

/-- W1467 builds W981 unit strict-exact/isomorphism data through W1466. -/
def unitStrictExactIsoDataOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467
    (input :
      W987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionInputW1467) :=
  unitStrictExactIsoDataOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
    (w1466InputOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467
      input)

/-- W1467 builds W945 localized-unit data through W1466. -/
def localizedUnitDataOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467
    (input :
      W987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionInputW1467) :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945 :=
  localizedUnitDataOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
    (w1466InputOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467
      input)

/-- W1467 builds W730 boundary/relation data through W1466. -/
def boundaryRelationDataOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467
    (input :
      W987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionInputW1467) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
    (w1466InputOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467
      input)

/-- W1467 builds W986 target/endpoint data through W1466. -/
def targetNormalizedEndpointDataOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467
    (input :
      W987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionInputW1467) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetNormalizedEndpointDataOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
    (w1466InputOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467
      input)

/-- W1467 builds W987 full data through W1466. -/
noncomputable def fullDataOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467
    (input :
      W987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionInputW1467) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfW987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataW1466
    (w1466InputOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467
      input)

/-- W1467's left triangle composite keeps the component identity family. -/
theorem w1467LocalizedAdjunctionLeftTriangleKeepsApp
    (input :
      W987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionInputW1467)
    (X : BoundedComplexCategory MetrizableLCA.{0}) :
    (localizedAdjunctionLeftTriangleNatTransOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467
        input).app X =
      (NatTrans.id
        (𝟭 (BoundedComplexCategory MetrizableLCA.{0}) ⋙
          boundedHomotopyLocalizedVerdierFunctorW1461)).app X :=
  input.boundedHomotopyLocalizedAdjunctionLeftTriangleApp X

/-- W1467's right triangle composite keeps the component identity family. -/
theorem w1467LocalizedAdjunctionRightTriangleKeepsApp
    (input :
      W987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionInputW1467)
    (Y : BoundedHomotopyLocalizedCategoryW1461) :
    (localizedAdjunctionRightTriangleNatTransOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467
        input).app Y =
      (NatTrans.id
        (boundedHomotopyLocalizedRightAdjointOfW1467 input ⋙
          𝟭 (BoundedComplexCategory MetrizableLCA.{0}))).app Y :=
  input.boundedHomotopyLocalizedAdjunctionRightTriangleApp Y

/-- W1467's W1466 input keeps the reconstructed localized right adjoint. -/
theorem w1467W1466InputKeepsConstructedLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionInputW1467) :
    (w1466InputOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467
        input).boundedHomotopyLocalizedRightAdjoint =
      boundedHomotopyLocalizedRightAdjointOfW1467 input :=
  rfl

/-- W1467's W1466 input keeps the localized unit component family. -/
theorem w1467W1466InputKeepsLocalizedUnitApp
    (input :
      W987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionInputW1467) :
    (w1466InputOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467
        input).boundedHomotopyLocalizedAdjunctionUnitApp =
      input.boundedHomotopyLocalizedAdjunctionUnitApp :=
  rfl

/-- W1467's W1466 input keeps the localized counit component family. -/
theorem w1467W1466InputKeepsLocalizedCounitApp
    (input :
      W987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionInputW1467) :
    (w1466InputOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467
        input).boundedHomotopyLocalizedAdjunctionCounitApp =
      input.boundedHomotopyLocalizedAdjunctionCounitApp :=
  rfl

/-- W1467's W1466 input keeps the unit mapping-cone model. -/
theorem w1467W1466InputKeepsUnitMappingConeModel
    (input :
      W987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionInputW1467) :
    (w1466InputOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467
        input).unitMappingConeModel =
      input.unitMappingConeModel :=
  rfl

/-- W1467's constructed W945 data keeps the localized right adjoint. -/
theorem w1467LocalizedUnitDataKeepsLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionInputW1467) :
    boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
        (localizedUnitDataOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467
          input) =
      boundedHomotopyLocalizedRightAdjointOfW1467 input :=
  rfl

/-- W1467's constructed W987 provider projects to the constructed W730 data. -/
theorem w1467FullDataKeepsConstructedBoundaryRelation
    (input :
      W987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionInputW1467) :
    boundaryRelationDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467
          input) =
      boundaryRelationDataOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467
        input :=
  rfl

/-- W1467's constructed W987 provider projects to the constructed W986 data. -/
theorem w1467FullDataKeepsConstructedTargetNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionInputW1467) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467
          input) =
      targetNormalizedEndpointDataOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467
        input :=
  rfl

def w987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionInputNamesW1467 :
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
    "bounded homotopy localized right-adjoint object map",
    "bounded homotopy localized right-adjoint morphism map",
    "bounded homotopy localized right-adjoint identity law",
    "bounded homotopy localized right-adjoint composition law",
    "localized adjunction unit component family",
    "localized adjunction unit naturality proof",
    "localized adjunction counit component family",
    "localized adjunction counit naturality proof",
    "localized adjunction left localized right-adjoint functor field identity family",
    "localized adjunction right localized right-adjoint functor field identity family",
    "unit mapping-cone model",
    "unit mapping-cone closed-embedding family",
    "unit mapping-cone open-map family",
    "unit mapping-cone cokernel-top family",
    "unit mapping-cone kernel-equality family",
    "unit mapping-cone isomorphism hom",
    "unit mapping-cone isomorphism inv",
    "unit mapping-cone isomorphism hom-inv identity",
    "unit mapping-cone isomorphism inv-hom identity"]

theorem w987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionInputNamesW1467_count :
    w987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionInputNamesW1467.length =
      35 :=
  rfl

def w987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionFunctorInputNamesW1467 :
    List String :=
  ["bounded homotopy localized right-adjoint functor"]

theorem w987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionFunctorInputNamesW1467_count :
    w987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionFunctorInputNamesW1467.length =
      1 :=
  rfl

def w987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionFunctorFieldInputNamesW1467 :
    List String :=
  ["bounded homotopy localized right-adjoint object map",
    "bounded homotopy localized right-adjoint morphism map",
    "bounded homotopy localized right-adjoint identity law",
    "bounded homotopy localized right-adjoint composition law"]

theorem w987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionFunctorFieldInputNamesW1467_count :
    w987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionFunctorFieldInputNamesW1467.length =
      4 :=
  rfl

/-- W1467 replaces one localized right-adjoint functor input by four raw functor-field inputs. -/
theorem w1467BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionSplitsRightAdjointFunctorInput :
    w987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionFunctorInputNamesW1467.length <
      w987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionFunctorFieldInputNamesW1467.length := by
  rw [
    w987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionFunctorInputNamesW1467_count,
    w987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionFunctorFieldInputNamesW1467_count]
  decide

/-- W1467 expands the W1466 input count by decomposing the localized right-adjoint functor. -/
theorem w1467BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionExpandsW1466InputCount :
    w987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionInputNamesW1466.length <
      w987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionInputNamesW1467.length := by
  rw [
    w987BoundaryRelationTargetLocalizedAdjunctionTriangleComponentFieldDataConstructionInputNamesW1466_count,
    w987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionInputNamesW1467_count]
  decide

/-- Current W1467 nonterminal localized-right-adjoint functor field construction state. -/
structure W987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionStateW1467 :
    Type where
  seed : String
  declarations : List String
  constructionResult : String
  projectionResult : String
  localizedRightAdjointFunctorInputNames : List String
  localizedRightAdjointFunctorFieldInputNames : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1467 records the localized right-adjoint functor-field construction path. -/
def currentW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionStateW1467 :
    W987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionStateW1467 where
  seed :=
    "w1467-w987-boundary-relation-target-localized-right-adjoint-functor-field-data-construction"
  declarations :=
    ["LocalizedRightAdjointFunctorFieldsW1467",
      "localizedRightAdjointOfW1467",
      "w1467LocalizedRightAdjointKeepsObj",
      "w1467LocalizedRightAdjointKeepsMap",
      "localizedAdjunctionLeftTriangleNatTransOfW1467",
      "localizedAdjunctionRightTriangleNatTransOfW1467",
      "W987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionInputW1467",
      "boundedHomotopyLocalizedRightAdjointOfW1467",
      "localizedAdjunctionLeftTriangleNatTransOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467",
      "localizedAdjunctionRightTriangleNatTransOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467",
      "localizedAdjunctionLeftTriangleOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467",
      "localizedAdjunctionRightTriangleOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467",
      "w1466InputOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467",
      "unitStrictExactIsoDataOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467",
      "localizedUnitDataOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467",
      "boundaryRelationDataOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467",
      "targetNormalizedEndpointDataOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467",
      "fullDataOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467",
      "w1467LocalizedAdjunctionLeftTriangleKeepsApp",
      "w1467LocalizedAdjunctionRightTriangleKeepsApp",
      "w1467W1466InputKeepsConstructedLocalizedRightAdjoint",
      "w1467W1466InputKeepsLocalizedUnitApp",
      "w1467W1466InputKeepsLocalizedCounitApp",
      "w1467W1466InputKeepsUnitMappingConeModel",
      "w1467LocalizedUnitDataKeepsLocalizedRightAdjoint",
      "w1467FullDataKeepsConstructedBoundaryRelation",
      "w1467FullDataKeepsConstructedTargetNormalizedEndpoint",
      "w987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionInputNamesW1467_count",
      "w987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionFunctorInputNamesW1467_count",
      "w987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionFunctorFieldInputNamesW1467_count",
      "w1467BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionSplitsRightAdjointFunctorInput",
      "w1467BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionExpandsW1466InputCount"]
  constructionResult :=
    "proved: W1467 reconstructs the localized right-adjoint functor from\
      object and morphism maps plus identity and composition laws, then feeds\
      the reconstructed functor into W1466"
  projectionResult :=
    "proved: the reconstructed localized right adjoint feeds W1466 while\
      preserving localized-unit, boundary, and target/endpoint projections;\
      product success is still not claimed"
  localizedRightAdjointFunctorInputNames :=
    w987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionFunctorInputNamesW1467
  localizedRightAdjointFunctorFieldInputNames :=
    w987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionFunctorFieldInputNamesW1467
  remainingInputs :=
    w987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionInputNamesW1467
  productSuccessClaimed := false

theorem currentW1467W987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstruction_productSuccess :
    currentW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionStateW1467.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
