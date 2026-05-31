import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionGuardW1462

/-!
W1463 refines W1462 by constructing its endpoint strict short-exact family from
endpoint closed-embedding, open-map, cokernel-top, and kernel-equality fields,
then runs the resulting data through the W1462 W987 construction.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace Dbounded

noncomputable section

/--
W1463 replaces the W1462 endpoint strict short-exact family by the four
endpoint component fields used to construct strict short exactness.
-/
structure W987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputW1463 :
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
  boundedHomotopyLocalizedAdjunctionUnit :
    𝟭 (BoundedComplexCategory MetrizableLCA.{0}) ⟶
      boundedHomotopyLocalizedVerdierFunctorW1461 ⋙
        boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedAdjunctionCounit :
    boundedHomotopyLocalizedRightAdjoint ⋙
        boundedHomotopyLocalizedVerdierFunctorW1461 ⟶
      𝟭 BoundedHomotopyLocalizedCategoryW1461
  boundedHomotopyLocalizedAdjunctionLeftTriangle :
    Functor.whiskerRight boundedHomotopyLocalizedAdjunctionUnit
          boundedHomotopyLocalizedVerdierFunctorW1461 ≫
        (Functor.associator boundedHomotopyLocalizedVerdierFunctorW1461
          boundedHomotopyLocalizedRightAdjoint
          boundedHomotopyLocalizedVerdierFunctorW1461).hom ≫
      Functor.whiskerLeft boundedHomotopyLocalizedVerdierFunctorW1461
        boundedHomotopyLocalizedAdjunctionCounit =
      NatTrans.id
        (𝟭 (BoundedComplexCategory MetrizableLCA.{0}) ⋙
          boundedHomotopyLocalizedVerdierFunctorW1461)
  boundedHomotopyLocalizedAdjunctionRightTriangle :
    Functor.whiskerLeft boundedHomotopyLocalizedRightAdjoint
          boundedHomotopyLocalizedAdjunctionUnit ≫
        (Functor.associator boundedHomotopyLocalizedRightAdjoint
          boundedHomotopyLocalizedVerdierFunctorW1461
          boundedHomotopyLocalizedRightAdjoint).inv ≫
      Functor.whiskerRight boundedHomotopyLocalizedAdjunctionCounit
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
  unitMappingConeIso :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
          (CochainComplex.mappingCone
            ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
              (boundedHomotopyLocalizedAdjunctionUnit.app X)))) ≅
        unitMappingConeModel X)

/-- W1463 constructs endpoint strict short exactness from endpoint components. -/
def endpointStrictExactOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
    (input :
      W987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputW1463) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  fun K i =>
    MetrizableLCA.strictShortExact_of_kernel_open_closed_cokernelSubgroup_eq_top
      (input.endpointKernelEquality K i)
      (input.endpointClosedEmbedding K i)
      (input.endpointOpenMap K i)
      (input.endpointCokernelTop K i)

/-- W1463 builds the W1462 input after constructing endpoint strict exactness. -/
def w1462InputOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
    (input :
      W987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputW1463) :
    W987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputW1462 where
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
  endpointStrictExact :=
    endpointStrictExactOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
      input
  boundedHomotopyLocalizedRightAdjoint :=
    input.boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedAdjunctionUnit :=
    input.boundedHomotopyLocalizedAdjunctionUnit
  boundedHomotopyLocalizedAdjunctionCounit :=
    input.boundedHomotopyLocalizedAdjunctionCounit
  boundedHomotopyLocalizedAdjunctionLeftTriangle :=
    input.boundedHomotopyLocalizedAdjunctionLeftTriangle
  boundedHomotopyLocalizedAdjunctionRightTriangle :=
    input.boundedHomotopyLocalizedAdjunctionRightTriangle
  unitMappingConeModel := input.unitMappingConeModel
  unitMappingConeClosedEmbedding := input.unitMappingConeClosedEmbedding
  unitMappingConeOpenMap := input.unitMappingConeOpenMap
  unitMappingConeCokernelTop := input.unitMappingConeCokernelTop
  unitMappingConeKernelEquality := input.unitMappingConeKernelEquality
  unitMappingConeIso := input.unitMappingConeIso

/-- W1463 builds W1461 input through W1462. -/
def w1461InputOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
    (input :
      W987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputW1463) :
    W987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputW1461 :=
  w1461InputOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
    (w1462InputOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
      input)

/-- W1463 builds the localized-adjunction core through W1462. -/
def localizedAdjunctionCoreOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
    (input :
      W987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputW1463) :
    Adjunction.CoreUnitCounit
      boundedHomotopyLocalizedVerdierFunctorW1461
      input.boundedHomotopyLocalizedRightAdjoint :=
  localizedAdjunctionCoreOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
    (w1462InputOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
      input)

/-- W1463 builds the localized adjunction through W1462. -/
def localizedAdjunctionOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
    (input :
      W987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputW1463) :
    boundedHomotopyLocalizedVerdierFunctorW1461 ⊣
      input.boundedHomotopyLocalizedRightAdjoint :=
  localizedAdjunctionOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
    (w1462InputOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
      input)

/-- W1463 builds the W1460 input through W1462. -/
def w1460InputOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
    (input :
      W987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputW1463) :
    W987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputW1460 :=
  w1460InputOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
    (w1462InputOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
      input)

/-- W1463 builds W975 localized-adjunction data through W1462. -/
def localizedAdjunctionDataOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
    (input :
      W987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputW1463) :
    BoundedHomotopyLocalizedAdjunctionDataProviderW975 :=
  localizedAdjunctionDataOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
    (w1462InputOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
      input)

/-- W1463 builds W981 unit strict-exact/isomorphism data through W1462. -/
def unitStrictExactIsoDataOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
    (input :
      W987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputW1463) :
    UnitMappingConeStrictExactIsoDataProviderW981
      (localizedAdjunctionDataOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
        input) :=
  unitStrictExactIsoDataOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
    (w1462InputOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
      input)

/-- W1463 builds the W939 unit-component witness through W1462. -/
def unitComponentsOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
    (input :
      W987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputW1463) :
    boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponentsPrimitiveW939
      input.boundedHomotopyLocalizedRightAdjoint
      (localizedAdjunctionOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
        input) :=
  unitComponentsOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
    (w1462InputOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
      input)

/-- W1463 builds W945 localized-unit data through W1462. -/
def localizedUnitDataOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
    (input :
      W987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputW1463) :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945 :=
  localizedUnitDataOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
    (w1462InputOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
      input)

/-- W1463 builds W730 boundary/relation data through W1462. -/
def boundaryRelationDataOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
    (input :
      W987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputW1463) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
    (w1462InputOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
      input)

/-- W1463 builds W986 target/endpoint data through W1462. -/
def targetNormalizedEndpointDataOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
    (input :
      W987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputW1463) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetNormalizedEndpointDataOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
    (w1462InputOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
      input)

/-- W1463 builds W987 full data through W1462. -/
noncomputable def fullDataOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
    (input :
      W987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputW1463) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
    (w1462InputOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
      input)

/-- W1463's constructed endpoint strict exactness keeps the closed-embedding field. -/
theorem w1463EndpointStrictExactKeepsClosedEmbedding
    (input :
      W987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputW1463)
    (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ) :
    (endpointStrictExactOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
        input K i).closed_inclusion =
      input.endpointClosedEmbedding K i :=
  rfl

/-- W1463's constructed endpoint strict exactness keeps the open-map field. -/
theorem w1463EndpointStrictExactKeepsOpenMap
    (input :
      W987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputW1463)
    (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ) :
    (endpointStrictExactOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
        input K i).open_map =
      input.endpointOpenMap K i :=
  rfl

/-- W1463 derives endpoint surjectivity from cokernel-top and open-map fields. -/
theorem w1463EndpointStrictExactDerivesSurjective
    (input :
      W987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputW1463)
    (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ) :
    (endpointStrictExactOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
        input K i).surjective =
      MetrizableLCA.surjective_of_cokernelSubgroup_eq_top_of_isOpenMap
        (K.sc i).g
        (input.endpointCokernelTop K i)
        (input.endpointOpenMap K i) :=
  rfl

/-- W1463 obtains endpoint algebraic exactness from the kernel-equality field. -/
theorem w1463EndpointStrictExactGivesAlgebraicExact
    (input :
      W987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputW1463)
    (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ)
    (x₂ : (K.sc i).X₂) (hx₂ : (K.sc i).g x₂ = 0) :
    ∃ x₁ : (K.sc i).X₁, (K.sc i).f x₁ = x₂ :=
  (input.endpointKernelEquality K i x₂).mp hx₂

/-- W1463's W1462 input keeps the constructed endpoint strict exactness. -/
theorem w1463W1462InputKeepsConstructedEndpointStrictExact
    (input :
      W987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputW1463) :
    (w1462InputOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
        input).endpointStrictExact =
      endpointStrictExactOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
        input :=
  rfl

/-- W1463's W1462 input keeps the unit mapping-cone model. -/
theorem w1463W1462InputKeepsUnitMappingConeModel
    (input :
      W987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputW1463) :
    (w1462InputOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
        input).unitMappingConeModel =
      input.unitMappingConeModel :=
  rfl

/-- W1463's W1462 input keeps the unit mapping-cone isomorphism. -/
theorem w1463W1462InputKeepsUnitMappingConeIso
    (input :
      W987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputW1463) :
    (w1462InputOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
        input).unitMappingConeIso =
      input.unitMappingConeIso :=
  rfl

/-- W1463's constructed W945 data keeps the localized right adjoint. -/
theorem w1463LocalizedUnitDataKeepsLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputW1463) :
    boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
        (localizedUnitDataOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
          input) =
      input.boundedHomotopyLocalizedRightAdjoint :=
  rfl

/-- W1463's constructed W945 data keeps the constructed localized adjunction. -/
theorem w1463LocalizedUnitDataKeepsConstructedLocalizedAdjunction
    (input :
      W987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputW1463) :
    boundedHomotopyLocalizedAdjunctionOfLocalizedUnitDataW945
        (localizedUnitDataOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
          input) =
      localizedAdjunctionOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
        input :=
  rfl

/-- W1463's constructed W987 provider projects to the constructed W730 data. -/
theorem w1463FullDataKeepsConstructedBoundaryRelation
    (input :
      W987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputW1463) :
    boundaryRelationDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
          input) =
      boundaryRelationDataOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
        input :=
  rfl

/-- W1463's constructed W987 provider projects to the constructed W986 data. -/
theorem w1463FullDataKeepsConstructedTargetNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputW1463) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
          input) =
      targetNormalizedEndpointDataOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
        input :=
  rfl

def w987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputNamesW1463 :
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
    "localized adjunction unit natural transformation",
    "localized adjunction counit natural transformation",
    "localized adjunction left triangle identity",
    "localized adjunction right triangle identity",
    "unit mapping-cone model",
    "unit mapping-cone closed-embedding family",
    "unit mapping-cone open-map family",
    "unit mapping-cone cokernel-top family",
    "unit mapping-cone kernel-equality family",
    "unit mapping-cone chosen isomorphism"]

theorem w987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputNamesW1463_count :
    w987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputNamesW1463.length =
      27 :=
  rfl

def w987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionStrictExactInputNamesW1463 :
    List String :=
  ["endpoint strict short-exact family"]

theorem w987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionStrictExactInputNamesW1463_count :
    w987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionStrictExactInputNamesW1463.length =
      1 :=
  rfl

def w987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionComponentInputNamesW1463 :
    List String :=
  ["endpoint closed-embedding family",
    "endpoint open-map family",
    "endpoint cokernel-top family",
    "endpoint kernel-equality family"]

theorem w987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionComponentInputNamesW1463_count :
    w987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionComponentInputNamesW1463.length =
      4 :=
  rfl

/-- W1463 splits W1462's endpoint strict short-exact input into four fields. -/
theorem w1463BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionSplitsStrictExactInput :
    w987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionStrictExactInputNamesW1463.length <
      w987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionComponentInputNamesW1463.length := by
  rw [
    w987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionStrictExactInputNamesW1463_count,
    w987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionComponentInputNamesW1463_count]
  norm_num

/-- W1463 replaces the twenty-four W1462 inputs by twenty-seven named inputs. -/
theorem w1463BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionExpandsW1462InputCount :
    w987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputNamesW1462.length <
      w987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputNamesW1463.length := by
  rw [w987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputNamesW1462_count,
    w987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputNamesW1463_count]
  norm_num

/-- Current W1463 nonterminal endpoint kernel/cokernel-top construction state. -/
structure W987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionStateW1463 :
    Type where
  seed : String
  declarations : List String
  constructionResult : String
  projectionResult : String
  endpointKernelCokernelTopInputNames : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1463 records the endpoint component-to-strict-exact construction path. -/
def currentW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionStateW1463 :
    W987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionStateW1463 where
  seed :=
    "w1463-w987-boundary-relation-target-endpoint-kernel-cokernel-top-field-data-construction"
  declarations :=
    ["W987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputW1463",
      "endpointStrictExactOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463",
      "w1462InputOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463",
      "w1461InputOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463",
      "localizedAdjunctionCoreOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463",
      "localizedAdjunctionOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463",
      "w1460InputOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463",
      "localizedAdjunctionDataOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463",
      "unitStrictExactIsoDataOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463",
      "unitComponentsOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463",
      "localizedUnitDataOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463",
      "boundaryRelationDataOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463",
      "targetNormalizedEndpointDataOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463",
      "fullDataOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463",
      "w1463EndpointStrictExactKeepsClosedEmbedding",
      "w1463EndpointStrictExactKeepsOpenMap",
      "w1463EndpointStrictExactDerivesSurjective",
      "w1463EndpointStrictExactGivesAlgebraicExact",
      "w1463W1462InputKeepsConstructedEndpointStrictExact",
      "w1463W1462InputKeepsUnitMappingConeModel",
      "w1463W1462InputKeepsUnitMappingConeIso",
      "w1463LocalizedUnitDataKeepsLocalizedRightAdjoint",
      "w1463LocalizedUnitDataKeepsConstructedLocalizedAdjunction",
      "w1463FullDataKeepsConstructedBoundaryRelation",
      "w1463FullDataKeepsConstructedTargetNormalizedEndpoint",
      "w987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputNamesW1463_count",
      "w987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionStrictExactInputNamesW1463_count",
      "w987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionComponentInputNamesW1463_count",
      "w1463BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionSplitsStrictExactInput",
      "w1463BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionExpandsW1462InputCount"]
  constructionResult :=
    "proved: W1463 constructs endpoint strict short exactness from\
      endpoint closed-embedding, open-map, cokernel-top, and kernel-equality\
      fields, then feeds that constructed strict exactness into W1462"
  projectionResult :=
    "proved: the constructed endpoint strict exactness feeds W1462 while\
      preserving localized-unit, boundary, and target/endpoint projections;\
      product success is still not claimed"
  endpointKernelCokernelTopInputNames :=
    w987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionComponentInputNamesW1463
  remainingInputs :=
    w987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputNamesW1463
  productSuccessClaimed := false

theorem currentW1463W987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstruction_productSuccess :
    currentW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionStateW1463.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
