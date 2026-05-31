import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionGuardW1461

/-!
W1462 refines W1461 by constructing its unit mapping-cone strict short-exact
family from closed-embedding, open-map, cokernel-top, and kernel-equality
fields, then runs the resulting data through the W1461 W987 construction.
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
W1462 replaces the W1461 unit mapping-cone strict short-exact family by the
four component fields used to construct strict short exactness.
-/
structure W987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputW1462 :
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
  endpointStrictExact :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i)
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

/-- W1462 constructs unit mapping-cone strict short exactness from components. -/
def unitMappingConeStrictExactOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
    (input :
      W987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputW1462) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact ((input.unitMappingConeModel X).as.sc i) :=
  fun X i =>
    MetrizableLCA.strictShortExact_of_kernel_open_closed_cokernelSubgroup_eq_top
      (input.unitMappingConeKernelEquality X i)
      (input.unitMappingConeClosedEmbedding X i)
      (input.unitMappingConeOpenMap X i)
      (input.unitMappingConeCokernelTop X i)

/-- W1462 builds the W1461 input after constructing strict exactness. -/
def w1461InputOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
    (input :
      W987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputW1462) :
    W987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputW1461 where
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
  endpointStrictExact := input.endpointStrictExact
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
  unitMappingConeStrictExact :=
    unitMappingConeStrictExactOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
      input
  unitMappingConeIso := input.unitMappingConeIso

/-- W1462 builds the localized-adjunction core through W1461. -/
def localizedAdjunctionCoreOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
    (input :
      W987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputW1462) :
    Adjunction.CoreUnitCounit
      boundedHomotopyLocalizedVerdierFunctorW1461
      input.boundedHomotopyLocalizedRightAdjoint :=
  localizedAdjunctionCoreOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
    (w1461InputOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
      input)

/-- W1462 builds the localized adjunction through W1461. -/
def localizedAdjunctionOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
    (input :
      W987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputW1462) :
    boundedHomotopyLocalizedVerdierFunctorW1461 ⊣
      input.boundedHomotopyLocalizedRightAdjoint :=
  localizedAdjunctionOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
    (w1461InputOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
      input)

/-- W1462 builds the W1460 input through W1461. -/
def w1460InputOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
    (input :
      W987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputW1462) :
    W987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputW1460 :=
  w1460InputOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
    (w1461InputOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
      input)

/-- W1462 builds W975 localized-adjunction data through W1461. -/
def localizedAdjunctionDataOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
    (input :
      W987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputW1462) :
    BoundedHomotopyLocalizedAdjunctionDataProviderW975 :=
  localizedAdjunctionDataOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
    (w1461InputOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
      input)

/-- W1462 builds W981 unit strict-exact/isomorphism data through W1461. -/
def unitStrictExactIsoDataOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
    (input :
      W987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputW1462) :
    UnitMappingConeStrictExactIsoDataProviderW981
      (localizedAdjunctionDataOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
        input) :=
  unitStrictExactIsoDataOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
    (w1461InputOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
      input)

/-- W1462 builds the W939 unit-component witness through W1461. -/
def unitComponentsOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
    (input :
      W987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputW1462) :
    boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponentsPrimitiveW939
      input.boundedHomotopyLocalizedRightAdjoint
      (localizedAdjunctionOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
        input) :=
  unitComponentsOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
    (w1461InputOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
      input)

/-- W1462 builds W945 localized-unit data through W1461. -/
def localizedUnitDataOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
    (input :
      W987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputW1462) :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945 :=
  localizedUnitDataOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
    (w1461InputOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
      input)

/-- W1462 builds W730 boundary/relation data through W1461. -/
def boundaryRelationDataOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
    (input :
      W987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputW1462) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
    (w1461InputOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
      input)

/-- W1462 builds W986 target/endpoint data through W1461. -/
def targetNormalizedEndpointDataOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
    (input :
      W987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputW1462) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetNormalizedEndpointDataOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
    (w1461InputOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
      input)

/-- W1462 builds W987 full data through W1461. -/
noncomputable def fullDataOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
    (input :
      W987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputW1462) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
    (w1461InputOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
      input)

/-- W1462's constructed strict exactness keeps the closed-embedding field. -/
theorem w1462UnitMappingConeStrictExactKeepsClosedEmbedding
    (input :
      W987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputW1462)
    (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ) :
    (unitMappingConeStrictExactOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
        input X i).closed_inclusion =
      input.unitMappingConeClosedEmbedding X i :=
  rfl

/-- W1462's constructed strict exactness keeps the open-map field. -/
theorem w1462UnitMappingConeStrictExactKeepsOpenMap
    (input :
      W987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputW1462)
    (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ) :
    (unitMappingConeStrictExactOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
        input X i).open_map =
      input.unitMappingConeOpenMap X i :=
  rfl

/-- W1462 derives surjectivity from cokernel-top and open-map fields. -/
theorem w1462UnitMappingConeStrictExactDerivesSurjective
    (input :
      W987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputW1462)
    (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ) :
    (unitMappingConeStrictExactOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
        input X i).surjective =
      MetrizableLCA.surjective_of_cokernelSubgroup_eq_top_of_isOpenMap
        (((input.unitMappingConeModel X).as.sc i).g)
        (input.unitMappingConeCokernelTop X i)
        (input.unitMappingConeOpenMap X i) :=
  rfl

/-- W1462 obtains algebraic exactness from the kernel-equality field. -/
theorem w1462UnitMappingConeStrictExactGivesAlgebraicExact
    (input :
      W987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputW1462)
    (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
    (x₂ : ((input.unitMappingConeModel X).as.sc i).X₂)
    (hx₂ : ((input.unitMappingConeModel X).as.sc i).g x₂ = 0) :
    ∃ x₁ : ((input.unitMappingConeModel X).as.sc i).X₁,
      ((input.unitMappingConeModel X).as.sc i).f x₁ = x₂ :=
  (input.unitMappingConeKernelEquality X i x₂).mp hx₂

/-- W1462's W1461 input keeps the constructed strict exactness. -/
theorem w1462W1461InputKeepsConstructedUnitMappingConeStrictExact
    (input :
      W987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputW1462) :
    (w1461InputOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
        input).unitMappingConeStrictExact =
      unitMappingConeStrictExactOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
        input :=
  rfl

/-- W1462's W1461 input keeps the unit mapping-cone model. -/
theorem w1462W1461InputKeepsUnitMappingConeModel
    (input :
      W987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputW1462) :
    (w1461InputOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
        input).unitMappingConeModel =
      input.unitMappingConeModel :=
  rfl

/-- W1462's W1461 input keeps the unit mapping-cone isomorphism. -/
theorem w1462W1461InputKeepsUnitMappingConeIso
    (input :
      W987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputW1462) :
    (w1461InputOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
        input).unitMappingConeIso =
      input.unitMappingConeIso :=
  rfl

/-- W1462's constructed W945 data keeps the localized right adjoint. -/
theorem w1462LocalizedUnitDataKeepsLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputW1462) :
    boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
        (localizedUnitDataOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
          input) =
      input.boundedHomotopyLocalizedRightAdjoint :=
  rfl

/-- W1462's constructed W945 data keeps the constructed localized adjunction. -/
theorem w1462LocalizedUnitDataKeepsConstructedLocalizedAdjunction
    (input :
      W987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputW1462) :
    boundedHomotopyLocalizedAdjunctionOfLocalizedUnitDataW945
        (localizedUnitDataOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
          input) =
      localizedAdjunctionOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
        input :=
  rfl

/-- W1462's constructed W987 provider projects to the constructed W730 data. -/
theorem w1462FullDataKeepsConstructedBoundaryRelation
    (input :
      W987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputW1462) :
    boundaryRelationDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
          input) =
      boundaryRelationDataOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
        input :=
  rfl

/-- W1462's constructed W987 provider projects to the constructed W986 data. -/
theorem w1462FullDataKeepsConstructedTargetNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputW1462) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
          input) =
      targetNormalizedEndpointDataOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462
        input :=
  rfl

def w987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputNamesW1462 :
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
    "endpoint strict short-exact witnesses",
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

theorem w987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputNamesW1462_count :
    w987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputNamesW1462.length =
      24 :=
  rfl

def w987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionStrictExactInputNamesW1462 :
    List String :=
  ["unit mapping-cone strict short-exact family"]

theorem w987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionStrictExactInputNamesW1462_count :
    w987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionStrictExactInputNamesW1462.length =
      1 :=
  rfl

def w987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionComponentInputNamesW1462 :
    List String :=
  ["unit mapping-cone closed-embedding family",
    "unit mapping-cone open-map family",
    "unit mapping-cone cokernel-top family",
    "unit mapping-cone kernel-equality family"]

theorem w987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionComponentInputNamesW1462_count :
    w987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionComponentInputNamesW1462.length =
      4 :=
  rfl

/-- W1462 splits W1461's strict short-exact input into four component fields. -/
theorem w1462BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionSplitsStrictExactInput :
    w987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionStrictExactInputNamesW1462.length <
      w987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionComponentInputNamesW1462.length := by
  rw [
    w987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionStrictExactInputNamesW1462_count,
    w987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionComponentInputNamesW1462_count]
  norm_num

/-- W1462 replaces the twenty-one W1461 inputs by twenty-four named inputs. -/
theorem w1462BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionExpandsW1461InputCount :
    w987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputNamesW1461.length <
      w987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputNamesW1462.length := by
  rw [w987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputNamesW1461_count,
    w987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputNamesW1462_count]
  norm_num

/-- Current W1462 nonterminal unit kernel/cokernel-top construction state. -/
structure W987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionStateW1462 :
    Type where
  seed : String
  declarations : List String
  constructionResult : String
  projectionResult : String
  unitKernelCokernelTopInputNames : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1462 records the component-to-strict-exact construction path into W1461. -/
def currentW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionStateW1462 :
    W987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionStateW1462 where
  seed :=
    "w1462-w987-boundary-relation-target-unit-kernel-cokernel-top-field-data-construction"
  declarations :=
    ["W987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputW1462",
      "unitMappingConeStrictExactOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462",
      "w1461InputOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462",
      "localizedAdjunctionCoreOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462",
      "localizedAdjunctionOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462",
      "w1460InputOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462",
      "localizedAdjunctionDataOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462",
      "unitStrictExactIsoDataOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462",
      "unitComponentsOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462",
      "localizedUnitDataOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462",
      "boundaryRelationDataOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462",
      "targetNormalizedEndpointDataOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462",
      "fullDataOfW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataW1462",
      "w1462UnitMappingConeStrictExactKeepsClosedEmbedding",
      "w1462UnitMappingConeStrictExactKeepsOpenMap",
      "w1462UnitMappingConeStrictExactDerivesSurjective",
      "w1462UnitMappingConeStrictExactGivesAlgebraicExact",
      "w1462W1461InputKeepsConstructedUnitMappingConeStrictExact",
      "w1462W1461InputKeepsUnitMappingConeModel",
      "w1462W1461InputKeepsUnitMappingConeIso",
      "w1462LocalizedUnitDataKeepsLocalizedRightAdjoint",
      "w1462LocalizedUnitDataKeepsConstructedLocalizedAdjunction",
      "w1462FullDataKeepsConstructedBoundaryRelation",
      "w1462FullDataKeepsConstructedTargetNormalizedEndpoint",
      "w987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputNamesW1462_count",
      "w987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionStrictExactInputNamesW1462_count",
      "w987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionComponentInputNamesW1462_count",
      "w1462BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionSplitsStrictExactInput",
      "w1462BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionExpandsW1461InputCount"]
  constructionResult :=
    "proved: W1462 constructs unit mapping-cone strict short exactness from\
      closed-embedding, open-map, cokernel-top, and kernel-equality fields,\
      then feeds that constructed strict exactness into the W1461 W987 route"
  projectionResult :=
    "proved: the constructed strict exactness feeds W1461 while preserving\
      localized-unit, boundary, and target/endpoint projections; product\
      success is still not claimed"
  unitKernelCokernelTopInputNames :=
    w987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionComponentInputNamesW1462
  remainingInputs :=
    w987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionInputNamesW1462
  productSuccessClaimed := false

theorem currentW1462W987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstruction_productSuccess :
    currentW987BoundaryRelationTargetUnitKernelCokernelTopFieldDataConstructionStateW1462.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
