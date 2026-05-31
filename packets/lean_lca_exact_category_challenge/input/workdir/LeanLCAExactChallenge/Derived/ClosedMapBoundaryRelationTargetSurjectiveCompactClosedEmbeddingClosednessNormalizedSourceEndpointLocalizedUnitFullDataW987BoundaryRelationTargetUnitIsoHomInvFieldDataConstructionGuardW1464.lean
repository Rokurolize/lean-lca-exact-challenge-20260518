import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionGuardW1463

/-!
W1464 refines W1463 by constructing the unit mapping-cone isomorphism from
explicit hom, inv, and inverse-identity fields, then running the resulting data
through the W1463 W987 construction.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace Dbounded

noncomputable section

/-- The source of the chosen unit mapping-cone isomorphism in W1464. -/
abbrev unitMappingConeIsoSourceW1464
    (boundedHomotopyLocalizedRightAdjoint :
      BoundedHomotopyLocalizedCategoryW1461 ⥤
        BoundedComplexCategory MetrizableLCA.{0})
    (boundedHomotopyLocalizedAdjunctionUnit :
      𝟭 (BoundedComplexCategory MetrizableLCA.{0}) ⟶
        boundedHomotopyLocalizedVerdierFunctorW1461 ⋙
          boundedHomotopyLocalizedRightAdjoint)
    (X : BoundedComplexCategory MetrizableLCA.{0}) :
    HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ) :=
  (HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
    (CochainComplex.mappingCone
      ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
        (boundedHomotopyLocalizedAdjunctionUnit.app X)))

/--
W1464 replaces W1463's chosen unit mapping-cone isomorphism by explicit
hom/inv fields and the two inverse identities used to construct that isomorphism.
-/
structure W987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionInputW1464 :
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
  unitMappingConeIsoHom :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      unitMappingConeIsoSourceW1464
          boundedHomotopyLocalizedRightAdjoint
          boundedHomotopyLocalizedAdjunctionUnit
          X ⟶
        unitMappingConeModel X
  unitMappingConeIsoInv :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      unitMappingConeModel X ⟶
        unitMappingConeIsoSourceW1464
          boundedHomotopyLocalizedRightAdjoint
          boundedHomotopyLocalizedAdjunctionUnit
          X
  unitMappingConeIsoHomInvId :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      unitMappingConeIsoHom X ≫ unitMappingConeIsoInv X =
        𝟙 (unitMappingConeIsoSourceW1464
          boundedHomotopyLocalizedRightAdjoint
          boundedHomotopyLocalizedAdjunctionUnit
          X)
  unitMappingConeIsoInvHomId :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      unitMappingConeIsoInv X ≫ unitMappingConeIsoHom X =
        𝟙 (unitMappingConeModel X)

/-- W1464 constructs the chosen unit mapping-cone isomorphism from hom/inv fields. -/
def unitMappingConeIsoOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464
    (input :
      W987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionInputW1464) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      unitMappingConeIsoSourceW1464
          input.boundedHomotopyLocalizedRightAdjoint
          input.boundedHomotopyLocalizedAdjunctionUnit
          X ≅
        input.unitMappingConeModel X :=
  fun X =>
    { hom := input.unitMappingConeIsoHom X
      inv := input.unitMappingConeIsoInv X
      hom_inv_id := input.unitMappingConeIsoHomInvId X
      inv_hom_id := input.unitMappingConeIsoInvHomId X }

/-- W1464 builds the W1463 input after constructing the unit mapping-cone isomorphism. -/
def w1463InputOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464
    (input :
      W987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionInputW1464) :
    W987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputW1463 where
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
  unitMappingConeIso :=
    unitMappingConeIsoOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464
      input

/-- W1464 builds W981 unit strict-exact/isomorphism data through W1463. -/
def unitStrictExactIsoDataOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464
    (input :
      W987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionInputW1464) :
    UnitMappingConeStrictExactIsoDataProviderW981
      (localizedAdjunctionDataOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
        (w1463InputOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464
          input)) :=
  unitStrictExactIsoDataOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
    (w1463InputOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464
      input)

/-- W1464 builds W945 localized-unit data through W1463. -/
def localizedUnitDataOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464
    (input :
      W987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionInputW1464) :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945 :=
  localizedUnitDataOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
    (w1463InputOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464
      input)

/-- W1464 builds W730 boundary/relation data through W1463. -/
def boundaryRelationDataOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464
    (input :
      W987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionInputW1464) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
    (w1463InputOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464
      input)

/-- W1464 builds W986 target/endpoint data through W1463. -/
def targetNormalizedEndpointDataOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464
    (input :
      W987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionInputW1464) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetNormalizedEndpointDataOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
    (w1463InputOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464
      input)

/-- W1464 builds W987 full data through W1463. -/
noncomputable def fullDataOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464
    (input :
      W987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionInputW1464) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfW987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataW1463
    (w1463InputOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464
      input)

/-- W1464's constructed unit mapping-cone isomorphism keeps the hom field. -/
theorem w1464UnitMappingConeIsoKeepsHom
    (input :
      W987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionInputW1464)
    (X : BoundedComplexCategory MetrizableLCA.{0}) :
    (unitMappingConeIsoOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464
        input X).hom =
      input.unitMappingConeIsoHom X :=
  rfl

/-- W1464's constructed unit mapping-cone isomorphism keeps the inv field. -/
theorem w1464UnitMappingConeIsoKeepsInv
    (input :
      W987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionInputW1464)
    (X : BoundedComplexCategory MetrizableLCA.{0}) :
    (unitMappingConeIsoOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464
        input X).inv =
      input.unitMappingConeIsoInv X :=
  rfl

/-- W1464's W1463 input keeps the constructed unit mapping-cone isomorphism. -/
theorem w1464W1463InputKeepsConstructedUnitMappingConeIso
    (input :
      W987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionInputW1464) :
    (w1463InputOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464
        input).unitMappingConeIso =
      unitMappingConeIsoOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464
        input :=
  rfl

/-- W1464's W1463 input keeps the unit mapping-cone model. -/
theorem w1464W1463InputKeepsUnitMappingConeModel
    (input :
      W987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionInputW1464) :
    (w1463InputOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464
        input).unitMappingConeModel =
      input.unitMappingConeModel :=
  rfl

/-- W1464's constructed W945 data keeps the localized right adjoint. -/
theorem w1464LocalizedUnitDataKeepsLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionInputW1464) :
    boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
        (localizedUnitDataOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464
          input) =
      input.boundedHomotopyLocalizedRightAdjoint :=
  rfl

/-- W1464's constructed W987 provider projects to the constructed W730 data. -/
theorem w1464FullDataKeepsConstructedBoundaryRelation
    (input :
      W987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionInputW1464) :
    boundaryRelationDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464
          input) =
      boundaryRelationDataOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464
        input :=
  rfl

/-- W1464's constructed W987 provider projects to the constructed W986 data. -/
theorem w1464FullDataKeepsConstructedTargetNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionInputW1464) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464
          input) =
      targetNormalizedEndpointDataOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464
        input :=
  rfl

def w987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionInputNamesW1464 :
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
    "unit mapping-cone isomorphism hom",
    "unit mapping-cone isomorphism inv",
    "unit mapping-cone isomorphism hom-inv identity",
    "unit mapping-cone isomorphism inv-hom identity"]

theorem w987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionInputNamesW1464_count :
    w987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionInputNamesW1464.length =
      30 :=
  rfl

def w987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionIsoInputNamesW1464 :
    List String :=
  ["unit mapping-cone chosen isomorphism"]

theorem w987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionIsoInputNamesW1464_count :
    w987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionIsoInputNamesW1464.length =
      1 :=
  rfl

def w987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionComponentInputNamesW1464 :
    List String :=
  ["unit mapping-cone isomorphism hom",
    "unit mapping-cone isomorphism inv",
    "unit mapping-cone isomorphism hom-inv identity",
    "unit mapping-cone isomorphism inv-hom identity"]

theorem w987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionComponentInputNamesW1464_count :
    w987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionComponentInputNamesW1464.length =
      4 :=
  rfl

/-- W1464 splits W1463's chosen unit mapping-cone isomorphism into four fields. -/
theorem w1464BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionSplitsIsoInput :
    w987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionIsoInputNamesW1464.length <
      w987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionComponentInputNamesW1464.length := by
  rw [
    w987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionIsoInputNamesW1464_count,
    w987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionComponentInputNamesW1464_count]
  norm_num

/-- W1464 replaces the twenty-seven W1463 inputs by thirty named inputs. -/
theorem w1464BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionExpandsW1463InputCount :
    w987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputNamesW1463.length <
      w987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionInputNamesW1464.length := by
  rw [w987BoundaryRelationTargetEndpointKernelCokernelTopFieldDataConstructionInputNamesW1463_count,
    w987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionInputNamesW1464_count]
  norm_num

/-- Current W1464 nonterminal unit mapping-cone isomorphism construction state. -/
structure W987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionStateW1464 :
    Type where
  seed : String
  declarations : List String
  constructionResult : String
  projectionResult : String
  isoComponentInputNames : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1464 records the hom/inv-to-iso construction path. -/
def currentW987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionStateW1464 :
    W987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionStateW1464 where
  seed :=
    "w1464-w987-boundary-relation-target-unit-iso-hom-inv-field-data-construction"
  declarations :=
    ["W987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionInputW1464",
      "unitMappingConeIsoOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464",
      "w1463InputOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464",
      "unitStrictExactIsoDataOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464",
      "localizedUnitDataOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464",
      "boundaryRelationDataOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464",
      "targetNormalizedEndpointDataOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464",
      "fullDataOfW987BoundaryRelationTargetUnitIsoHomInvFieldDataW1464",
      "w1464UnitMappingConeIsoKeepsHom",
      "w1464UnitMappingConeIsoKeepsInv",
      "w1464W1463InputKeepsConstructedUnitMappingConeIso",
      "w1464W1463InputKeepsUnitMappingConeModel",
      "w1464LocalizedUnitDataKeepsLocalizedRightAdjoint",
      "w1464FullDataKeepsConstructedBoundaryRelation",
      "w1464FullDataKeepsConstructedTargetNormalizedEndpoint",
      "w987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionInputNamesW1464_count",
      "w987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionIsoInputNamesW1464_count",
      "w987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionComponentInputNamesW1464_count",
      "w1464BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionSplitsIsoInput",
      "w1464BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionExpandsW1463InputCount"]
  constructionResult :=
    "proved: W1464 constructs the unit mapping-cone isomorphism from hom, inv,\
      hom-inv, and inv-hom fields, then feeds that constructed isomorphism into W1463"
  projectionResult :=
    "proved: the constructed unit mapping-cone isomorphism feeds W1463 while\
      preserving localized-unit, boundary, and target/endpoint projections;\
      product success is still not claimed"
  isoComponentInputNames :=
    w987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionComponentInputNamesW1464
  remainingInputs :=
    w987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionInputNamesW1464
  productSuccessClaimed := false

theorem currentW1464W987BoundaryRelationTargetUnitIsoHomInvFieldDataConstruction_productSuccess :
    currentW987BoundaryRelationTargetUnitIsoHomInvFieldDataConstructionStateW1464.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
