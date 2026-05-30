import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987BoundaryRelationTargetUnitMappingConeFieldDataConstructionGuardW1460

/-!
W1461 refines W1460 by constructing its localized adjunction from explicit
unit, counit, and triangle-identity fields via `Adjunction.mkOfUnitCounit`,
then runs the resulting data through the W1460 W987 construction.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

noncomputable section

abbrev BoundedHomotopyLocalizedCategoryW1461 :=
  MorphismProperty.Localization
    ((exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).trW)

abbrev boundedHomotopyLocalizedVerdierFunctorW1461 :
    BoundedComplexCategory MetrizableLCA.{0} ⥤
      BoundedHomotopyLocalizedCategoryW1461 :=
  boundedHomotopyLocalizedVerdierFunctor MetrizableLCA.{0}

/--
W1461 replaces the W1460 bundled localized adjunction by the unit, counit,
and triangle fields used to construct that adjunction.
-/
structure W987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputW1461 :
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
  unitMappingConeStrictExact :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact ((unitMappingConeModel X).as.sc i)
  unitMappingConeIso :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
          (CochainComplex.mappingCone
            ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
              (boundedHomotopyLocalizedAdjunctionUnit.app X)))) ≅
        unitMappingConeModel X)

/-- W1461 packages the explicit localized-adjunction fields as mathlib core data. -/
def localizedAdjunctionCoreOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputW1461) :
    Adjunction.CoreUnitCounit
      boundedHomotopyLocalizedVerdierFunctorW1461
      input.boundedHomotopyLocalizedRightAdjoint where
  unit := input.boundedHomotopyLocalizedAdjunctionUnit
  counit := input.boundedHomotopyLocalizedAdjunctionCounit
  left_triangle := input.boundedHomotopyLocalizedAdjunctionLeftTriangle
  right_triangle := input.boundedHomotopyLocalizedAdjunctionRightTriangle

/-- W1461 constructs the localized adjunction from its unit/counit core. -/
def localizedAdjunctionOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputW1461) :
    boundedHomotopyLocalizedVerdierFunctorW1461 ⊣
      input.boundedHomotopyLocalizedRightAdjoint :=
  Adjunction.mkOfUnitCounit
    (localizedAdjunctionCoreOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
      input)

/-- W1461 builds the W1460 input after constructing the localized adjunction. -/
def w1460InputOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputW1461) :
    W987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputW1460 where
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
  boundedHomotopyLocalizedAdjunction :=
    localizedAdjunctionOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
      input
  unitMappingConeModel := input.unitMappingConeModel
  unitMappingConeStrictExact := input.unitMappingConeStrictExact
  unitMappingConeIso := input.unitMappingConeIso

/-- W1461 builds W975 localized-adjunction data through W1460. -/
def localizedAdjunctionDataOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputW1461) :
    BoundedHomotopyLocalizedAdjunctionDataProviderW975 :=
  localizedAdjunctionDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
    (w1460InputOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
      input)

/-- W1461 builds W981 unit strict-exact/isomorphism data through W1460. -/
def unitStrictExactIsoDataOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputW1461) :
    UnitMappingConeStrictExactIsoDataProviderW981
      (localizedAdjunctionDataOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
        input) :=
  unitStrictExactIsoDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
    (w1460InputOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
      input)

/-- W1461 builds the W939 unit-component witness through W1460. -/
def unitComponentsOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputW1461) :
    boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponentsPrimitiveW939
      input.boundedHomotopyLocalizedRightAdjoint
      (localizedAdjunctionOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
        input) :=
  unitComponentsOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
    (w1460InputOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
      input)

/-- W1461 builds W945 localized-unit data through W1460. -/
def localizedUnitDataOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputW1461) :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945 :=
  localizedUnitDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
    (w1460InputOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
      input)

/-- W1461 builds W730 boundary/relation data through W1460. -/
def boundaryRelationDataOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputW1461) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
    (w1460InputOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
      input)

/-- W1461 builds W986 target/endpoint data through W1460. -/
def targetNormalizedEndpointDataOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputW1461) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetNormalizedEndpointDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
    (w1460InputOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
      input)

/-- W1461 builds W987 full data through W1460. -/
noncomputable def fullDataOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputW1461) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
    (w1460InputOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
      input)

/-- W1461's core data keeps the unit field. -/
theorem w1461LocalizedAdjunctionCoreKeepsUnit
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputW1461) :
    (localizedAdjunctionCoreOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
        input).unit =
      input.boundedHomotopyLocalizedAdjunctionUnit :=
  rfl

/-- W1461's core data keeps the counit field. -/
theorem w1461LocalizedAdjunctionCoreKeepsCounit
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputW1461) :
    (localizedAdjunctionCoreOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
        input).counit =
      input.boundedHomotopyLocalizedAdjunctionCounit :=
  rfl

/-- W1461's constructed adjunction keeps the unit field. -/
theorem w1461ConstructedLocalizedAdjunctionKeepsUnit
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputW1461) :
    (localizedAdjunctionOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
        input).unit =
      input.boundedHomotopyLocalizedAdjunctionUnit :=
  rfl

/-- W1461's constructed adjunction keeps the counit field. -/
theorem w1461ConstructedLocalizedAdjunctionKeepsCounit
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputW1461) :
    (localizedAdjunctionOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
        input).counit =
      input.boundedHomotopyLocalizedAdjunctionCounit :=
  rfl

/-- W1461's W1460 input keeps the constructed localized adjunction. -/
theorem w1461W1460InputKeepsConstructedLocalizedAdjunction
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputW1461) :
    (w1460InputOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
        input).boundedHomotopyLocalizedAdjunction =
      localizedAdjunctionOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
        input :=
  rfl

/-- W1461's W1460 input keeps the chosen unit mapping-cone model. -/
theorem w1461W1460InputKeepsUnitMappingConeModel
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputW1461) :
    (w1460InputOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
        input).unitMappingConeModel =
      input.unitMappingConeModel :=
  rfl

/-- W1461's W1460 input keeps the unit mapping-cone strict exactness. -/
theorem w1461W1460InputKeepsUnitMappingConeStrictExact
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputW1461) :
    (w1460InputOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
        input).unitMappingConeStrictExact =
      input.unitMappingConeStrictExact :=
  rfl

/-- W1461's constructed W945 data keeps the localized right adjoint. -/
theorem w1461LocalizedUnitDataKeepsLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputW1461) :
    boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
        (localizedUnitDataOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
          input) =
      input.boundedHomotopyLocalizedRightAdjoint :=
  rfl

/-- W1461's constructed W945 data keeps the constructed localized adjunction. -/
theorem w1461LocalizedUnitDataKeepsConstructedLocalizedAdjunction
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputW1461) :
    boundedHomotopyLocalizedAdjunctionOfLocalizedUnitDataW945
        (localizedUnitDataOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
          input) =
      localizedAdjunctionOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
        input :=
  rfl

/-- W1461's constructed W987 provider projects to the constructed W730 data. -/
theorem w1461FullDataKeepsConstructedBoundaryRelation
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputW1461) :
    boundaryRelationDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
          input) =
      boundaryRelationDataOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
        input :=
  rfl

/-- W1461's constructed W987 provider projects to the constructed W986 data. -/
theorem w1461FullDataKeepsConstructedTargetNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputW1461) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
          input) =
      targetNormalizedEndpointDataOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461
        input :=
  rfl

def w987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputNamesW1461 :
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
    "unit mapping-cone strict short-exact family",
    "unit mapping-cone chosen isomorphism"]

theorem w987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputNamesW1461_count :
    w987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputNamesW1461.length =
      21 :=
  rfl

def w987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionBundledAdjunctionInputNamesW1461 :
    List String :=
  ["bounded homotopy localized adjunction"]

theorem w987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionBundledAdjunctionInputNamesW1461_count :
    w987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionBundledAdjunctionInputNamesW1461.length =
      1 :=
  rfl

def w987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionCoreInputNamesW1461 :
    List String :=
  ["localized adjunction unit natural transformation",
    "localized adjunction counit natural transformation",
    "localized adjunction left triangle identity",
    "localized adjunction right triangle identity"]

theorem w987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionCoreInputNamesW1461_count :
    w987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionCoreInputNamesW1461.length =
      4 :=
  rfl

/-- W1461 splits W1460's bundled localized adjunction into four core fields. -/
theorem w1461BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionSplitsAdjunctionInput :
    w987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionBundledAdjunctionInputNamesW1461.length <
      w987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionCoreInputNamesW1461.length := by
  rw [
    w987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionBundledAdjunctionInputNamesW1461_count,
    w987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionCoreInputNamesW1461_count]
  norm_num

/-- W1461 replaces the eighteen W1460 inputs by twenty-one named construction inputs. -/
theorem w1461BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionExpandsW1460InputCount :
    w987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputNamesW1460.length <
      w987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputNamesW1461.length := by
  rw [w987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputNamesW1460_count,
    w987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputNamesW1461_count]
  norm_num

/-- Current W1461 nonterminal localized-adjunction core construction state. -/
structure W987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionStateW1461 :
    Type where
  seed : String
  declarations : List String
  constructionResult : String
  projectionResult : String
  localizedAdjunctionCoreInputNames : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1461 records the core unit/counit construction path into W1460. -/
def currentW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionStateW1461 :
    W987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionStateW1461 where
  seed :=
    "w1461-w987-boundary-relation-target-localized-adjunction-core-field-data-construction"
  declarations :=
    ["W987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputW1461",
      "localizedAdjunctionCoreOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461",
      "localizedAdjunctionOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461",
      "w1460InputOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461",
      "localizedAdjunctionDataOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461",
      "unitStrictExactIsoDataOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461",
      "unitComponentsOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461",
      "localizedUnitDataOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461",
      "boundaryRelationDataOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461",
      "targetNormalizedEndpointDataOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461",
      "fullDataOfW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataW1461",
      "w1461LocalizedAdjunctionCoreKeepsUnit",
      "w1461LocalizedAdjunctionCoreKeepsCounit",
      "w1461ConstructedLocalizedAdjunctionKeepsUnit",
      "w1461ConstructedLocalizedAdjunctionKeepsCounit",
      "w1461W1460InputKeepsConstructedLocalizedAdjunction",
      "w1461W1460InputKeepsUnitMappingConeModel",
      "w1461W1460InputKeepsUnitMappingConeStrictExact",
      "w1461LocalizedUnitDataKeepsLocalizedRightAdjoint",
      "w1461LocalizedUnitDataKeepsConstructedLocalizedAdjunction",
      "w1461FullDataKeepsConstructedBoundaryRelation",
      "w1461FullDataKeepsConstructedTargetNormalizedEndpoint",
      "w987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputNamesW1461_count",
      "w987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionBundledAdjunctionInputNamesW1461_count",
      "w987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionCoreInputNamesW1461_count",
      "w1461BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionSplitsAdjunctionInput",
      "w1461BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionExpandsW1460InputCount"]
  constructionResult :=
    "proved: W1461 constructs the localized adjunction with\
      Adjunction.mkOfUnitCounit from unit, counit, and triangle fields, then\
      feeds that constructed adjunction into the W1460 W981/W939/W987 route"
  projectionResult :=
    "proved: the constructed localized adjunction feeds W1460 while preserving\
      localized-unit, boundary, and target/endpoint projections; product\
      success is still not claimed"
  localizedAdjunctionCoreInputNames :=
    w987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionCoreInputNamesW1461
  remainingInputs :=
    w987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionInputNamesW1461
  productSuccessClaimed := false

theorem currentW1461W987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstruction_productSuccess :
    currentW987BoundaryRelationTargetLocalizedAdjunctionCoreFieldDataConstructionStateW1461.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
