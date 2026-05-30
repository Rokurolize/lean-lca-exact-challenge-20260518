import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987BoundaryRelationTargetLocalizedUnitFieldDataConstructionGuardW1459
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataRoute

/-!
W1460 refines W1459 by constructing its W939 unit-component witness from the
W981-style unit mapping-cone model, strict short-exact family, and chosen
isomorphism fields, then runs the resulting data through the W1459 W987
construction.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/--
W1460 replaces the W1459 W939 unit-component witness by the three W981 unit
mapping-cone fields.
-/
structure W987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputW1460 :
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
    MorphismProperty.Localization
        ((exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).trW) ⥤
      BoundedComplexCategory MetrizableLCA.{0}
  boundedHomotopyLocalizedAdjunction :
    boundedHomotopyLocalizedVerdierFunctor MetrizableLCA.{0} ⊣
      boundedHomotopyLocalizedRightAdjoint
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
              (boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
        unitMappingConeModel X)

/-- W1460 builds W975 localized-adjunction data from explicit fields. -/
def localizedAdjunctionDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
    (input :
      W987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputW1460) :
    BoundedHomotopyLocalizedAdjunctionDataProviderW975 where
  boundedHomotopyLocalizedRightAdjoint :=
    input.boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedAdjunction :=
    input.boundedHomotopyLocalizedAdjunction

/-- W1460 builds W981 unit strict-exact/isomorphism data from three fields. -/
def unitStrictExactIsoDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
    (input :
      W987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputW1460) :
    UnitMappingConeStrictExactIsoDataProviderW981
      (localizedAdjunctionDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
        input) where
  unitMappingConeModel := input.unitMappingConeModel
  unitMappingConeStrictExact := input.unitMappingConeStrictExact
  unitMappingConeIso := input.unitMappingConeIso

/-- W1460 builds the W939 unit-component witness from W981-style fields. -/
def unitComponentsOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
    (input :
      W987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputW1460) :
    boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponentsPrimitiveW939
      input.boundedHomotopyLocalizedRightAdjoint
      input.boundedHomotopyLocalizedAdjunction :=
  fun X =>
    ⟨input.unitMappingConeModel X,
      fun i => (input.unitMappingConeStrictExact X i).closed_inclusion,
      fun i => (input.unitMappingConeStrictExact X i).open_map,
      fun i => (input.unitMappingConeStrictExact X i).surjective,
      fun i => (input.unitMappingConeStrictExact X i).algebraic_exact,
      ⟨input.unitMappingConeIso X⟩⟩

/-- W1460 builds the W1459 input after constructing W939 data. -/
def w1459InputOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
    (input :
      W987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputW1460) :
    W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459 where
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
    input.boundedHomotopyLocalizedAdjunction
  boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents :=
    unitComponentsOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
      input

/-- W1460 builds W945 localized-unit data through W1459. -/
def localizedUnitDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
    (input :
      W987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputW1460) :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945 :=
  localizedUnitDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
    (w1459InputOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
      input)

/-- W1460 builds the W1458 input through W1459. -/
def w1458InputOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
    (input :
      W987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputW1460) :
    W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458 :=
  w1458InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
    (w1459InputOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
      input)

/-- W1460 builds W948 normalized-source data through W1459. -/
def normalizedSourceTriangulationDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
    (input :
      W987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputW1460) :
    NormalizedFixedTargetSourceTriangulationDataProviderW948 :=
  normalizedSourceTriangulationDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
    (w1459InputOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
      input)

/-- W1460 builds W949 endpoint-localized-unit data through W1459. -/
def endpointLocalizedUnitDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
    (input :
      W987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputW1460) :
    EndpointStrictExactLocalizedUnitDataProviderW949 :=
  endpointLocalizedUnitDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
    (w1459InputOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
      input)

/-- W1460 builds W730 boundary/relation data through W1459. -/
def boundaryRelationDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
    (input :
      W987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputW1460) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
    (w1459InputOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
      input)

/-- W1460 builds W986 target/endpoint data through W1459. -/
def targetNormalizedEndpointDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
    (input :
      W987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputW1460) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetNormalizedEndpointDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
    (w1459InputOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
      input)

/-- W1460 builds W987 full data through W1459. -/
noncomputable def fullDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
    (input :
      W987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputW1460) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
    (w1459InputOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
      input)

/-- W1460's W975 data keeps the localized right adjoint. -/
theorem w1460LocalizedAdjunctionDataKeepsRightAdjoint
    (input :
      W987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputW1460) :
    (localizedAdjunctionDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
        input).boundedHomotopyLocalizedRightAdjoint =
      input.boundedHomotopyLocalizedRightAdjoint :=
  rfl

/-- W1460's W975 data keeps the localized adjunction. -/
theorem w1460LocalizedAdjunctionDataKeepsAdjunction
    (input :
      W987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputW1460) :
    (localizedAdjunctionDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
        input).boundedHomotopyLocalizedAdjunction =
      input.boundedHomotopyLocalizedAdjunction :=
  rfl

/-- W1460's W981 unit data keeps the unit mapping-cone model. -/
theorem w1460UnitStrictExactIsoDataKeepsModel
    (input :
      W987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputW1460) :
    (unitStrictExactIsoDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
        input).unitMappingConeModel =
      input.unitMappingConeModel :=
  rfl

/-- W1460's W981 unit data keeps the strict short-exact family. -/
theorem w1460UnitStrictExactIsoDataKeepsStrictExact
    (input :
      W987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputW1460) :
    (unitStrictExactIsoDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
        input).unitMappingConeStrictExact =
      input.unitMappingConeStrictExact :=
  rfl

/-- W1460's W981 unit data keeps the chosen isomorphism field. -/
theorem w1460UnitStrictExactIsoDataKeepsIso
    (input :
      W987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputW1460) :
    (unitStrictExactIsoDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
        input).unitMappingConeIso =
      input.unitMappingConeIso :=
  rfl

/-- W1460's W1459 input keeps the constructed W939 witness. -/
theorem w1460W1459InputKeepsConstructedUnitComponents
    (input :
      W987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputW1460) :
    (w1459InputOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
        input).boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents =
      unitComponentsOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
        input :=
  rfl

/-- W1460's constructed W945 data keeps the localized right adjoint. -/
theorem w1460LocalizedUnitDataKeepsLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputW1460) :
    boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
        (localizedUnitDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
          input) =
      input.boundedHomotopyLocalizedRightAdjoint :=
  rfl

/-- W1460's constructed W945 data keeps the localized adjunction. -/
theorem w1460LocalizedUnitDataKeepsLocalizedAdjunction
    (input :
      W987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputW1460) :
    boundedHomotopyLocalizedAdjunctionOfLocalizedUnitDataW945
        (localizedUnitDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
          input) =
      input.boundedHomotopyLocalizedAdjunction :=
  rfl

/-- W1460's constructed W945 data keeps the constructed W939 witness. -/
theorem w1460LocalizedUnitDataKeepsConstructedUnitComponents
    (input :
      W987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputW1460) :
    boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponentsOfLocalizedUnitDataW945
        (localizedUnitDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
          input) =
      unitComponentsOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
        input :=
  rfl

/-- W1460's W949 data keeps the constructed W945 data. -/
theorem w1460EndpointLocalizedUnitDataKeepsConstructedLocalizedUnitData
    (input :
      W987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputW1460) :
    localizedUnitDataOfEndpointLocalizedUnitDataW949
        (endpointLocalizedUnitDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
          input) =
      localizedUnitDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
        input :=
  rfl

/-- W1460's W987 provider projects to the constructed W730 data. -/
theorem w1460FullDataKeepsConstructedBoundaryRelation
    (input :
      W987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputW1460) :
    boundaryRelationDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
          input) =
      boundaryRelationDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
        input :=
  rfl

/-- W1460's W987 provider projects to the constructed W986 data. -/
theorem w1460FullDataKeepsConstructedTargetNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputW1460) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
          input) =
      targetNormalizedEndpointDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460
        input :=
  rfl

def w987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputNamesW1460 :
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
    "bounded homotopy localized adjunction",
    "unit mapping-cone model",
    "unit mapping-cone strict short-exact family",
    "unit mapping-cone chosen isomorphism"]

theorem w987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputNamesW1460_count :
    w987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputNamesW1460.length =
      18 :=
  rfl

def w987BoundaryRelationTargetUnitMappingConeFieldDataConstructionBundledUnitComponentInputNamesW1460 :
    List String :=
  ["W939 unit mapping-cone component witness"]

theorem w987BoundaryRelationTargetUnitMappingConeFieldDataConstructionBundledUnitComponentInputNamesW1460_count :
    w987BoundaryRelationTargetUnitMappingConeFieldDataConstructionBundledUnitComponentInputNamesW1460.length =
      1 :=
  rfl

def w987BoundaryRelationTargetUnitMappingConeFieldDataConstructionUnitMappingConeInputNamesW1460 :
    List String :=
  unitStrictExactIsoDataInputNamesW981

theorem w987BoundaryRelationTargetUnitMappingConeFieldDataConstructionUnitMappingConeInputNamesW1460_count :
    w987BoundaryRelationTargetUnitMappingConeFieldDataConstructionUnitMappingConeInputNamesW1460.length =
      3 :=
  unitStrictExactIsoDataInputNamesW981_count

/-- W1460 splits W1459's W939 unit-component witness into three W981 fields. -/
theorem w1460BoundaryRelationTargetUnitMappingConeFieldDataConstructionSplitsW939Input :
    w987BoundaryRelationTargetUnitMappingConeFieldDataConstructionBundledUnitComponentInputNamesW1460.length <
      w987BoundaryRelationTargetUnitMappingConeFieldDataConstructionUnitMappingConeInputNamesW1460.length := by
  rw [
    w987BoundaryRelationTargetUnitMappingConeFieldDataConstructionBundledUnitComponentInputNamesW1460_count,
    w987BoundaryRelationTargetUnitMappingConeFieldDataConstructionUnitMappingConeInputNamesW1460_count]
  norm_num

/-- W1460 replaces the sixteen W1459 inputs by eighteen named construction inputs. -/
theorem w1460BoundaryRelationTargetUnitMappingConeFieldDataConstructionExpandsW1459InputCount :
    w987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputNamesW1459.length <
      w987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputNamesW1460.length := by
  rw [w987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputNamesW1459_count,
    w987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputNamesW1460_count]
  norm_num

/-- Current W1460 nonterminal unit mapping-cone construction state. -/
structure W987BoundaryRelationTargetUnitMappingConeFieldDataConstructionStateW1460 :
    Type where
  seed : String
  declarations : List String
  constructionResult : String
  projectionResult : String
  unitMappingConeInputNames : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1460 records the W981-style construction path into W1459. -/
def currentW987BoundaryRelationTargetUnitMappingConeFieldDataConstructionStateW1460 :
    W987BoundaryRelationTargetUnitMappingConeFieldDataConstructionStateW1460 where
  seed :=
    "w1460-w987-boundary-relation-target-unit-mapping-cone-field-data-construction"
  declarations :=
    ["W987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputW1460",
      "localizedAdjunctionDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460",
      "unitStrictExactIsoDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460",
      "unitComponentsOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460",
      "w1459InputOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460",
      "localizedUnitDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460",
      "w1458InputOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460",
      "normalizedSourceTriangulationDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460",
      "endpointLocalizedUnitDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460",
      "boundaryRelationDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460",
      "targetNormalizedEndpointDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460",
      "fullDataOfW987BoundaryRelationTargetUnitMappingConeFieldDataW1460",
      "w1460LocalizedAdjunctionDataKeepsRightAdjoint",
      "w1460LocalizedAdjunctionDataKeepsAdjunction",
      "w1460UnitStrictExactIsoDataKeepsModel",
      "w1460UnitStrictExactIsoDataKeepsStrictExact",
      "w1460UnitStrictExactIsoDataKeepsIso",
      "w1460W1459InputKeepsConstructedUnitComponents",
      "w1460LocalizedUnitDataKeepsLocalizedRightAdjoint",
      "w1460LocalizedUnitDataKeepsLocalizedAdjunction",
      "w1460LocalizedUnitDataKeepsConstructedUnitComponents",
      "w1460EndpointLocalizedUnitDataKeepsConstructedLocalizedUnitData",
      "w1460FullDataKeepsConstructedBoundaryRelation",
      "w1460FullDataKeepsConstructedTargetNormalizedEndpoint",
      "w987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputNamesW1460_count",
      "w987BoundaryRelationTargetUnitMappingConeFieldDataConstructionBundledUnitComponentInputNamesW1460_count",
      "w987BoundaryRelationTargetUnitMappingConeFieldDataConstructionUnitMappingConeInputNamesW1460_count",
      "w1460BoundaryRelationTargetUnitMappingConeFieldDataConstructionSplitsW939Input",
      "w1460BoundaryRelationTargetUnitMappingConeFieldDataConstructionExpandsW1459InputCount"]
  constructionResult :=
    "proved: W1460 constructs W975 data, W981 unit strict-exact/isomorphism\
      data, and the W939 unit-component witness from the localized adjunction\
      fields plus a unit mapping-cone model, strict short-exact family, and\
      chosen isomorphism"
  projectionResult :=
    "proved: the constructed W939 witness feeds W1459, whose W945/W949/W987\
      projections still return to the constructed localized-unit, boundary,\
      and target/endpoint data"
  unitMappingConeInputNames :=
    w987BoundaryRelationTargetUnitMappingConeFieldDataConstructionUnitMappingConeInputNamesW1460
  remainingInputs :=
    w987BoundaryRelationTargetUnitMappingConeFieldDataConstructionInputNamesW1460
  productSuccessClaimed := false

theorem currentW1460W987BoundaryRelationTargetUnitMappingConeFieldDataConstruction_productSuccess :
    currentW987BoundaryRelationTargetUnitMappingConeFieldDataConstructionStateW1460.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
