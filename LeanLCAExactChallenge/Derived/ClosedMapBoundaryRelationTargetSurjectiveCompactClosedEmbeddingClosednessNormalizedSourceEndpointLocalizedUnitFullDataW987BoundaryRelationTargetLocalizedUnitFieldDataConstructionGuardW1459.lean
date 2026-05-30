import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987BoundaryRelationTargetSourceTriangulationFieldDataConstructionGuardW1458

/-!
W1459 refines W1458 by constructing its W945 localized-unit input from the
bounded-homotopy localized right adjoint, localized adjunction, and W939
unit-component witness, then runs the resulting data through the W1458/W1457/
W1456/W1455/W1454/W1453/W1452/W1451/W1450 W987 construction.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/--
W1459 replaces the W1458 W945 localized-unit input by the localized adjoint,
adjunction, and unit-component witness fields.
-/
structure W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459 :
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
  boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents :
    boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponentsPrimitiveW939
      boundedHomotopyLocalizedRightAdjoint
      boundedHomotopyLocalizedAdjunction

/-- W1459 builds W945 localized-unit data from three fields. -/
def localizedUnitDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945 where
  boundedHomotopyLocalizedRightAdjoint :=
    input.boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedAdjunction :=
    input.boundedHomotopyLocalizedAdjunction
  boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents :=
    input.boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents

/-- W1459 builds the W1458 input after constructing W945 data. -/
def w1458InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458 where
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
  localizedUnitData :=
    localizedUnitDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
      input

/-- W1459 builds W722 source-triangulation data through W1458. -/
def sourceTriangulationDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    MetrizableWppSourceTriangulationDataProviderW722 :=
  sourceTriangulationDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
    (w1458InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
      input)

/-- W1459 builds the W1457 input through W1458. -/
def w1457InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457 :=
  w1457InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
    (w1458InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
      input)

/-- W1459 builds W719 normalized fixed-target data through W1458. -/
def normalizedFixedTargetDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    MetrizableWppNormalizedFixedTargetDataProviderW719 :=
  normalizedFixedTargetDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
    (w1458InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
      input)

/-- W1459 builds the W1456 input through W1458. -/
def w1456InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456 :=
  w1456InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
    (w1458InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
      input)

/-- W1459 builds W948 normalized-source data through W1458. -/
def normalizedSourceTriangulationDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    NormalizedFixedTargetSourceTriangulationDataProviderW948 :=
  normalizedSourceTriangulationDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
    (w1458InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
      input)

/-- W1459 builds the W1455 input through W1458. -/
def w1455InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputW1455 :=
  w1455InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
    (w1458InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
      input)

/-- W1459 builds W949 endpoint-localized-unit data through W1458. -/
def endpointLocalizedUnitDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    EndpointStrictExactLocalizedUnitDataProviderW949 :=
  endpointLocalizedUnitDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
    (w1458InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
      input)

/-- W1459 builds W950 normalized-source/endpoint data through W1458. -/
def normalizedSourceEndpointLocalizedUnitDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950 :=
  normalizedSourceEndpointLocalizedUnitDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
    (w1458InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
      input)

/-- W1459 builds W984 target/closedness data through W1458. -/
def targetClosedEmbeddingClosednessDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    TargetNoUnivClosedEmbeddingClosednessDataProviderW984 :=
  targetClosedEmbeddingClosednessDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
    (w1458InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
      input)

/-- W1459 builds W717 relation data through W1458. -/
def relationDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    ClosedNatTransOrdinaryRelationDataProviderW717 :=
  relationDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
    (w1458InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
      input)

/-- W1459 builds W716 boundary data through W1458. -/
def boundaryDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    MetrizableWppLimitBoundaryDataW716 :=
  boundaryDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
    (w1458InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
      input)

/-- W1459 builds W730 boundary/relation data through W1458. -/
def boundaryRelationDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
    (w1458InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
      input)

/-- W1459 builds W986 target/endpoint data through W1458. -/
def targetNormalizedEndpointDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetNormalizedEndpointDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
    (w1458InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
      input)

/-- W1459 builds the remaining W987 full-data provider through W1458. -/
noncomputable def fullDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
    (w1458InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
      input)

/-- W1459's constructed W945 data keeps the localized right adjoint. -/
theorem w1459LocalizedUnitDataKeepsLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
        (localizedUnitDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
          input) =
      input.boundedHomotopyLocalizedRightAdjoint :=
  rfl

/-- W1459's constructed W945 data keeps the localized adjunction. -/
theorem w1459LocalizedUnitDataKeepsLocalizedAdjunction
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    boundedHomotopyLocalizedAdjunctionOfLocalizedUnitDataW945
        (localizedUnitDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
          input) =
      input.boundedHomotopyLocalizedAdjunction :=
  rfl

/-- W1459's constructed W945 data keeps the W939 unit-component witness. -/
theorem w1459LocalizedUnitDataKeepsUnitComponents
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponentsOfLocalizedUnitDataW945
        (localizedUnitDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
          input) =
      input.boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents :=
  rfl

/-- W1459's W1458 input keeps the raw right-open boundary field. -/
theorem w1459InputKeepsRightOpenBoundary
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    (w1458InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
        input).rightOpenBoundary =
      input.rightOpenBoundary :=
  rfl

/-- W1459's W1458 input keeps the raw source-pi-zero boundary field. -/
theorem w1459InputKeepsSourcePiZeroBoundary
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    (w1458InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
        input).sourcePiZeroBoundary =
      input.sourcePiZeroBoundary :=
  rfl

/-- W1459's W1458 input keeps the raw relation-pullback field. -/
theorem w1459InputKeepsRelationPullbackProvider
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    (w1458InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
        input).relationPullbackProvider =
      input.relationPullbackProvider :=
  rfl

/-- W1459's W1458 input keeps the raw target-relation-lifts field. -/
theorem w1459InputKeepsTargetRelationLiftsProvider
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    (w1458InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
        input).targetRelationLiftsProvider =
      input.targetRelationLiftsProvider :=
  rfl

/-- W1459's W1458 input keeps the W944 target no-univ provider. -/
theorem w1459InputKeepsTargetNoUnivData
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    (w1458InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
        input).targetNoUnivData =
      input.targetNoUnivData :=
  rfl

/-- W1459's W1458 input keeps the W973 closedness provider. -/
theorem w1459InputKeepsClosedEmbeddingClosednessData
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    (w1458InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
        input).closedEmbeddingClosednessData =
      input.closedEmbeddingClosednessData :=
  rfl

/-- W1459's W1458 input keeps the normalized lift blueprint. -/
theorem w1459InputKeepsNormalizedLiftBlueprint
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    (w1458InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
        input).normalizedLiftBlueprint =
      input.normalizedLiftBlueprint :=
  rfl

/-- W1459's W1458 input keeps target fixed-target uniqueness. -/
theorem w1459InputKeepsTargetFixedTargetUniq
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    (w1458InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
        input).targetFixedTargetUniq =
      input.targetFixedTargetUniq :=
  rfl

/-- W1459's W1458 input keeps localization-model fixed-target uniqueness. -/
theorem w1459InputKeepsLocalizationModelFixedTargetUniq
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    (w1458InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
        input).localizationModelFixedTargetUniq =
      input.localizationModelFixedTargetUniq :=
  rfl

/-- W1459's W1458 input keeps the source pretriangulated structure. -/
theorem w1459InputKeepsSourcePretriangulated
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    (w1458InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
        input).sourcePretriangulated =
      input.sourcePretriangulated :=
  rfl

/-- W1459's W1458 input keeps the source triangulated structure. -/
theorem w1459InputKeepsSourceTriangulated
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    (w1458InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
        input).sourceTriangulated =
      input.sourceTriangulated :=
  rfl

/-- W1459's W1458 input keeps source triangle completion. -/
theorem w1459InputKeepsTriangleCompletion
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    (w1458InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
        input).triangleCompletion =
      input.triangleCompletion :=
  rfl

/-- W1459's W1458 input keeps the endpoint strict-exact witnesses. -/
theorem w1459InputKeepsEndpointStrictExact
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    (w1458InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
        input).endpointStrictExact =
      input.endpointStrictExact :=
  rfl

/-- W1459's W1458 input keeps the constructed W945 localized-unit data. -/
theorem w1459InputKeepsConstructedLocalizedUnitData
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    (w1458InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
        input).localizedUnitData =
      localizedUnitDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
        input :=
  rfl

/-- W1459's constructed W949 data keeps the endpoint strict-exact witnesses. -/
theorem w1459EndpointLocalizedUnitDataKeepsEndpointStrictExact
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    endpointStrictExactOfEndpointLocalizedUnitDataW949
        (endpointLocalizedUnitDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
          input) =
      input.endpointStrictExact :=
  rfl

/-- W1459's constructed W949 data keeps the constructed W945 data. -/
theorem w1459EndpointLocalizedUnitDataKeepsConstructedLocalizedUnitData
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    localizedUnitDataOfEndpointLocalizedUnitDataW949
        (endpointLocalizedUnitDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
          input) =
      localizedUnitDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
        input :=
  rfl

/-- W1459's constructed W950 data keeps the constructed W949 data. -/
theorem w1459NormalizedEndpointDataKeepsConstructedEndpointLocalizedUnitData
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitDataW950
        (normalizedSourceEndpointLocalizedUnitDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
          input) =
      endpointLocalizedUnitDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
        input :=
  rfl

/-- W1459's W1455 input keeps the constructed W945 data. -/
theorem w1459W1455InputKeepsConstructedLocalizedUnitData
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    (w1455InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
        input).localizedUnitData =
      localizedUnitDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
        input :=
  rfl

/-- W1459's W730 construction keeps the constructed W716 boundary data. -/
theorem w1459BoundaryRelationKeepsConstructedBoundaryData
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    boundaryData_of_boundaryRelationDataW730
        (boundaryRelationDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
          input) =
      boundaryDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
        input :=
  rfl

/-- W1459's W730 construction keeps the constructed W717 relation data. -/
theorem w1459BoundaryRelationKeepsConstructedRelationData
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    relationData_of_boundaryRelationDataW730
        (boundaryRelationDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
          input) =
      relationDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
        input :=
  rfl

/-- W1459's W986 construction keeps the constructed W984 target/closedness data. -/
theorem w1459TargetNormalizedEndpointKeepsConstructedTargetClosedness
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
        (targetNormalizedEndpointDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
          input) =
      targetClosedEmbeddingClosednessDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
        input :=
  rfl

/-- W1459's W986 construction keeps the constructed W950 normalized-endpoint data. -/
theorem w1459TargetNormalizedEndpointKeepsConstructedNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    normalizedSourceEndpointLocalizedUnitDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
        (targetNormalizedEndpointDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
          input) =
      normalizedSourceEndpointLocalizedUnitDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
        input :=
  rfl

/-- W1459's W987 provider projects to the constructed W730 data. -/
theorem w1459FullDataKeepsConstructedBoundaryRelation
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    boundaryRelationDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
          input) =
      boundaryRelationDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
        input :=
  rfl

/-- W1459's W987 provider projects to the constructed W986 target/endpoint data. -/
theorem w1459FullDataKeepsConstructedTargetNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
          input) =
      targetNormalizedEndpointDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459
        input :=
  rfl

def w987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputNamesW1459 :
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
    "W939 unit mapping-cone strict-exact component witness"]

theorem w987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputNamesW1459_count :
    w987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputNamesW1459.length =
      16 :=
  rfl

def w987BoundaryRelationTargetLocalizedUnitFieldDataConstructionBundledLocalizedUnitInputNamesW1459 :
    List String :=
  ["W945 localized-unit data"]

theorem w987BoundaryRelationTargetLocalizedUnitFieldDataConstructionBundledLocalizedUnitInputNamesW1459_count :
    w987BoundaryRelationTargetLocalizedUnitFieldDataConstructionBundledLocalizedUnitInputNamesW1459.length =
      1 :=
  rfl

def w987BoundaryRelationTargetLocalizedUnitFieldDataConstructionLocalizedUnitInputNamesW1459 :
    List String :=
  canonicalW945LocalizedUnitInnerInputNamesW1306

theorem w987BoundaryRelationTargetLocalizedUnitFieldDataConstructionLocalizedUnitInputNamesW1459_count :
    w987BoundaryRelationTargetLocalizedUnitFieldDataConstructionLocalizedUnitInputNamesW1459.length =
      3 :=
  canonicalW945LocalizedUnitInnerInputNamesW1306_count

/-- W1459 splits W1458's one W945 localized-unit input into three fields. -/
theorem w1459BoundaryRelationTargetLocalizedUnitFieldDataConstructionSplitsW945Input :
    w987BoundaryRelationTargetLocalizedUnitFieldDataConstructionBundledLocalizedUnitInputNamesW1459.length <
      w987BoundaryRelationTargetLocalizedUnitFieldDataConstructionLocalizedUnitInputNamesW1459.length := by
  rw [
    w987BoundaryRelationTargetLocalizedUnitFieldDataConstructionBundledLocalizedUnitInputNamesW1459_count,
    w987BoundaryRelationTargetLocalizedUnitFieldDataConstructionLocalizedUnitInputNamesW1459_count]
  norm_num

/-- W1459 replaces the fourteen W1458 inputs by sixteen named construction inputs. -/
theorem w1459BoundaryRelationTargetLocalizedUnitFieldDataConstructionExpandsW1458InputCount :
    w987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputNamesW1458.length <
      w987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputNamesW1459.length := by
  rw [w987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputNamesW1458_count,
    w987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputNamesW1459_count]
  norm_num

/-- Current W1459 nonterminal localized-unit construction state. -/
structure W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionStateW1459 :
    Type where
  seed : String
  declarations : List String
  constructionResult : String
  projectionResult : String
  localizedUnitInputNames : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1459 records the W945 construction path into W1458. -/
def currentW987BoundaryRelationTargetLocalizedUnitFieldDataConstructionStateW1459 :
    W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionStateW1459 where
  seed :=
    "w1459-w987-boundary-relation-target-localized-unit-field-data-construction"
  declarations :=
    ["W987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputW1459",
      "localizedUnitDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459",
      "w1458InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459",
      "sourceTriangulationDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459",
      "w1457InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459",
      "normalizedFixedTargetDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459",
      "w1456InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459",
      "normalizedSourceTriangulationDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459",
      "w1455InputOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459",
      "endpointLocalizedUnitDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459",
      "normalizedSourceEndpointLocalizedUnitDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459",
      "targetClosedEmbeddingClosednessDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459",
      "relationDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459",
      "boundaryDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459",
      "boundaryRelationDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459",
      "targetNormalizedEndpointDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459",
      "fullDataOfW987BoundaryRelationTargetLocalizedUnitFieldDataW1459",
      "w1459LocalizedUnitDataKeepsLocalizedRightAdjoint",
      "w1459LocalizedUnitDataKeepsLocalizedAdjunction",
      "w1459LocalizedUnitDataKeepsUnitComponents",
      "w1459InputKeepsRightOpenBoundary",
      "w1459InputKeepsSourcePiZeroBoundary",
      "w1459InputKeepsRelationPullbackProvider",
      "w1459InputKeepsTargetRelationLiftsProvider",
      "w1459InputKeepsTargetNoUnivData",
      "w1459InputKeepsClosedEmbeddingClosednessData",
      "w1459InputKeepsNormalizedLiftBlueprint",
      "w1459InputKeepsTargetFixedTargetUniq",
      "w1459InputKeepsLocalizationModelFixedTargetUniq",
      "w1459InputKeepsSourcePretriangulated",
      "w1459InputKeepsSourceTriangulated",
      "w1459InputKeepsTriangleCompletion",
      "w1459InputKeepsEndpointStrictExact",
      "w1459InputKeepsConstructedLocalizedUnitData",
      "w1459EndpointLocalizedUnitDataKeepsEndpointStrictExact",
      "w1459EndpointLocalizedUnitDataKeepsConstructedLocalizedUnitData",
      "w1459NormalizedEndpointDataKeepsConstructedEndpointLocalizedUnitData",
      "w1459W1455InputKeepsConstructedLocalizedUnitData",
      "w1459BoundaryRelationKeepsConstructedBoundaryData",
      "w1459BoundaryRelationKeepsConstructedRelationData",
      "w1459TargetNormalizedEndpointKeepsConstructedTargetClosedness",
      "w1459TargetNormalizedEndpointKeepsConstructedNormalizedEndpoint",
      "w1459FullDataKeepsConstructedBoundaryRelation",
      "w1459FullDataKeepsConstructedTargetNormalizedEndpoint",
      "w987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputNamesW1459_count",
      "w1459BoundaryRelationTargetLocalizedUnitFieldDataConstructionSplitsW945Input",
      "w1459BoundaryRelationTargetLocalizedUnitFieldDataConstructionExpandsW1458InputCount"]
  constructionResult :=
    "proved: W945 localized-unit data can be assembled from the bounded\
      homotopy localized right adjoint, localized adjunction, and W939\
      unit-component witness before running W1458's W987 construction"
  projectionResult :=
    "proved: the constructed W945, W949, W950, W730, W986, and W987 providers\
      project back to the W1459 localized-unit fields, endpoint field,\
      source-triangulation fields, fixed-target fields, target fields,\
      relation fields, and boundary fields"
  localizedUnitInputNames :=
    w987BoundaryRelationTargetLocalizedUnitFieldDataConstructionLocalizedUnitInputNamesW1459
  remainingInputs :=
    w987BoundaryRelationTargetLocalizedUnitFieldDataConstructionInputNamesW1459
  productSuccessClaimed := false

theorem currentW1459W987BoundaryRelationTargetLocalizedUnitFieldDataConstruction_productSuccess :
    currentW987BoundaryRelationTargetLocalizedUnitFieldDataConstructionStateW1459.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
