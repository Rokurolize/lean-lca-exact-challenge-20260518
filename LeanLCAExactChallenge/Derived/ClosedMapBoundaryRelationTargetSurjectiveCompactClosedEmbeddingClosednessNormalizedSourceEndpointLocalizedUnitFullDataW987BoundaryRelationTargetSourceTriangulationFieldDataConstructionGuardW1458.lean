import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionGuardW1457

/-!
W1458 refines W1457 by constructing its W722 source-triangulation input
from the source pretriangulated structure, the source triangulated structure,
and the source triangle-completion input, then runs the resulting data through
the W1457/W1456/W1455/W1454/W1453/W1452/W1451/W1450 W987 construction.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/--
W1458 replaces the W1457 W722 source-triangulation input by separate source
triangulation and triangle-completion fields.
-/
structure W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458 :
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
  localizedUnitData :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945

/-- W1458 builds W722 source-triangulation data from three fields. -/
def sourceTriangulationDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    MetrizableWppSourceTriangulationDataProviderW722 where
  sourcePretriangulated := input.sourcePretriangulated
  sourceTriangulated := input.sourceTriangulated
  triangleCompletion := input.triangleCompletion

/-- W1458 builds the W1457 input after constructing W722 data. -/
def w1457InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457 where
  rightOpenBoundary := input.rightOpenBoundary
  sourcePiZeroBoundary := input.sourcePiZeroBoundary
  relationPullbackProvider := input.relationPullbackProvider
  targetRelationLiftsProvider := input.targetRelationLiftsProvider
  targetNoUnivData := input.targetNoUnivData
  closedEmbeddingClosednessData := input.closedEmbeddingClosednessData
  normalizedLiftBlueprint := input.normalizedLiftBlueprint
  targetFixedTargetUniq := input.targetFixedTargetUniq
  localizationModelFixedTargetUniq := input.localizationModelFixedTargetUniq
  sourceTriangulationData :=
    sourceTriangulationDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
      input
  endpointStrictExact := input.endpointStrictExact
  localizedUnitData := input.localizedUnitData

/-- W1458 builds W719 normalized fixed-target data through W1457. -/
def normalizedFixedTargetDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    MetrizableWppNormalizedFixedTargetDataProviderW719 :=
  normalizedFixedTargetDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
    (w1457InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
      input)

/-- W1458 builds the W1456 input through W1457. -/
def w1456InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456 :=
  w1456InputOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
    (w1457InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
      input)

/-- W1458 builds W948 normalized-source data through W1457. -/
def normalizedSourceTriangulationDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    NormalizedFixedTargetSourceTriangulationDataProviderW948 :=
  normalizedSourceTriangulationDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
    (w1457InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
      input)

/-- W1458 builds the W1455 input through W1457. -/
def w1455InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputW1455 :=
  w1455InputOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
    (w1457InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
      input)

/-- W1458 builds W949 endpoint-localized-unit data through W1457. -/
def endpointLocalizedUnitDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    EndpointStrictExactLocalizedUnitDataProviderW949 :=
  endpointLocalizedUnitDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
    (w1457InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
      input)

/-- W1458 builds W950 normalized-source/endpoint data through W1457. -/
def normalizedSourceEndpointLocalizedUnitDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950 :=
  normalizedSourceEndpointLocalizedUnitDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
    (w1457InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
      input)

/-- W1458 builds W984 target/closedness data through W1457. -/
def targetClosedEmbeddingClosednessDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    TargetNoUnivClosedEmbeddingClosednessDataProviderW984 :=
  targetClosedEmbeddingClosednessDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
    (w1457InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
      input)

/-- W1458 builds W717 relation data through W1457. -/
def relationDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    ClosedNatTransOrdinaryRelationDataProviderW717 :=
  relationDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
    (w1457InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
      input)

/-- W1458 builds W716 boundary data through W1457. -/
def boundaryDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    MetrizableWppLimitBoundaryDataW716 :=
  boundaryDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
    (w1457InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
      input)

/-- W1458 builds W730 boundary/relation data through W1457. -/
def boundaryRelationDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
    (w1457InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
      input)

/-- W1458 builds W986 target/endpoint data through W1457. -/
def targetNormalizedEndpointDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetNormalizedEndpointDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
    (w1457InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
      input)

/-- W1458 builds the remaining W987 full-data provider through W1457. -/
noncomputable def fullDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
    (w1457InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
      input)

/-- W1458's constructed W722 data keeps the source pretriangulated structure. -/
theorem w1458SourceTriangulationDataKeepsSourcePretriangulated
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    sourcePretriangulated_of_sourceTriangulationDataW722
        (sourceTriangulationDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
          input) =
      input.sourcePretriangulated :=
  rfl

/-- W1458's constructed W722 data keeps the source triangulated structure. -/
theorem w1458SourceTriangulationDataKeepsSourceTriangulated
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    sourceTriangulated_of_sourceTriangulationDataW722
        (sourceTriangulationDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
          input) =
      input.sourceTriangulated :=
  rfl

/-- W1458's constructed W722 data keeps source triangle completion. -/
theorem w1458SourceTriangulationDataKeepsTriangleCompletion
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    triangleCompletion_of_sourceTriangulationDataW722
        (sourceTriangulationDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
          input) =
      input.triangleCompletion :=
  rfl

/-- W1458's W1457 input keeps the raw right-open boundary field. -/
theorem w1458InputKeepsRightOpenBoundary
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    (w1457InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
        input).rightOpenBoundary =
      input.rightOpenBoundary :=
  rfl

/-- W1458's W1457 input keeps the raw source-pi-zero boundary field. -/
theorem w1458InputKeepsSourcePiZeroBoundary
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    (w1457InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
        input).sourcePiZeroBoundary =
      input.sourcePiZeroBoundary :=
  rfl

/-- W1458's W1457 input keeps the raw relation-pullback field. -/
theorem w1458InputKeepsRelationPullbackProvider
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    (w1457InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
        input).relationPullbackProvider =
      input.relationPullbackProvider :=
  rfl

/-- W1458's W1457 input keeps the raw target-relation-lifts field. -/
theorem w1458InputKeepsTargetRelationLiftsProvider
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    (w1457InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
        input).targetRelationLiftsProvider =
      input.targetRelationLiftsProvider :=
  rfl

/-- W1458's W1457 input keeps the W944 target no-univ provider. -/
theorem w1458InputKeepsTargetNoUnivData
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    (w1457InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
        input).targetNoUnivData =
      input.targetNoUnivData :=
  rfl

/-- W1458's W1457 input keeps the W973 closedness provider. -/
theorem w1458InputKeepsClosedEmbeddingClosednessData
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    (w1457InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
        input).closedEmbeddingClosednessData =
      input.closedEmbeddingClosednessData :=
  rfl

/-- W1458's W1457 input keeps the normalized lift blueprint. -/
theorem w1458InputKeepsNormalizedLiftBlueprint
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    (w1457InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
        input).normalizedLiftBlueprint =
      input.normalizedLiftBlueprint :=
  rfl

/-- W1458's W1457 input keeps target fixed-target uniqueness. -/
theorem w1458InputKeepsTargetFixedTargetUniq
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    (w1457InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
        input).targetFixedTargetUniq =
      input.targetFixedTargetUniq :=
  rfl

/-- W1458's W1457 input keeps localization-model fixed-target uniqueness. -/
theorem w1458InputKeepsLocalizationModelFixedTargetUniq
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    (w1457InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
        input).localizationModelFixedTargetUniq =
      input.localizationModelFixedTargetUniq :=
  rfl

/-- W1458's W1457 input keeps the constructed W722 source-triangulation data. -/
theorem w1458InputKeepsConstructedSourceTriangulationData
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    (w1457InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
        input).sourceTriangulationData =
      sourceTriangulationDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
        input :=
  rfl

/-- W1458's W1457 input keeps the endpoint strict-exact witnesses. -/
theorem w1458InputKeepsEndpointStrictExact
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    (w1457InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
        input).endpointStrictExact =
      input.endpointStrictExact :=
  rfl

/-- W1458's W1457 input keeps the W945 localized-unit data. -/
theorem w1458InputKeepsLocalizedUnitData
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    (w1457InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
        input).localizedUnitData =
      input.localizedUnitData :=
  rfl

/-- W1458's constructed W719 data keeps the normalized lift blueprint. -/
theorem w1458NormalizedFixedTargetDataKeepsNormalizedLiftBlueprint
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    normalizedLiftBlueprint_of_normalizedFixedTargetDataW719
        (normalizedFixedTargetDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
          input) =
      input.normalizedLiftBlueprint :=
  rfl

/-- W1458's constructed W719 data keeps target fixed-target uniqueness. -/
theorem w1458NormalizedFixedTargetDataKeepsTargetFixedTargetUniq
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    targetFixedTargetUniq_of_normalizedFixedTargetDataW719
        (normalizedFixedTargetDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
          input) =
      input.targetFixedTargetUniq :=
  rfl

/-- W1458's constructed W719 data keeps localization-model fixed-target uniqueness. -/
theorem w1458NormalizedFixedTargetDataKeepsLocalizationModelFixedTargetUniq
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    localizationModelFixedTargetUniq_of_normalizedFixedTargetDataW719
        (normalizedFixedTargetDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
          input) =
      input.localizationModelFixedTargetUniq :=
  rfl

/-- W1458's constructed W948 data keeps the constructed W719 data. -/
theorem w1458NormalizedSourceDataKeepsConstructedNormalizedFixedTargetData
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    normalizedFixedTargetDataOfNormalizedSourceTriangulationDataW948
        (normalizedSourceTriangulationDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
          input) =
      normalizedFixedTargetDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
        input :=
  rfl

/-- W1458's constructed W948 data keeps the constructed W722 data. -/
theorem w1458NormalizedSourceDataKeepsConstructedSourceTriangulationData
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    sourceTriangulationDataOfNormalizedSourceTriangulationDataW948
        (normalizedSourceTriangulationDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
          input) =
      sourceTriangulationDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
        input :=
  rfl

/-- W1458's W1456 input keeps the constructed W719 data. -/
theorem w1458W1456InputKeepsConstructedNormalizedFixedTargetData
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    (w1456InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
        input).normalizedFixedTargetData =
      normalizedFixedTargetDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
        input :=
  rfl

/-- W1458's W1456 input keeps the constructed W722 data. -/
theorem w1458W1456InputKeepsConstructedSourceTriangulationData
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    (w1456InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
        input).sourceTriangulationData =
      sourceTriangulationDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
        input :=
  rfl

/-- W1458's W730 construction keeps the constructed W716 boundary data. -/
theorem w1458BoundaryRelationKeepsConstructedBoundaryData
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    boundaryData_of_boundaryRelationDataW730
        (boundaryRelationDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
          input) =
      boundaryDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
        input :=
  rfl

/-- W1458's W730 construction keeps the constructed W717 relation data. -/
theorem w1458BoundaryRelationKeepsConstructedRelationData
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    relationData_of_boundaryRelationDataW730
        (boundaryRelationDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
          input) =
      relationDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
        input :=
  rfl

/-- W1458's W986 construction keeps the constructed W984 target/closedness data. -/
theorem w1458TargetNormalizedEndpointKeepsConstructedTargetClosedness
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
        (targetNormalizedEndpointDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
          input) =
      targetClosedEmbeddingClosednessDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
        input :=
  rfl

/-- W1458's W986 construction keeps the constructed W950 normalized-endpoint data. -/
theorem w1458TargetNormalizedEndpointKeepsConstructedNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    normalizedSourceEndpointLocalizedUnitDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
        (targetNormalizedEndpointDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
          input) =
      normalizedSourceEndpointLocalizedUnitDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
        input :=
  rfl

/-- W1458's W987 provider projects to the constructed W730 data. -/
theorem w1458FullDataKeepsConstructedBoundaryRelation
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    boundaryRelationDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
          input) =
      boundaryRelationDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
        input :=
  rfl

/-- W1458's W987 provider projects to the constructed W986 target/endpoint data. -/
theorem w1458FullDataKeepsConstructedTargetNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
          input) =
      targetNormalizedEndpointDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458
        input :=
  rfl

def w987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputNamesW1458 :
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
    "W945 localized-unit data"]

theorem w987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputNamesW1458_count :
    w987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputNamesW1458.length =
      14 :=
  rfl

def w987BoundaryRelationTargetSourceTriangulationFieldDataConstructionBundledSourceTriangulationInputNamesW1458 :
    List String :=
  ["W722 source-triangulation data"]

theorem w987BoundaryRelationTargetSourceTriangulationFieldDataConstructionBundledSourceTriangulationInputNamesW1458_count :
    w987BoundaryRelationTargetSourceTriangulationFieldDataConstructionBundledSourceTriangulationInputNamesW1458.length =
      1 :=
  rfl

def w987BoundaryRelationTargetSourceTriangulationFieldDataConstructionSourceTriangulationInputNamesW1458 :
    List String :=
  ["source pretriangulated structure",
    "source triangulated structure",
    "source triangle-completion input"]

theorem w987BoundaryRelationTargetSourceTriangulationFieldDataConstructionSourceTriangulationInputNamesW1458_count :
    w987BoundaryRelationTargetSourceTriangulationFieldDataConstructionSourceTriangulationInputNamesW1458.length =
      3 :=
  rfl

/-- W1458 splits W1457's one W722 source-triangulation input into three fields. -/
theorem w1458BoundaryRelationTargetSourceTriangulationFieldDataConstructionSplitsW722Input :
    w987BoundaryRelationTargetSourceTriangulationFieldDataConstructionBundledSourceTriangulationInputNamesW1458.length <
      w987BoundaryRelationTargetSourceTriangulationFieldDataConstructionSourceTriangulationInputNamesW1458.length := by
  rw [
    w987BoundaryRelationTargetSourceTriangulationFieldDataConstructionBundledSourceTriangulationInputNamesW1458_count,
    w987BoundaryRelationTargetSourceTriangulationFieldDataConstructionSourceTriangulationInputNamesW1458_count]
  norm_num

/-- W1458 replaces the twelve W1457 inputs by fourteen named construction inputs. -/
theorem w1458BoundaryRelationTargetSourceTriangulationFieldDataConstructionExpandsW1457InputCount :
    w987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputNamesW1457.length <
      w987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputNamesW1458.length := by
  rw [w987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputNamesW1457_count,
    w987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputNamesW1458_count]
  norm_num

/-- Current W1458 nonterminal source-triangulation construction state. -/
structure W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionStateW1458 :
    Type where
  seed : String
  declarations : List String
  constructionResult : String
  projectionResult : String
  sourceTriangulationInputNames : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1458 records the W722 construction path into W1457. -/
def currentW987BoundaryRelationTargetSourceTriangulationFieldDataConstructionStateW1458 :
    W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionStateW1458 where
  seed :=
    "w1458-w987-boundary-relation-target-source-triangulation-field-data-construction"
  declarations :=
    ["W987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputW1458",
      "sourceTriangulationDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458",
      "w1457InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458",
      "normalizedFixedTargetDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458",
      "w1456InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458",
      "normalizedSourceTriangulationDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458",
      "w1455InputOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458",
      "endpointLocalizedUnitDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458",
      "normalizedSourceEndpointLocalizedUnitDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458",
      "targetClosedEmbeddingClosednessDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458",
      "relationDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458",
      "boundaryDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458",
      "boundaryRelationDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458",
      "targetNormalizedEndpointDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458",
      "fullDataOfW987BoundaryRelationTargetSourceTriangulationFieldDataW1458",
      "w1458SourceTriangulationDataKeepsSourcePretriangulated",
      "w1458SourceTriangulationDataKeepsSourceTriangulated",
      "w1458SourceTriangulationDataKeepsTriangleCompletion",
      "w1458InputKeepsRightOpenBoundary",
      "w1458InputKeepsSourcePiZeroBoundary",
      "w1458InputKeepsRelationPullbackProvider",
      "w1458InputKeepsTargetRelationLiftsProvider",
      "w1458InputKeepsTargetNoUnivData",
      "w1458InputKeepsClosedEmbeddingClosednessData",
      "w1458InputKeepsNormalizedLiftBlueprint",
      "w1458InputKeepsTargetFixedTargetUniq",
      "w1458InputKeepsLocalizationModelFixedTargetUniq",
      "w1458InputKeepsConstructedSourceTriangulationData",
      "w1458InputKeepsEndpointStrictExact",
      "w1458InputKeepsLocalizedUnitData",
      "w1458NormalizedFixedTargetDataKeepsNormalizedLiftBlueprint",
      "w1458NormalizedFixedTargetDataKeepsTargetFixedTargetUniq",
      "w1458NormalizedFixedTargetDataKeepsLocalizationModelFixedTargetUniq",
      "w1458NormalizedSourceDataKeepsConstructedNormalizedFixedTargetData",
      "w1458NormalizedSourceDataKeepsConstructedSourceTriangulationData",
      "w1458W1456InputKeepsConstructedNormalizedFixedTargetData",
      "w1458W1456InputKeepsConstructedSourceTriangulationData",
      "w1458BoundaryRelationKeepsConstructedBoundaryData",
      "w1458BoundaryRelationKeepsConstructedRelationData",
      "w1458TargetNormalizedEndpointKeepsConstructedTargetClosedness",
      "w1458TargetNormalizedEndpointKeepsConstructedNormalizedEndpoint",
      "w1458FullDataKeepsConstructedBoundaryRelation",
      "w1458FullDataKeepsConstructedTargetNormalizedEndpoint",
      "w987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputNamesW1458_count",
      "w1458BoundaryRelationTargetSourceTriangulationFieldDataConstructionSplitsW722Input",
      "w1458BoundaryRelationTargetSourceTriangulationFieldDataConstructionExpandsW1457InputCount"]
  constructionResult :=
    "proved: W722 source-triangulation data can be assembled from the source\
      pretriangulated structure, source triangulated structure, and source\
      triangle-completion input before running W1457's W987 construction"
  projectionResult :=
    "proved: the constructed W722, W948, W950, W730, W986, and W987 providers\
      project back to the W1458 source-triangulation fields, fixed-target\
      fields, endpoint fields, target fields, relation fields, and boundary\
      fields"
  sourceTriangulationInputNames :=
    w987BoundaryRelationTargetSourceTriangulationFieldDataConstructionSourceTriangulationInputNamesW1458
  remainingInputs :=
    w987BoundaryRelationTargetSourceTriangulationFieldDataConstructionInputNamesW1458
  productSuccessClaimed := false

theorem currentW1458W987BoundaryRelationTargetSourceTriangulationFieldDataConstruction_productSuccess :
    currentW987BoundaryRelationTargetSourceTriangulationFieldDataConstructionStateW1458.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
