import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987BoundaryRelationTargetNormalizedSourceFieldDataConstructionGuardW1456

/-!
W1457 refines W1456 by constructing its W719 normalized fixed-target input
from the normalized lift blueprint and the two fixed-target uniqueness fields,
then runs the resulting data through the W1456/W1455/W1454/W1453/W1452/W1451/
W1450 W987 construction.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/--
W1457 replaces the W1456 W719 normalized fixed-target input by separate
normalized lift blueprint and fixed-target uniqueness fields.
-/
structure W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457 :
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
  sourceTriangulationData :
    MetrizableWppSourceTriangulationDataProviderW722
  endpointStrictExact :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i)
  localizedUnitData :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945

/-- W1457 builds W719 normalized fixed-target data from three fields. -/
def normalizedFixedTargetDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
    (input :
      W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457) :
    MetrizableWppNormalizedFixedTargetDataProviderW719 where
  normalizedLiftBlueprint := input.normalizedLiftBlueprint
  targetFixedTargetUniq := input.targetFixedTargetUniq
  localizationModelFixedTargetUniq := input.localizationModelFixedTargetUniq

/-- W1457 builds the W1456 input after constructing W719 data. -/
def w1456InputOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
    (input :
      W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457) :
    W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456 where
  rightOpenBoundary := input.rightOpenBoundary
  sourcePiZeroBoundary := input.sourcePiZeroBoundary
  relationPullbackProvider := input.relationPullbackProvider
  targetRelationLiftsProvider := input.targetRelationLiftsProvider
  targetNoUnivData := input.targetNoUnivData
  closedEmbeddingClosednessData := input.closedEmbeddingClosednessData
  normalizedFixedTargetData :=
    normalizedFixedTargetDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
      input
  sourceTriangulationData := input.sourceTriangulationData
  endpointStrictExact := input.endpointStrictExact
  localizedUnitData := input.localizedUnitData

/-- W1457 builds W948 normalized-source data through W1456. -/
def normalizedSourceTriangulationDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
    (input :
      W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457) :
    NormalizedFixedTargetSourceTriangulationDataProviderW948 :=
  normalizedSourceTriangulationDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
    (w1456InputOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
      input)

/-- W1457 builds the W1455 input through W1456. -/
def w1455InputOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
    (input :
      W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457) :
    W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputW1455 :=
  w1455InputOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
    (w1456InputOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
      input)

/-- W1457 builds W949 endpoint-localized-unit data through W1456. -/
def endpointLocalizedUnitDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
    (input :
      W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457) :
    EndpointStrictExactLocalizedUnitDataProviderW949 :=
  endpointLocalizedUnitDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
    (w1456InputOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
      input)

/-- W1457 builds W950 normalized-source/endpoint data through W1456. -/
def normalizedSourceEndpointLocalizedUnitDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
    (input :
      W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457) :
    NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950 :=
  normalizedSourceEndpointLocalizedUnitDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
    (w1456InputOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
      input)

/-- W1457 builds W984 target/closedness data through W1456. -/
def targetClosedEmbeddingClosednessDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
    (input :
      W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457) :
    TargetNoUnivClosedEmbeddingClosednessDataProviderW984 :=
  targetClosedEmbeddingClosednessDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
    (w1456InputOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
      input)

/-- W1457 builds W717 relation data through W1456. -/
def relationDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
    (input :
      W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457) :
    ClosedNatTransOrdinaryRelationDataProviderW717 :=
  relationDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
    (w1456InputOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
      input)

/-- W1457 builds W716 boundary data through W1456. -/
def boundaryDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
    (input :
      W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457) :
    MetrizableWppLimitBoundaryDataW716 :=
  boundaryDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
    (w1456InputOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
      input)

/-- W1457 builds W730 boundary/relation data through W1456. -/
def boundaryRelationDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
    (input :
      W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
    (w1456InputOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
      input)

/-- W1457 builds W986 target/endpoint data through W1456. -/
def targetNormalizedEndpointDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
    (input :
      W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetNormalizedEndpointDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
    (w1456InputOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
      input)

/-- W1457 builds the remaining W987 full-data provider through W1456. -/
noncomputable def fullDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
    (input :
      W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
    (w1456InputOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
      input)

/-- W1457's constructed W719 data keeps the normalized lift blueprint. -/
theorem w1457NormalizedFixedTargetDataKeepsNormalizedLiftBlueprint
    (input :
      W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457) :
    normalizedLiftBlueprint_of_normalizedFixedTargetDataW719
        (normalizedFixedTargetDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
          input) =
      input.normalizedLiftBlueprint :=
  rfl

/-- W1457's constructed W719 data keeps target fixed-target uniqueness. -/
theorem w1457NormalizedFixedTargetDataKeepsTargetFixedTargetUniq
    (input :
      W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457) :
    targetFixedTargetUniq_of_normalizedFixedTargetDataW719
        (normalizedFixedTargetDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
          input) =
      input.targetFixedTargetUniq :=
  rfl

/-- W1457's constructed W719 data keeps localization-model fixed-target uniqueness. -/
theorem w1457NormalizedFixedTargetDataKeepsLocalizationModelFixedTargetUniq
    (input :
      W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457) :
    localizationModelFixedTargetUniq_of_normalizedFixedTargetDataW719
        (normalizedFixedTargetDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
          input) =
      input.localizationModelFixedTargetUniq :=
  rfl

/-- W1457's constructed W948 data keeps the constructed W719 data. -/
theorem w1457NormalizedSourceDataKeepsConstructedNormalizedFixedTargetData
    (input :
      W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457) :
    normalizedFixedTargetDataOfNormalizedSourceTriangulationDataW948
        (normalizedSourceTriangulationDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
          input) =
      normalizedFixedTargetDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
        input :=
  rfl

/-- W1457's constructed W948 data keeps the W722 source-triangulation data. -/
theorem w1457NormalizedSourceDataKeepsSourceTriangulationData
    (input :
      W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457) :
    sourceTriangulationDataOfNormalizedSourceTriangulationDataW948
        (normalizedSourceTriangulationDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
          input) =
      input.sourceTriangulationData :=
  rfl

/-- W1457's W1456 input keeps the raw right-open boundary field. -/
theorem w1457InputKeepsRightOpenBoundary
    (input :
      W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457) :
    (w1456InputOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
        input).rightOpenBoundary =
      input.rightOpenBoundary :=
  rfl

/-- W1457's W1456 input keeps the raw source-pi-zero boundary field. -/
theorem w1457InputKeepsSourcePiZeroBoundary
    (input :
      W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457) :
    (w1456InputOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
        input).sourcePiZeroBoundary =
      input.sourcePiZeroBoundary :=
  rfl

/-- W1457's W1456 input keeps the raw relation-pullback field. -/
theorem w1457InputKeepsRelationPullbackProvider
    (input :
      W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457) :
    (w1456InputOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
        input).relationPullbackProvider =
      input.relationPullbackProvider :=
  rfl

/-- W1457's W1456 input keeps the raw target-relation-lifts field. -/
theorem w1457InputKeepsTargetRelationLiftsProvider
    (input :
      W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457) :
    (w1456InputOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
        input).targetRelationLiftsProvider =
      input.targetRelationLiftsProvider :=
  rfl

/-- W1457's W1456 input keeps the W944 target no-univ provider. -/
theorem w1457InputKeepsTargetNoUnivData
    (input :
      W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457) :
    (w1456InputOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
        input).targetNoUnivData =
      input.targetNoUnivData :=
  rfl

/-- W1457's W1456 input keeps the W973 closedness provider. -/
theorem w1457InputKeepsClosedEmbeddingClosednessData
    (input :
      W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457) :
    (w1456InputOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
        input).closedEmbeddingClosednessData =
      input.closedEmbeddingClosednessData :=
  rfl

/-- W1457's W1456 input keeps the constructed W719 normalized fixed-target data. -/
theorem w1457InputKeepsConstructedNormalizedFixedTargetData
    (input :
      W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457) :
    (w1456InputOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
        input).normalizedFixedTargetData =
      normalizedFixedTargetDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
        input :=
  rfl

/-- W1457's W1456 input keeps the W722 source-triangulation data. -/
theorem w1457InputKeepsSourceTriangulationData
    (input :
      W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457) :
    (w1456InputOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
        input).sourceTriangulationData =
      input.sourceTriangulationData :=
  rfl

/-- W1457's W1456 input keeps the endpoint strict-exact witnesses. -/
theorem w1457InputKeepsEndpointStrictExact
    (input :
      W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457) :
    (w1456InputOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
        input).endpointStrictExact =
      input.endpointStrictExact :=
  rfl

/-- W1457's W1456 input keeps the W945 localized-unit data. -/
theorem w1457InputKeepsLocalizedUnitData
    (input :
      W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457) :
    (w1456InputOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
        input).localizedUnitData =
      input.localizedUnitData :=
  rfl

/-- W1457's W730 construction keeps the constructed W716 boundary data. -/
theorem w1457BoundaryRelationKeepsConstructedBoundaryData
    (input :
      W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457) :
    boundaryData_of_boundaryRelationDataW730
        (boundaryRelationDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
          input) =
      boundaryDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
        input :=
  rfl

/-- W1457's W730 construction keeps the constructed W717 relation data. -/
theorem w1457BoundaryRelationKeepsConstructedRelationData
    (input :
      W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457) :
    relationData_of_boundaryRelationDataW730
        (boundaryRelationDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
          input) =
      relationDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
        input :=
  rfl

/-- W1457's W986 construction keeps the constructed W984 target/closedness data. -/
theorem w1457TargetNormalizedEndpointKeepsConstructedTargetClosedness
    (input :
      W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457) :
    targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
        (targetNormalizedEndpointDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
          input) =
      targetClosedEmbeddingClosednessDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
        input :=
  rfl

/-- W1457's W986 construction keeps the constructed W950 normalized-endpoint data. -/
theorem w1457TargetNormalizedEndpointKeepsConstructedNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457) :
    normalizedSourceEndpointLocalizedUnitDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
        (targetNormalizedEndpointDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
          input) =
      normalizedSourceEndpointLocalizedUnitDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
        input :=
  rfl

/-- W1457's W987 provider projects to the constructed W730 data. -/
theorem w1457FullDataKeepsConstructedBoundaryRelation
    (input :
      W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457) :
    boundaryRelationDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
          input) =
      boundaryRelationDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
        input :=
  rfl

/-- W1457's W987 provider projects to the constructed W986 target/endpoint data. -/
theorem w1457FullDataKeepsConstructedTargetNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
          input) =
      targetNormalizedEndpointDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457
        input :=
  rfl

def w987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputNamesW1457 :
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
    "W722 source-triangulation data",
    "endpoint strict short-exact witnesses",
    "W945 localized-unit data"]

theorem w987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputNamesW1457_count :
    w987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputNamesW1457.length =
      12 :=
  rfl

def w987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionBundledFixedTargetInputNamesW1457 :
    List String :=
  ["W719 normalized fixed-target data"]

theorem w987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionBundledFixedTargetInputNamesW1457_count :
    w987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionBundledFixedTargetInputNamesW1457.length =
      1 :=
  rfl

def w987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionFixedTargetInputNamesW1457 :
    List String :=
  ["normalized lift blueprint",
    "target fixed-target uniqueness",
    "localization-model fixed-target uniqueness"]

theorem w987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionFixedTargetInputNamesW1457_count :
    w987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionFixedTargetInputNamesW1457.length =
      3 :=
  rfl

/-- W1457 splits W1456's one W719 normalized fixed-target input into three fields. -/
theorem w1457BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionSplitsW719Input :
    w987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionBundledFixedTargetInputNamesW1457.length <
      w987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionFixedTargetInputNamesW1457.length := by
  rw [
    w987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionBundledFixedTargetInputNamesW1457_count,
    w987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionFixedTargetInputNamesW1457_count]
  norm_num

/-- W1457 replaces the ten W1456 inputs by twelve named construction inputs. -/
theorem w1457BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionExpandsW1456InputCount :
    w987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputNamesW1456.length <
      w987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputNamesW1457.length := by
  rw [w987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputNamesW1456_count,
    w987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputNamesW1457_count]
  norm_num

/-- Current W1457 nonterminal normalized fixed-target construction state. -/
structure W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionStateW1457 :
    Type where
  seed : String
  declarations : List String
  constructionResult : String
  projectionResult : String
  fixedTargetInputNames : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1457 records the W719 construction path into W1456. -/
def currentW987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionStateW1457 :
    W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionStateW1457 where
  seed :=
    "w1457-w987-boundary-relation-target-normalized-fixed-target-field-data-construction"
  declarations :=
    ["W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputW1457",
      "normalizedFixedTargetDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457",
      "w1456InputOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457",
      "normalizedSourceTriangulationDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457",
      "w1455InputOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457",
      "endpointLocalizedUnitDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457",
      "normalizedSourceEndpointLocalizedUnitDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457",
      "targetClosedEmbeddingClosednessDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457",
      "relationDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457",
      "boundaryDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457",
      "boundaryRelationDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457",
      "targetNormalizedEndpointDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457",
      "fullDataOfW987BoundaryRelationTargetNormalizedFixedTargetFieldDataW1457",
      "w1457NormalizedFixedTargetDataKeepsNormalizedLiftBlueprint",
      "w1457NormalizedFixedTargetDataKeepsTargetFixedTargetUniq",
      "w1457NormalizedFixedTargetDataKeepsLocalizationModelFixedTargetUniq",
      "w1457NormalizedSourceDataKeepsConstructedNormalizedFixedTargetData",
      "w1457NormalizedSourceDataKeepsSourceTriangulationData",
      "w1457InputKeepsRightOpenBoundary",
      "w1457InputKeepsSourcePiZeroBoundary",
      "w1457InputKeepsRelationPullbackProvider",
      "w1457InputKeepsTargetRelationLiftsProvider",
      "w1457InputKeepsTargetNoUnivData",
      "w1457InputKeepsClosedEmbeddingClosednessData",
      "w1457InputKeepsConstructedNormalizedFixedTargetData",
      "w1457InputKeepsSourceTriangulationData",
      "w1457InputKeepsEndpointStrictExact",
      "w1457InputKeepsLocalizedUnitData",
      "w1457BoundaryRelationKeepsConstructedBoundaryData",
      "w1457BoundaryRelationKeepsConstructedRelationData",
      "w1457TargetNormalizedEndpointKeepsConstructedTargetClosedness",
      "w1457TargetNormalizedEndpointKeepsConstructedNormalizedEndpoint",
      "w1457FullDataKeepsConstructedBoundaryRelation",
      "w1457FullDataKeepsConstructedTargetNormalizedEndpoint",
      "w987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputNamesW1457_count",
      "w1457BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionSplitsW719Input",
      "w1457BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionExpandsW1456InputCount"]
  constructionResult :=
    "proved: W719 normalized fixed-target data can be assembled from the\
      normalized lift blueprint, target fixed-target uniqueness, and\
      localization-model fixed-target uniqueness before running W1456's W987\
      construction"
  projectionResult :=
    "proved: the constructed W719, W948, W950, W730, W986, and W987 providers\
      project back to the W1457 fixed-target fields, source field, endpoint\
      fields, target fields, relation fields, and boundary fields"
  fixedTargetInputNames :=
    w987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionFixedTargetInputNamesW1457
  remainingInputs :=
    w987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionInputNamesW1457
  productSuccessClaimed := false

theorem currentW1457W987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstruction_productSuccess :
    currentW987BoundaryRelationTargetNormalizedFixedTargetFieldDataConstructionStateW1457.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
