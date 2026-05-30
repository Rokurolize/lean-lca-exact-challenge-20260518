import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987BoundaryFieldDataConstructionGuardW1451
import LeanLCAExactChallenge.Derived.ClosedMapRelationFieldsBoundaryFieldsComponentFieldsRoute

/-!
W1452 refines W1451 by constructing its W717 relation-data input from the two
raw relation fields already used by W908, then runs the resulting data through
the W1451/W1450 W987 construction.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

/--
W1452 replaces the W1451 W717 relation-data input by relation-pullback and
target-relation-lifts providers.
-/
structure W987BoundaryRelationFieldDataConstructionInputW1452 : Type 2 where
  rightOpenBoundary :
    Dbounded.MetrizableWppLimitRightOpenClosedQuotientCoverBoundary
  sourcePiZeroBoundary :
    Dbounded.MetrizableWppLimitSourceDifferenceCokernelPiZeroBoundary
  relationPullbackProvider :
    ClosedNatTransOrdinaryRelationPullbackProviderW712
  targetRelationLiftsProvider :
    ClosedNatTransOrdinaryTargetRelationLiftsProviderW712
  targetClosedEmbeddingClosednessData :
    TargetNoUnivClosedEmbeddingClosednessDataProviderW984
  normalizedSourceEndpointLocalizedUnitData :
    NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950

/-- W1452 builds W717 relation data from the two raw relation fields. -/
def relationDataOfW987BoundaryRelationFieldDataW1452
    (input : W987BoundaryRelationFieldDataConstructionInputW1452) :
    ClosedNatTransOrdinaryRelationDataProviderW717 :=
  relationDataOfFieldsW908 input.relationPullbackProvider
    input.targetRelationLiftsProvider

/-- W1452 builds the W1451 input after constructing W717 relation data. -/
def w1451InputOfW987BoundaryRelationFieldDataW1452
    (input : W987BoundaryRelationFieldDataConstructionInputW1452) :
    W987BoundaryFieldDataConstructionInputW1451 where
  rightOpenBoundary := input.rightOpenBoundary
  sourcePiZeroBoundary := input.sourcePiZeroBoundary
  relationData := relationDataOfW987BoundaryRelationFieldDataW1452 input
  targetClosedEmbeddingClosednessData :=
    input.targetClosedEmbeddingClosednessData
  normalizedSourceEndpointLocalizedUnitData :=
    input.normalizedSourceEndpointLocalizedUnitData

/-- W1452 builds W716 boundary data through W1451. -/
def boundaryDataOfW987BoundaryRelationFieldDataW1452
    (input : W987BoundaryRelationFieldDataConstructionInputW1452) :
    MetrizableWppLimitBoundaryDataW716 :=
  boundaryDataOfW987BoundaryFieldDataW1451
    (w1451InputOfW987BoundaryRelationFieldDataW1452 input)

/-- W1452 builds W730 boundary/relation data through W1451. -/
def boundaryRelationDataOfW987BoundaryRelationFieldDataW1452
    (input : W987BoundaryRelationFieldDataConstructionInputW1452) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfW987BoundaryFieldDataW1451
    (w1451InputOfW987BoundaryRelationFieldDataW1452 input)

/-- W1452 builds W986 target/endpoint data through W1451. -/
def targetNormalizedEndpointDataOfW987BoundaryRelationFieldDataW1452
    (input : W987BoundaryRelationFieldDataConstructionInputW1452) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetNormalizedEndpointDataOfW987BoundaryFieldDataW1451
    (w1451InputOfW987BoundaryRelationFieldDataW1452 input)

/-- W1452 builds the remaining W987 full-data provider through W1451. -/
noncomputable def fullDataOfW987BoundaryRelationFieldDataW1452
    (input : W987BoundaryRelationFieldDataConstructionInputW1452) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfW987BoundaryFieldDataW1451
    (w1451InputOfW987BoundaryRelationFieldDataW1452 input)

/-- W1452's constructed W717 data keeps the relation-pullback provider. -/
theorem w1452RelationDataKeepsRelationPullbackProvider
    (input : W987BoundaryRelationFieldDataConstructionInputW1452) :
    (relationDataOfW987BoundaryRelationFieldDataW1452
        input).relationPullbackProvider =
      input.relationPullbackProvider :=
  rfl

/-- W1452's constructed W717 data keeps the target-relation-lifts provider. -/
theorem w1452RelationDataKeepsTargetRelationLiftsProvider
    (input : W987BoundaryRelationFieldDataConstructionInputW1452) :
    (relationDataOfW987BoundaryRelationFieldDataW1452
        input).targetRelationLiftsProvider =
      input.targetRelationLiftsProvider :=
  rfl

/-- W1452's W1451 input keeps the raw right-open boundary field. -/
theorem w1452InputKeepsRightOpenBoundary
    (input : W987BoundaryRelationFieldDataConstructionInputW1452) :
    (w1451InputOfW987BoundaryRelationFieldDataW1452
        input).rightOpenBoundary =
      input.rightOpenBoundary :=
  rfl

/-- W1452's W1451 input keeps the raw source-pi-zero boundary field. -/
theorem w1452InputKeepsSourcePiZeroBoundary
    (input : W987BoundaryRelationFieldDataConstructionInputW1452) :
    (w1451InputOfW987BoundaryRelationFieldDataW1452
        input).sourcePiZeroBoundary =
      input.sourcePiZeroBoundary :=
  rfl

/-- W1452's W1451 input keeps the constructed W717 relation data. -/
theorem w1452InputKeepsConstructedRelationData
    (input : W987BoundaryRelationFieldDataConstructionInputW1452) :
    (w1451InputOfW987BoundaryRelationFieldDataW1452 input).relationData =
      relationDataOfW987BoundaryRelationFieldDataW1452 input :=
  rfl

/-- W1452's W1451 input keeps the original W984 target/closedness data. -/
theorem w1452InputKeepsTargetClosednessData
    (input : W987BoundaryRelationFieldDataConstructionInputW1452) :
    (w1451InputOfW987BoundaryRelationFieldDataW1452
        input).targetClosedEmbeddingClosednessData =
      input.targetClosedEmbeddingClosednessData :=
  rfl

/-- W1452's W1451 input keeps the original W950 normalized-endpoint data. -/
theorem w1452InputKeepsNormalizedEndpointData
    (input : W987BoundaryRelationFieldDataConstructionInputW1452) :
    (w1451InputOfW987BoundaryRelationFieldDataW1452
        input).normalizedSourceEndpointLocalizedUnitData =
      input.normalizedSourceEndpointLocalizedUnitData :=
  rfl

/-- W1452's W730 construction keeps the constructed W716 boundary data. -/
theorem w1452BoundaryRelationKeepsConstructedBoundaryData
    (input : W987BoundaryRelationFieldDataConstructionInputW1452) :
    boundaryData_of_boundaryRelationDataW730
        (boundaryRelationDataOfW987BoundaryRelationFieldDataW1452 input) =
      boundaryDataOfW987BoundaryRelationFieldDataW1452 input :=
  rfl

/-- W1452's W730 construction keeps the constructed W717 relation data. -/
theorem w1452BoundaryRelationKeepsConstructedRelationData
    (input : W987BoundaryRelationFieldDataConstructionInputW1452) :
    relationData_of_boundaryRelationDataW730
        (boundaryRelationDataOfW987BoundaryRelationFieldDataW1452 input) =
      relationDataOfW987BoundaryRelationFieldDataW1452 input :=
  rfl

/-- W1452's W987 provider projects to the constructed W730 data. -/
theorem w1452FullDataKeepsConstructedBoundaryRelation
    (input : W987BoundaryRelationFieldDataConstructionInputW1452) :
    boundaryRelationDataOfFullDataW987
        (fullDataOfW987BoundaryRelationFieldDataW1452 input) =
      boundaryRelationDataOfW987BoundaryRelationFieldDataW1452 input :=
  rfl

/-- W1452's W987 provider projects to the constructed W986 target/endpoint data. -/
theorem w1452FullDataKeepsConstructedTargetNormalizedEndpoint
    (input : W987BoundaryRelationFieldDataConstructionInputW1452) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (fullDataOfW987BoundaryRelationFieldDataW1452 input) =
      targetNormalizedEndpointDataOfW987BoundaryRelationFieldDataW1452
        input :=
  rfl

def w987BoundaryRelationFieldDataConstructionInputNamesW1452 :
    List String :=
  ["raw right-open closed-quotient-cover WPP-limit boundary field",
    "raw source-difference cokernel-pi-zero WPP-limit boundary field",
    "raw closed-natural-transformation relation-pullback provider",
    "raw closed-natural-transformation target-relation-lifts provider",
    "W984 target/closed-embedding closedness data",
    "W950 normalized-source/endpoint-localized-unit data"]

theorem w987BoundaryRelationFieldDataConstructionInputNamesW1452_count :
    w987BoundaryRelationFieldDataConstructionInputNamesW1452.length = 6 :=
  rfl

def w987BoundaryRelationFieldDataConstructionBundledRelationInputNamesW1452 :
    List String :=
  ["W717 closed natural-transformation relation data"]

theorem w987BoundaryRelationFieldDataConstructionBundledRelationInputNamesW1452_count :
    w987BoundaryRelationFieldDataConstructionBundledRelationInputNamesW1452.length =
      1 :=
  rfl

def w987BoundaryRelationFieldDataConstructionRelationInputNamesW1452 :
    List String :=
  ["raw closed-natural-transformation relation-pullback provider",
    "raw closed-natural-transformation target-relation-lifts provider"]

theorem w987BoundaryRelationFieldDataConstructionRelationInputNamesW1452_count :
    w987BoundaryRelationFieldDataConstructionRelationInputNamesW1452.length = 2 :=
  rfl

/-- W1452 splits W1451's one W717 relation-data input into two raw fields. -/
theorem w1452BoundaryRelationFieldDataConstructionSplitsW717Input :
    w987BoundaryRelationFieldDataConstructionBundledRelationInputNamesW1452.length <
      w987BoundaryRelationFieldDataConstructionRelationInputNamesW1452.length := by
  rw [w987BoundaryRelationFieldDataConstructionBundledRelationInputNamesW1452_count,
    w987BoundaryRelationFieldDataConstructionRelationInputNamesW1452_count]
  norm_num

/-- W1452 replaces the five W1451 inputs by six named construction inputs. -/
theorem w1452BoundaryRelationFieldDataConstructionExpandsW1451InputCount :
    w987BoundaryFieldDataConstructionInputNamesW1451.length <
      w987BoundaryRelationFieldDataConstructionInputNamesW1452.length := by
  rw [w987BoundaryFieldDataConstructionInputNamesW1451_count,
    w987BoundaryRelationFieldDataConstructionInputNamesW1452_count]
  norm_num

/-- Current W1452 nonterminal relation-field construction state. -/
structure W987BoundaryRelationFieldDataConstructionStateW1452 : Type where
  seed : String
  declarations : List String
  constructionResult : String
  projectionResult : String
  relationInputNames : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1452 records the raw-relation-field construction path into W1451. -/
def currentW987BoundaryRelationFieldDataConstructionStateW1452 :
    W987BoundaryRelationFieldDataConstructionStateW1452 where
  seed := "w1452-w987-boundary-relation-field-data-construction"
  declarations :=
    ["W987BoundaryRelationFieldDataConstructionInputW1452",
      "relationDataOfW987BoundaryRelationFieldDataW1452",
      "w1451InputOfW987BoundaryRelationFieldDataW1452",
      "boundaryDataOfW987BoundaryRelationFieldDataW1452",
      "boundaryRelationDataOfW987BoundaryRelationFieldDataW1452",
      "targetNormalizedEndpointDataOfW987BoundaryRelationFieldDataW1452",
      "fullDataOfW987BoundaryRelationFieldDataW1452",
      "w1452RelationDataKeepsRelationPullbackProvider",
      "w1452RelationDataKeepsTargetRelationLiftsProvider",
      "w1452InputKeepsRightOpenBoundary",
      "w1452InputKeepsSourcePiZeroBoundary",
      "w1452InputKeepsConstructedRelationData",
      "w1452InputKeepsTargetClosednessData",
      "w1452InputKeepsNormalizedEndpointData",
      "w1452BoundaryRelationKeepsConstructedBoundaryData",
      "w1452BoundaryRelationKeepsConstructedRelationData",
      "w1452FullDataKeepsConstructedBoundaryRelation",
      "w1452FullDataKeepsConstructedTargetNormalizedEndpoint",
      "w987BoundaryRelationFieldDataConstructionInputNamesW1452_count",
      "w1452BoundaryRelationFieldDataConstructionSplitsW717Input",
      "w1452BoundaryRelationFieldDataConstructionExpandsW1451InputCount"]
  constructionResult :=
    "proved: W717 relation data can be assembled from raw relation-pullback\
      and target-relation-lifts providers before running W1451's W987\
      construction"
  projectionResult :=
    "proved: the constructed W717, W730, W986, and W987 providers project back\
      to the W1452 relation fields, boundary fields, and carried W984/W950 data"
  relationInputNames :=
    w987BoundaryRelationFieldDataConstructionRelationInputNamesW1452
  remainingInputs := w987BoundaryRelationFieldDataConstructionInputNamesW1452
  productSuccessClaimed := false

theorem currentW1452W987BoundaryRelationFieldDataConstruction_productSuccess :
    currentW987BoundaryRelationFieldDataConstructionStateW1452.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
