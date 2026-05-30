import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987BoundaryRelationFieldDataConstructionGuardW1452

/-!
W1453 refines W1452 by constructing its W984 target/closedness input from the
W944 target no-univ provider and the W973 closed-embedding closedness provider,
then runs the resulting data through the W1452/W1451/W1450 W987 construction.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

/--
W1453 replaces the W1452 W984 target/closedness input by separate W944 and W973
providers.
-/
structure W987BoundaryRelationTargetFieldDataConstructionInputW1453 :
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
  normalizedSourceEndpointLocalizedUnitData :
    NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950

/-- W1453 builds W984 target/closedness data from W944 and W973 data. -/
def targetClosedEmbeddingClosednessDataOfW987BoundaryRelationTargetFieldDataW1453
    (input :
      W987BoundaryRelationTargetFieldDataConstructionInputW1453) :
    TargetNoUnivClosedEmbeddingClosednessDataProviderW984
    where
  targetNoUnivData := input.targetNoUnivData
  closedEmbeddingClosednessData := input.closedEmbeddingClosednessData

/-- W1453 builds the W1452 input after constructing W984 target/closedness data. -/
def w1452InputOfW987BoundaryRelationTargetFieldDataW1453
    (input :
      W987BoundaryRelationTargetFieldDataConstructionInputW1453) :
    W987BoundaryRelationFieldDataConstructionInputW1452 where
  rightOpenBoundary := input.rightOpenBoundary
  sourcePiZeroBoundary := input.sourcePiZeroBoundary
  relationPullbackProvider := input.relationPullbackProvider
  targetRelationLiftsProvider := input.targetRelationLiftsProvider
  targetClosedEmbeddingClosednessData :=
    targetClosedEmbeddingClosednessDataOfW987BoundaryRelationTargetFieldDataW1453
      input
  normalizedSourceEndpointLocalizedUnitData :=
    input.normalizedSourceEndpointLocalizedUnitData

/-- W1453 builds W717 relation data through W1452. -/
def relationDataOfW987BoundaryRelationTargetFieldDataW1453
    (input :
      W987BoundaryRelationTargetFieldDataConstructionInputW1453) :
    ClosedNatTransOrdinaryRelationDataProviderW717 :=
  relationDataOfW987BoundaryRelationFieldDataW1452
    (w1452InputOfW987BoundaryRelationTargetFieldDataW1453 input)

/-- W1453 builds W716 boundary data through W1452. -/
def boundaryDataOfW987BoundaryRelationTargetFieldDataW1453
    (input :
      W987BoundaryRelationTargetFieldDataConstructionInputW1453) :
    MetrizableWppLimitBoundaryDataW716 :=
  boundaryDataOfW987BoundaryRelationFieldDataW1452
    (w1452InputOfW987BoundaryRelationTargetFieldDataW1453 input)

/-- W1453 builds W730 boundary/relation data through W1452. -/
def boundaryRelationDataOfW987BoundaryRelationTargetFieldDataW1453
    (input :
      W987BoundaryRelationTargetFieldDataConstructionInputW1453) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfW987BoundaryRelationFieldDataW1452
    (w1452InputOfW987BoundaryRelationTargetFieldDataW1453 input)

/-- W1453 builds W986 target/endpoint data through W1452. -/
def targetNormalizedEndpointDataOfW987BoundaryRelationTargetFieldDataW1453
    (input :
      W987BoundaryRelationTargetFieldDataConstructionInputW1453) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetNormalizedEndpointDataOfW987BoundaryRelationFieldDataW1452
    (w1452InputOfW987BoundaryRelationTargetFieldDataW1453 input)

/-- W1453 builds the remaining W987 full-data provider through W1452. -/
noncomputable def fullDataOfW987BoundaryRelationTargetFieldDataW1453
    (input :
      W987BoundaryRelationTargetFieldDataConstructionInputW1453) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfW987BoundaryRelationFieldDataW1452
    (w1452InputOfW987BoundaryRelationTargetFieldDataW1453 input)

/-- W1453's constructed W984 data keeps the W944 target no-univ provider. -/
theorem w1453TargetClosednessDataKeepsTargetNoUnivData
    (input :
      W987BoundaryRelationTargetFieldDataConstructionInputW1453) :
    targetNoUnivDataOfTargetClosedEmbeddingClosednessDataW984
        (targetClosedEmbeddingClosednessDataOfW987BoundaryRelationTargetFieldDataW1453
          input) =
      input.targetNoUnivData :=
  rfl

/-- W1453's constructed W984 data keeps the W973 closedness provider. -/
theorem w1453TargetClosednessDataKeepsClosedEmbeddingClosednessData
    (input :
      W987BoundaryRelationTargetFieldDataConstructionInputW1453) :
    closedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessDataW984
        (targetClosedEmbeddingClosednessDataOfW987BoundaryRelationTargetFieldDataW1453
          input) =
      input.closedEmbeddingClosednessData :=
  rfl

/-- W1453's W1452 input keeps the raw right-open boundary field. -/
theorem w1453InputKeepsRightOpenBoundary
    (input :
      W987BoundaryRelationTargetFieldDataConstructionInputW1453) :
    (w1452InputOfW987BoundaryRelationTargetFieldDataW1453
        input).rightOpenBoundary =
      input.rightOpenBoundary :=
  rfl

/-- W1453's W1452 input keeps the raw source-pi-zero boundary field. -/
theorem w1453InputKeepsSourcePiZeroBoundary
    (input :
      W987BoundaryRelationTargetFieldDataConstructionInputW1453) :
    (w1452InputOfW987BoundaryRelationTargetFieldDataW1453
        input).sourcePiZeroBoundary =
      input.sourcePiZeroBoundary :=
  rfl

/-- W1453's W1452 input keeps the raw relation-pullback field. -/
theorem w1453InputKeepsRelationPullbackProvider
    (input :
      W987BoundaryRelationTargetFieldDataConstructionInputW1453) :
    (w1452InputOfW987BoundaryRelationTargetFieldDataW1453
        input).relationPullbackProvider =
      input.relationPullbackProvider :=
  rfl

/-- W1453's W1452 input keeps the raw target-relation-lifts field. -/
theorem w1453InputKeepsTargetRelationLiftsProvider
    (input :
      W987BoundaryRelationTargetFieldDataConstructionInputW1453) :
    (w1452InputOfW987BoundaryRelationTargetFieldDataW1453
        input).targetRelationLiftsProvider =
      input.targetRelationLiftsProvider :=
  rfl

/-- W1453's W1452 input keeps the constructed W984 target/closedness data. -/
theorem w1453InputKeepsConstructedTargetClosednessData
    (input :
      W987BoundaryRelationTargetFieldDataConstructionInputW1453) :
    (w1452InputOfW987BoundaryRelationTargetFieldDataW1453
        input).targetClosedEmbeddingClosednessData =
      targetClosedEmbeddingClosednessDataOfW987BoundaryRelationTargetFieldDataW1453
        input :=
  rfl

/-- W1453's W1452 input keeps the original W950 normalized-endpoint data. -/
theorem w1453InputKeepsNormalizedEndpointData
    (input :
      W987BoundaryRelationTargetFieldDataConstructionInputW1453) :
    (w1452InputOfW987BoundaryRelationTargetFieldDataW1453
        input).normalizedSourceEndpointLocalizedUnitData =
      input.normalizedSourceEndpointLocalizedUnitData :=
  rfl

/-- W1453's W730 construction keeps the constructed W716 boundary data. -/
theorem w1453BoundaryRelationKeepsConstructedBoundaryData
    (input :
      W987BoundaryRelationTargetFieldDataConstructionInputW1453) :
    boundaryData_of_boundaryRelationDataW730
        (boundaryRelationDataOfW987BoundaryRelationTargetFieldDataW1453
          input) =
      boundaryDataOfW987BoundaryRelationTargetFieldDataW1453 input :=
  rfl

/-- W1453's W730 construction keeps the constructed W717 relation data. -/
theorem w1453BoundaryRelationKeepsConstructedRelationData
    (input :
      W987BoundaryRelationTargetFieldDataConstructionInputW1453) :
    relationData_of_boundaryRelationDataW730
        (boundaryRelationDataOfW987BoundaryRelationTargetFieldDataW1453
          input) =
      relationDataOfW987BoundaryRelationTargetFieldDataW1453 input :=
  rfl

/-- W1453's W986 construction keeps the constructed W984 target/closedness data. -/
theorem w1453TargetNormalizedEndpointKeepsConstructedTargetClosedness
    (input :
      W987BoundaryRelationTargetFieldDataConstructionInputW1453) :
    targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
        (targetNormalizedEndpointDataOfW987BoundaryRelationTargetFieldDataW1453
          input) =
      targetClosedEmbeddingClosednessDataOfW987BoundaryRelationTargetFieldDataW1453
        input :=
  rfl

/-- W1453's W986 construction keeps the original W950 normalized-endpoint data. -/
theorem w1453TargetNormalizedEndpointKeepsNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetFieldDataConstructionInputW1453) :
    normalizedSourceEndpointLocalizedUnitDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
        (targetNormalizedEndpointDataOfW987BoundaryRelationTargetFieldDataW1453
          input) =
      input.normalizedSourceEndpointLocalizedUnitData :=
  rfl

/-- W1453's W987 provider projects to the constructed W730 data. -/
theorem w1453FullDataKeepsConstructedBoundaryRelation
    (input :
      W987BoundaryRelationTargetFieldDataConstructionInputW1453) :
    boundaryRelationDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetFieldDataW1453 input) =
      boundaryRelationDataOfW987BoundaryRelationTargetFieldDataW1453
        input :=
  rfl

/-- W1453's W987 provider projects to the constructed W986 target/endpoint data. -/
theorem w1453FullDataKeepsConstructedTargetNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetFieldDataConstructionInputW1453) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetFieldDataW1453 input) =
      targetNormalizedEndpointDataOfW987BoundaryRelationTargetFieldDataW1453
        input :=
  rfl

def w987BoundaryRelationTargetFieldDataConstructionInputNamesW1453 :
    List String :=
  ["raw right-open closed-quotient-cover WPP-limit boundary field",
    "raw source-difference cokernel-pi-zero WPP-limit boundary field",
    "raw closed-natural-transformation relation-pullback provider",
    "raw closed-natural-transformation target-relation-lifts provider",
    "W944 target no-univ data",
    "W973 closed-embedding closedness data",
    "W950 normalized-source/endpoint-localized-unit data"]

theorem w987BoundaryRelationTargetFieldDataConstructionInputNamesW1453_count :
    w987BoundaryRelationTargetFieldDataConstructionInputNamesW1453.length = 7 :=
  rfl

def w987BoundaryRelationTargetFieldDataConstructionBundledTargetInputNamesW1453 :
    List String :=
  ["W984 target/closed-embedding closedness data"]

theorem w987BoundaryRelationTargetFieldDataConstructionBundledTargetInputNamesW1453_count :
    w987BoundaryRelationTargetFieldDataConstructionBundledTargetInputNamesW1453.length =
      1 :=
  rfl

def w987BoundaryRelationTargetFieldDataConstructionTargetInputNamesW1453 :
    List String :=
  ["W944 target no-univ data",
    "W973 closed-embedding closedness data"]

theorem w987BoundaryRelationTargetFieldDataConstructionTargetInputNamesW1453_count :
    w987BoundaryRelationTargetFieldDataConstructionTargetInputNamesW1453.length =
      2 :=
  rfl

/-- W1453 splits W1452's one W984 target/closedness input into two fields. -/
theorem w1453BoundaryRelationTargetFieldDataConstructionSplitsW984Input :
    w987BoundaryRelationTargetFieldDataConstructionBundledTargetInputNamesW1453.length <
      w987BoundaryRelationTargetFieldDataConstructionTargetInputNamesW1453.length := by
  rw [w987BoundaryRelationTargetFieldDataConstructionBundledTargetInputNamesW1453_count,
    w987BoundaryRelationTargetFieldDataConstructionTargetInputNamesW1453_count]
  norm_num

/-- W1453 replaces the six W1452 inputs by seven named construction inputs. -/
theorem w1453BoundaryRelationTargetFieldDataConstructionExpandsW1452InputCount :
    w987BoundaryRelationFieldDataConstructionInputNamesW1452.length <
      w987BoundaryRelationTargetFieldDataConstructionInputNamesW1453.length := by
  rw [w987BoundaryRelationFieldDataConstructionInputNamesW1452_count,
    w987BoundaryRelationTargetFieldDataConstructionInputNamesW1453_count]
  norm_num

/-- Current W1453 nonterminal target-field construction state. -/
structure W987BoundaryRelationTargetFieldDataConstructionStateW1453 :
    Type where
  seed : String
  declarations : List String
  constructionResult : String
  projectionResult : String
  targetInputNames : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1453 records the W944/W973 construction path into W1452. -/
def currentW987BoundaryRelationTargetFieldDataConstructionStateW1453 :
    W987BoundaryRelationTargetFieldDataConstructionStateW1453 where
  seed := "w1453-w987-boundary-relation-target-field-data-construction"
  declarations :=
    ["W987BoundaryRelationTargetFieldDataConstructionInputW1453",
      "targetClosedEmbeddingClosednessDataOfW987BoundaryRelationTargetFieldDataW1453",
      "w1452InputOfW987BoundaryRelationTargetFieldDataW1453",
      "relationDataOfW987BoundaryRelationTargetFieldDataW1453",
      "boundaryDataOfW987BoundaryRelationTargetFieldDataW1453",
      "boundaryRelationDataOfW987BoundaryRelationTargetFieldDataW1453",
      "targetNormalizedEndpointDataOfW987BoundaryRelationTargetFieldDataW1453",
      "fullDataOfW987BoundaryRelationTargetFieldDataW1453",
      "w1453TargetClosednessDataKeepsTargetNoUnivData",
      "w1453TargetClosednessDataKeepsClosedEmbeddingClosednessData",
      "w1453InputKeepsRightOpenBoundary",
      "w1453InputKeepsSourcePiZeroBoundary",
      "w1453InputKeepsRelationPullbackProvider",
      "w1453InputKeepsTargetRelationLiftsProvider",
      "w1453InputKeepsConstructedTargetClosednessData",
      "w1453InputKeepsNormalizedEndpointData",
      "w1453BoundaryRelationKeepsConstructedBoundaryData",
      "w1453BoundaryRelationKeepsConstructedRelationData",
      "w1453TargetNormalizedEndpointKeepsConstructedTargetClosedness",
      "w1453TargetNormalizedEndpointKeepsNormalizedEndpoint",
      "w1453FullDataKeepsConstructedBoundaryRelation",
      "w1453FullDataKeepsConstructedTargetNormalizedEndpoint",
      "w987BoundaryRelationTargetFieldDataConstructionInputNamesW1453_count",
      "w1453BoundaryRelationTargetFieldDataConstructionSplitsW984Input",
      "w1453BoundaryRelationTargetFieldDataConstructionExpandsW1452InputCount"]
  constructionResult :=
    "proved: W984 target/closedness data can be assembled from W944 target\
      no-univ data and W973 closed-embedding closedness data before running\
      W1452's W987 construction"
  projectionResult :=
    "proved: the constructed W984, W730, W986, and W987 providers project back\
      to the W1453 target fields, relation fields, boundary fields, and carried\
      W950 data"
  targetInputNames :=
    w987BoundaryRelationTargetFieldDataConstructionTargetInputNamesW1453
  remainingInputs := w987BoundaryRelationTargetFieldDataConstructionInputNamesW1453
  productSuccessClaimed := false

theorem currentW1453W987BoundaryRelationTargetFieldDataConstruction_productSuccess :
    currentW987BoundaryRelationTargetFieldDataConstructionStateW1453.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
