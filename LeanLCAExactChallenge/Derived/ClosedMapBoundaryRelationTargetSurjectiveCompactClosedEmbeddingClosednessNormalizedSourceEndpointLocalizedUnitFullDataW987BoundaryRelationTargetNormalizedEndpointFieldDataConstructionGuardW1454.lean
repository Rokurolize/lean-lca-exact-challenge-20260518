import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987BoundaryRelationTargetFieldDataConstructionGuardW1453

/-!
W1454 refines W1453 by constructing its W950 normalized-source/endpoint input
from W948 normalized-source-triangulation data and W949 endpoint-localized-unit
data, then runs the resulting data through the W1453/W1452/W1451/W1450 W987
construction.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

/--
W1454 replaces the W1453 W950 normalized-source/endpoint input by separate
W948 and W949 providers.
-/
structure W987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputW1454 :
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
  normalizedSourceTriangulationData :
    NormalizedFixedTargetSourceTriangulationDataProviderW948
  endpointLocalizedUnitData :
    EndpointStrictExactLocalizedUnitDataProviderW949

/-- W1454 builds W950 normalized-source/endpoint data from W948 and W949 data. -/
def normalizedSourceEndpointLocalizedUnitDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
    (input :
      W987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputW1454) :
    NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950
    where
  normalizedSourceTriangulationData :=
    input.normalizedSourceTriangulationData
  endpointLocalizedUnitData := input.endpointLocalizedUnitData

/-- W1454 builds the W1453 input after constructing W950 data. -/
def w1453InputOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
    (input :
      W987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputW1454) :
    W987BoundaryRelationTargetFieldDataConstructionInputW1453 where
  rightOpenBoundary := input.rightOpenBoundary
  sourcePiZeroBoundary := input.sourcePiZeroBoundary
  relationPullbackProvider := input.relationPullbackProvider
  targetRelationLiftsProvider := input.targetRelationLiftsProvider
  targetNoUnivData := input.targetNoUnivData
  closedEmbeddingClosednessData := input.closedEmbeddingClosednessData
  normalizedSourceEndpointLocalizedUnitData :=
    normalizedSourceEndpointLocalizedUnitDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
      input

/-- W1454 builds W984 target/closedness data through W1453. -/
def targetClosedEmbeddingClosednessDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
    (input :
      W987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputW1454) :
    TargetNoUnivClosedEmbeddingClosednessDataProviderW984 :=
  targetClosedEmbeddingClosednessDataOfW987BoundaryRelationTargetFieldDataW1453
    (w1453InputOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
      input)

/-- W1454 builds W717 relation data through W1453. -/
def relationDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
    (input :
      W987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputW1454) :
    ClosedNatTransOrdinaryRelationDataProviderW717 :=
  relationDataOfW987BoundaryRelationTargetFieldDataW1453
    (w1453InputOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
      input)

/-- W1454 builds W716 boundary data through W1453. -/
def boundaryDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
    (input :
      W987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputW1454) :
    MetrizableWppLimitBoundaryDataW716 :=
  boundaryDataOfW987BoundaryRelationTargetFieldDataW1453
    (w1453InputOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
      input)

/-- W1454 builds W730 boundary/relation data through W1453. -/
def boundaryRelationDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
    (input :
      W987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputW1454) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfW987BoundaryRelationTargetFieldDataW1453
    (w1453InputOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
      input)

/-- W1454 builds W986 target/endpoint data through W1453. -/
def targetNormalizedEndpointDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
    (input :
      W987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputW1454) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetNormalizedEndpointDataOfW987BoundaryRelationTargetFieldDataW1453
    (w1453InputOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
      input)

/-- W1454 builds the remaining W987 full-data provider through W1453. -/
noncomputable def fullDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
    (input :
      W987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputW1454) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfW987BoundaryRelationTargetFieldDataW1453
    (w1453InputOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
      input)

/-- W1454's constructed W950 data keeps the W948 normalized-source provider. -/
theorem w1454NormalizedEndpointDataKeepsNormalizedSourceTriangulationData
    (input :
      W987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputW1454) :
    normalizedSourceTriangulationDataOfNormalizedSourceEndpointLocalizedUnitDataW950
        (normalizedSourceEndpointLocalizedUnitDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
          input) =
      input.normalizedSourceTriangulationData :=
  rfl

/-- W1454's constructed W950 data keeps the W949 endpoint-localized provider. -/
theorem w1454NormalizedEndpointDataKeepsEndpointLocalizedUnitData
    (input :
      W987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputW1454) :
    endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitDataW950
        (normalizedSourceEndpointLocalizedUnitDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
          input) =
      input.endpointLocalizedUnitData :=
  rfl

/-- W1454's W1453 input keeps the raw right-open boundary field. -/
theorem w1454InputKeepsRightOpenBoundary
    (input :
      W987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputW1454) :
    (w1453InputOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
        input).rightOpenBoundary =
      input.rightOpenBoundary :=
  rfl

/-- W1454's W1453 input keeps the raw source-pi-zero boundary field. -/
theorem w1454InputKeepsSourcePiZeroBoundary
    (input :
      W987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputW1454) :
    (w1453InputOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
        input).sourcePiZeroBoundary =
      input.sourcePiZeroBoundary :=
  rfl

/-- W1454's W1453 input keeps the raw relation-pullback field. -/
theorem w1454InputKeepsRelationPullbackProvider
    (input :
      W987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputW1454) :
    (w1453InputOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
        input).relationPullbackProvider =
      input.relationPullbackProvider :=
  rfl

/-- W1454's W1453 input keeps the raw target-relation-lifts field. -/
theorem w1454InputKeepsTargetRelationLiftsProvider
    (input :
      W987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputW1454) :
    (w1453InputOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
        input).targetRelationLiftsProvider =
      input.targetRelationLiftsProvider :=
  rfl

/-- W1454's W1453 input keeps the W944 target no-univ provider. -/
theorem w1454InputKeepsTargetNoUnivData
    (input :
      W987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputW1454) :
    (w1453InputOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
        input).targetNoUnivData =
      input.targetNoUnivData :=
  rfl

/-- W1454's W1453 input keeps the W973 closedness provider. -/
theorem w1454InputKeepsClosedEmbeddingClosednessData
    (input :
      W987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputW1454) :
    (w1453InputOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
        input).closedEmbeddingClosednessData =
      input.closedEmbeddingClosednessData :=
  rfl

/-- W1454's W1453 input keeps the constructed W950 normalized-endpoint data. -/
theorem w1454InputKeepsConstructedNormalizedEndpointData
    (input :
      W987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputW1454) :
    (w1453InputOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
        input).normalizedSourceEndpointLocalizedUnitData =
      normalizedSourceEndpointLocalizedUnitDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
        input :=
  rfl

/-- W1454's W730 construction keeps the constructed W716 boundary data. -/
theorem w1454BoundaryRelationKeepsConstructedBoundaryData
    (input :
      W987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputW1454) :
    boundaryData_of_boundaryRelationDataW730
        (boundaryRelationDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
          input) =
      boundaryDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
        input :=
  rfl

/-- W1454's W730 construction keeps the constructed W717 relation data. -/
theorem w1454BoundaryRelationKeepsConstructedRelationData
    (input :
      W987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputW1454) :
    relationData_of_boundaryRelationDataW730
        (boundaryRelationDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
          input) =
      relationDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
        input :=
  rfl

/-- W1454's W986 construction keeps the constructed W984 target/closedness data. -/
theorem w1454TargetNormalizedEndpointKeepsConstructedTargetClosedness
    (input :
      W987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputW1454) :
    targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
        (targetNormalizedEndpointDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
          input) =
      targetClosedEmbeddingClosednessDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
        input :=
  rfl

/-- W1454's W986 construction keeps the constructed W950 normalized-endpoint data. -/
theorem w1454TargetNormalizedEndpointKeepsConstructedNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputW1454) :
    normalizedSourceEndpointLocalizedUnitDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
        (targetNormalizedEndpointDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
          input) =
      normalizedSourceEndpointLocalizedUnitDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
        input :=
  rfl

/-- W1454's W987 provider projects to the constructed W730 data. -/
theorem w1454FullDataKeepsConstructedBoundaryRelation
    (input :
      W987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputW1454) :
    boundaryRelationDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
          input) =
      boundaryRelationDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
        input :=
  rfl

/-- W1454's W987 provider projects to the constructed W986 target/endpoint data. -/
theorem w1454FullDataKeepsConstructedTargetNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputW1454) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
          input) =
      targetNormalizedEndpointDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
        input :=
  rfl

def w987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputNamesW1454 :
    List String :=
  ["raw right-open closed-quotient-cover WPP-limit boundary field",
    "raw source-difference cokernel-pi-zero WPP-limit boundary field",
    "raw closed-natural-transformation relation-pullback provider",
    "raw closed-natural-transformation target-relation-lifts provider",
    "W944 target no-univ data",
    "W973 closed-embedding closedness data",
    "W948 normalized-source-triangulation data",
    "W949 endpoint-localized-unit data"]

theorem w987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputNamesW1454_count :
    w987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputNamesW1454.length =
      8 :=
  rfl

def w987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionBundledNormalizedEndpointInputNamesW1454 :
    List String :=
  ["W950 normalized-source/endpoint-localized-unit data"]

theorem w987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionBundledNormalizedEndpointInputNamesW1454_count :
    w987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionBundledNormalizedEndpointInputNamesW1454.length =
      1 :=
  rfl

def w987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionNormalizedEndpointInputNamesW1454 :
    List String :=
  ["W948 normalized-source-triangulation data",
    "W949 endpoint-localized-unit data"]

theorem w987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionNormalizedEndpointInputNamesW1454_count :
    w987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionNormalizedEndpointInputNamesW1454.length =
      2 :=
  rfl

/-- W1454 splits W1453's one W950 normalized-endpoint input into two fields. -/
theorem w1454BoundaryRelationTargetNormalizedEndpointFieldDataConstructionSplitsW950Input :
    w987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionBundledNormalizedEndpointInputNamesW1454.length <
      w987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionNormalizedEndpointInputNamesW1454.length := by
  rw [
    w987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionBundledNormalizedEndpointInputNamesW1454_count,
    w987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionNormalizedEndpointInputNamesW1454_count]
  norm_num

/-- W1454 replaces the seven W1453 inputs by eight named construction inputs. -/
theorem w1454BoundaryRelationTargetNormalizedEndpointFieldDataConstructionExpandsW1453InputCount :
    w987BoundaryRelationTargetFieldDataConstructionInputNamesW1453.length <
      w987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputNamesW1454.length := by
  rw [w987BoundaryRelationTargetFieldDataConstructionInputNamesW1453_count,
    w987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputNamesW1454_count]
  norm_num

/-- Current W1454 nonterminal normalized-endpoint construction state. -/
structure W987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionStateW1454 :
    Type where
  seed : String
  declarations : List String
  constructionResult : String
  projectionResult : String
  normalizedEndpointInputNames : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1454 records the W948/W949 construction path into W1453. -/
def currentW987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionStateW1454 :
    W987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionStateW1454 where
  seed :=
    "w1454-w987-boundary-relation-target-normalized-endpoint-field-data-construction"
  declarations :=
    ["W987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputW1454",
      "normalizedSourceEndpointLocalizedUnitDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454",
      "w1453InputOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454",
      "targetClosedEmbeddingClosednessDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454",
      "relationDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454",
      "boundaryDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454",
      "boundaryRelationDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454",
      "targetNormalizedEndpointDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454",
      "fullDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454",
      "w1454NormalizedEndpointDataKeepsNormalizedSourceTriangulationData",
      "w1454NormalizedEndpointDataKeepsEndpointLocalizedUnitData",
      "w1454InputKeepsRightOpenBoundary",
      "w1454InputKeepsSourcePiZeroBoundary",
      "w1454InputKeepsRelationPullbackProvider",
      "w1454InputKeepsTargetRelationLiftsProvider",
      "w1454InputKeepsTargetNoUnivData",
      "w1454InputKeepsClosedEmbeddingClosednessData",
      "w1454InputKeepsConstructedNormalizedEndpointData",
      "w1454BoundaryRelationKeepsConstructedBoundaryData",
      "w1454BoundaryRelationKeepsConstructedRelationData",
      "w1454TargetNormalizedEndpointKeepsConstructedTargetClosedness",
      "w1454TargetNormalizedEndpointKeepsConstructedNormalizedEndpoint",
      "w1454FullDataKeepsConstructedBoundaryRelation",
      "w1454FullDataKeepsConstructedTargetNormalizedEndpoint",
      "w987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputNamesW1454_count",
      "w1454BoundaryRelationTargetNormalizedEndpointFieldDataConstructionSplitsW950Input",
      "w1454BoundaryRelationTargetNormalizedEndpointFieldDataConstructionExpandsW1453InputCount"]
  constructionResult :=
    "proved: W950 normalized-source/endpoint data can be assembled from W948\
      normalized-source-triangulation data and W949 endpoint-localized-unit\
      data before running W1453's W987 construction"
  projectionResult :=
    "proved: the constructed W950, W730, W986, and W987 providers project back\
      to the W1454 normalized-endpoint fields, target fields, relation fields,\
      and boundary fields"
  normalizedEndpointInputNames :=
    w987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionNormalizedEndpointInputNamesW1454
  remainingInputs :=
    w987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputNamesW1454
  productSuccessClaimed := false

theorem currentW1454W987BoundaryRelationTargetNormalizedEndpointFieldDataConstruction_productSuccess :
    currentW987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionStateW1454.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
