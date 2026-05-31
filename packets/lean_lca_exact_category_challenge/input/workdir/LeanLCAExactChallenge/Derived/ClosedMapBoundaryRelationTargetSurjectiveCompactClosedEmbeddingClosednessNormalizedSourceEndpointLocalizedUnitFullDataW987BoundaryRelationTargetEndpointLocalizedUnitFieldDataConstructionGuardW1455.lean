import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionGuardW1454

/-!
W1455 refines W1454 by constructing its W949 endpoint-localized-unit input
from endpoint strict-exact witnesses and W945 localized-unit data, then runs the
resulting data through the W1454/W1453/W1452/W1451/W1450 W987 construction.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

/--
W1455 replaces the W1454 W949 endpoint-localized-unit input by separate
endpoint strict-exact witnesses and W945 localized-unit data.
-/
structure W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputW1455 :
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
  endpointStrictExact :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i)
  localizedUnitData :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945

/-- W1455 builds W949 endpoint-localized-unit data from endpoint and W945 data. -/
def endpointLocalizedUnitDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
    (input :
      W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputW1455) :
    EndpointStrictExactLocalizedUnitDataProviderW949 where
  endpointStrictExact := input.endpointStrictExact
  localizedUnitData := input.localizedUnitData

/-- W1455 builds the W1454 input after constructing W949 data. -/
def w1454InputOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
    (input :
      W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputW1455) :
    W987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputW1454 where
  rightOpenBoundary := input.rightOpenBoundary
  sourcePiZeroBoundary := input.sourcePiZeroBoundary
  relationPullbackProvider := input.relationPullbackProvider
  targetRelationLiftsProvider := input.targetRelationLiftsProvider
  targetNoUnivData := input.targetNoUnivData
  closedEmbeddingClosednessData := input.closedEmbeddingClosednessData
  normalizedSourceTriangulationData := input.normalizedSourceTriangulationData
  endpointLocalizedUnitData :=
    endpointLocalizedUnitDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
      input

/-- W1455 builds W950 normalized-source/endpoint data through W1454. -/
def normalizedSourceEndpointLocalizedUnitDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
    (input :
      W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputW1455) :
    NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950 :=
  normalizedSourceEndpointLocalizedUnitDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
    (w1454InputOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
      input)

/-- W1455 builds W984 target/closedness data through W1454. -/
def targetClosedEmbeddingClosednessDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
    (input :
      W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputW1455) :
    TargetNoUnivClosedEmbeddingClosednessDataProviderW984 :=
  targetClosedEmbeddingClosednessDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
    (w1454InputOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
      input)

/-- W1455 builds W717 relation data through W1454. -/
def relationDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
    (input :
      W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputW1455) :
    ClosedNatTransOrdinaryRelationDataProviderW717 :=
  relationDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
    (w1454InputOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
      input)

/-- W1455 builds W716 boundary data through W1454. -/
def boundaryDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
    (input :
      W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputW1455) :
    MetrizableWppLimitBoundaryDataW716 :=
  boundaryDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
    (w1454InputOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
      input)

/-- W1455 builds W730 boundary/relation data through W1454. -/
def boundaryRelationDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
    (input :
      W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputW1455) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
    (w1454InputOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
      input)

/-- W1455 builds W986 target/endpoint data through W1454. -/
def targetNormalizedEndpointDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
    (input :
      W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputW1455) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetNormalizedEndpointDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
    (w1454InputOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
      input)

/-- W1455 builds the remaining W987 full-data provider through W1454. -/
noncomputable def fullDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
    (input :
      W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputW1455) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfW987BoundaryRelationTargetNormalizedEndpointFieldDataW1454
    (w1454InputOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
      input)

/-- W1455's constructed W949 data keeps the endpoint strict-exact witnesses. -/
theorem w1455EndpointLocalizedUnitDataKeepsEndpointStrictExact
    (input :
      W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputW1455) :
    endpointStrictExactOfEndpointLocalizedUnitDataW949
        (endpointLocalizedUnitDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
          input) =
      input.endpointStrictExact :=
  rfl

/-- W1455's constructed W949 data keeps the W945 localized-unit data. -/
theorem w1455EndpointLocalizedUnitDataKeepsLocalizedUnitData
    (input :
      W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputW1455) :
    localizedUnitDataOfEndpointLocalizedUnitDataW949
        (endpointLocalizedUnitDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
          input) =
      input.localizedUnitData :=
  rfl

/-- W1455's constructed W950 data keeps the W948 normalized-source provider. -/
theorem w1455NormalizedEndpointDataKeepsNormalizedSourceTriangulationData
    (input :
      W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputW1455) :
    normalizedSourceTriangulationDataOfNormalizedSourceEndpointLocalizedUnitDataW950
        (normalizedSourceEndpointLocalizedUnitDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
          input) =
      input.normalizedSourceTriangulationData :=
  rfl

/-- W1455's constructed W950 data keeps the constructed W949 data. -/
theorem w1455NormalizedEndpointDataKeepsConstructedEndpointLocalizedUnitData
    (input :
      W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputW1455) :
    endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitDataW950
        (normalizedSourceEndpointLocalizedUnitDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
          input) =
      endpointLocalizedUnitDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
        input :=
  rfl

/-- W1455's W1454 input keeps the raw right-open boundary field. -/
theorem w1455InputKeepsRightOpenBoundary
    (input :
      W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputW1455) :
    (w1454InputOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
        input).rightOpenBoundary =
      input.rightOpenBoundary :=
  rfl

/-- W1455's W1454 input keeps the raw source-pi-zero boundary field. -/
theorem w1455InputKeepsSourcePiZeroBoundary
    (input :
      W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputW1455) :
    (w1454InputOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
        input).sourcePiZeroBoundary =
      input.sourcePiZeroBoundary :=
  rfl

/-- W1455's W1454 input keeps the raw relation-pullback field. -/
theorem w1455InputKeepsRelationPullbackProvider
    (input :
      W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputW1455) :
    (w1454InputOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
        input).relationPullbackProvider =
      input.relationPullbackProvider :=
  rfl

/-- W1455's W1454 input keeps the raw target-relation-lifts field. -/
theorem w1455InputKeepsTargetRelationLiftsProvider
    (input :
      W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputW1455) :
    (w1454InputOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
        input).targetRelationLiftsProvider =
      input.targetRelationLiftsProvider :=
  rfl

/-- W1455's W1454 input keeps the W944 target no-univ provider. -/
theorem w1455InputKeepsTargetNoUnivData
    (input :
      W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputW1455) :
    (w1454InputOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
        input).targetNoUnivData =
      input.targetNoUnivData :=
  rfl

/-- W1455's W1454 input keeps the W973 closedness provider. -/
theorem w1455InputKeepsClosedEmbeddingClosednessData
    (input :
      W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputW1455) :
    (w1454InputOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
        input).closedEmbeddingClosednessData =
      input.closedEmbeddingClosednessData :=
  rfl

/-- W1455's W1454 input keeps the W948 normalized-source provider. -/
theorem w1455InputKeepsNormalizedSourceTriangulationData
    (input :
      W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputW1455) :
    (w1454InputOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
        input).normalizedSourceTriangulationData =
      input.normalizedSourceTriangulationData :=
  rfl

/-- W1455's W1454 input keeps the constructed W949 endpoint-localized-unit data. -/
theorem w1455InputKeepsConstructedEndpointLocalizedUnitData
    (input :
      W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputW1455) :
    (w1454InputOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
        input).endpointLocalizedUnitData =
      endpointLocalizedUnitDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
        input :=
  rfl

/-- W1455's W730 construction keeps the constructed W716 boundary data. -/
theorem w1455BoundaryRelationKeepsConstructedBoundaryData
    (input :
      W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputW1455) :
    boundaryData_of_boundaryRelationDataW730
        (boundaryRelationDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
          input) =
      boundaryDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
        input :=
  rfl

/-- W1455's W730 construction keeps the constructed W717 relation data. -/
theorem w1455BoundaryRelationKeepsConstructedRelationData
    (input :
      W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputW1455) :
    relationData_of_boundaryRelationDataW730
        (boundaryRelationDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
          input) =
      relationDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
        input :=
  rfl

/-- W1455's W986 construction keeps the constructed W984 target/closedness data. -/
theorem w1455TargetNormalizedEndpointKeepsConstructedTargetClosedness
    (input :
      W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputW1455) :
    targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
        (targetNormalizedEndpointDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
          input) =
      targetClosedEmbeddingClosednessDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
        input :=
  rfl

/-- W1455's W986 construction keeps the constructed W950 normalized-endpoint data. -/
theorem w1455TargetNormalizedEndpointKeepsConstructedNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputW1455) :
    normalizedSourceEndpointLocalizedUnitDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
        (targetNormalizedEndpointDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
          input) =
      normalizedSourceEndpointLocalizedUnitDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
        input :=
  rfl

/-- W1455's W987 provider projects to the constructed W730 data. -/
theorem w1455FullDataKeepsConstructedBoundaryRelation
    (input :
      W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputW1455) :
    boundaryRelationDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
          input) =
      boundaryRelationDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
        input :=
  rfl

/-- W1455's W987 provider projects to the constructed W986 target/endpoint data. -/
theorem w1455FullDataKeepsConstructedTargetNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputW1455) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
          input) =
      targetNormalizedEndpointDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
        input :=
  rfl

def w987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputNamesW1455 :
    List String :=
  ["raw right-open closed-quotient-cover WPP-limit boundary field",
    "raw source-difference cokernel-pi-zero WPP-limit boundary field",
    "raw closed-natural-transformation relation-pullback provider",
    "raw closed-natural-transformation target-relation-lifts provider",
    "W944 target no-univ data",
    "W973 closed-embedding closedness data",
    "W948 normalized-source-triangulation data",
    "endpoint strict short-exact witnesses",
    "W945 localized-unit data"]

theorem w987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputNamesW1455_count :
    w987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputNamesW1455.length =
      9 :=
  rfl

def w987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionBundledEndpointInputNamesW1455 :
    List String :=
  ["W949 endpoint-localized-unit data"]

theorem w987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionBundledEndpointInputNamesW1455_count :
    w987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionBundledEndpointInputNamesW1455.length =
      1 :=
  rfl

def w987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionEndpointInputNamesW1455 :
    List String :=
  ["endpoint strict short-exact witnesses", "W945 localized-unit data"]

theorem w987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionEndpointInputNamesW1455_count :
    w987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionEndpointInputNamesW1455.length =
      2 :=
  rfl

/-- W1455 splits W1454's one W949 endpoint-localized-unit input into two fields. -/
theorem w1455BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionSplitsW949Input :
    w987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionBundledEndpointInputNamesW1455.length <
      w987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionEndpointInputNamesW1455.length := by
  rw [
    w987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionBundledEndpointInputNamesW1455_count,
    w987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionEndpointInputNamesW1455_count]
  norm_num

/-- W1455 replaces the eight W1454 inputs by nine named construction inputs. -/
theorem w1455BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionExpandsW1454InputCount :
    w987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputNamesW1454.length <
      w987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputNamesW1455.length := by
  rw [w987BoundaryRelationTargetNormalizedEndpointFieldDataConstructionInputNamesW1454_count,
    w987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputNamesW1455_count]
  norm_num

/-- Current W1455 nonterminal endpoint-localized-unit construction state. -/
structure W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionStateW1455 :
    Type where
  seed : String
  declarations : List String
  constructionResult : String
  projectionResult : String
  endpointInputNames : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1455 records the endpoint/W945 construction path into W1454. -/
def currentW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionStateW1455 :
    W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionStateW1455 where
  seed :=
    "w1455-w987-boundary-relation-target-endpoint-localized-unit-field-data-construction"
  declarations :=
    ["W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputW1455",
      "endpointLocalizedUnitDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455",
      "w1454InputOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455",
      "normalizedSourceEndpointLocalizedUnitDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455",
      "targetClosedEmbeddingClosednessDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455",
      "relationDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455",
      "boundaryDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455",
      "boundaryRelationDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455",
      "targetNormalizedEndpointDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455",
      "fullDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455",
      "w1455EndpointLocalizedUnitDataKeepsEndpointStrictExact",
      "w1455EndpointLocalizedUnitDataKeepsLocalizedUnitData",
      "w1455NormalizedEndpointDataKeepsNormalizedSourceTriangulationData",
      "w1455NormalizedEndpointDataKeepsConstructedEndpointLocalizedUnitData",
      "w1455InputKeepsRightOpenBoundary",
      "w1455InputKeepsSourcePiZeroBoundary",
      "w1455InputKeepsRelationPullbackProvider",
      "w1455InputKeepsTargetRelationLiftsProvider",
      "w1455InputKeepsTargetNoUnivData",
      "w1455InputKeepsClosedEmbeddingClosednessData",
      "w1455InputKeepsNormalizedSourceTriangulationData",
      "w1455InputKeepsConstructedEndpointLocalizedUnitData",
      "w1455BoundaryRelationKeepsConstructedBoundaryData",
      "w1455BoundaryRelationKeepsConstructedRelationData",
      "w1455TargetNormalizedEndpointKeepsConstructedTargetClosedness",
      "w1455TargetNormalizedEndpointKeepsConstructedNormalizedEndpoint",
      "w1455FullDataKeepsConstructedBoundaryRelation",
      "w1455FullDataKeepsConstructedTargetNormalizedEndpoint",
      "w987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputNamesW1455_count",
      "w1455BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionSplitsW949Input",
      "w1455BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionExpandsW1454InputCount"]
  constructionResult :=
    "proved: W949 endpoint-localized-unit data can be assembled from endpoint\
      strict-exact witnesses and W945 localized-unit data before running\
      W1454's W987 construction"
  projectionResult :=
    "proved: the constructed W949, W950, W730, W986, and W987 providers\
      project back to the W1455 endpoint fields, normalized-source field,\
      target fields, relation fields, and boundary fields"
  endpointInputNames :=
    w987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionEndpointInputNamesW1455
  remainingInputs :=
    w987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputNamesW1455
  productSuccessClaimed := false

theorem currentW1455W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstruction_productSuccess :
    currentW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionStateW1455.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
