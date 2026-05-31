import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionGuardW1455

/-!
W1456 refines W1455 by constructing its W948 normalized-source-triangulation
input from W719 normalized fixed-target data and W722 source-triangulation data,
then runs the resulting data through the W1455/W1454/W1453/W1452/W1451/W1450
W987 construction.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

/--
W1456 replaces the W1455 W948 normalized-source-triangulation input by separate
W719 normalized fixed-target data and W722 source-triangulation data.
-/
structure W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456 :
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
  normalizedFixedTargetData :
    MetrizableWppNormalizedFixedTargetDataProviderW719
  sourceTriangulationData :
    MetrizableWppSourceTriangulationDataProviderW722
  endpointStrictExact :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i)
  localizedUnitData :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945

/-- W1456 builds W948 normalized-source data from W719 and W722 data. -/
def normalizedSourceTriangulationDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
    (input :
      W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456) :
    NormalizedFixedTargetSourceTriangulationDataProviderW948 where
  normalizedFixedTargetData := input.normalizedFixedTargetData
  sourceTriangulationData := input.sourceTriangulationData

/-- W1456 builds the W1455 input after constructing W948 data. -/
def w1455InputOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
    (input :
      W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456) :
    W987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputW1455 where
  rightOpenBoundary := input.rightOpenBoundary
  sourcePiZeroBoundary := input.sourcePiZeroBoundary
  relationPullbackProvider := input.relationPullbackProvider
  targetRelationLiftsProvider := input.targetRelationLiftsProvider
  targetNoUnivData := input.targetNoUnivData
  closedEmbeddingClosednessData := input.closedEmbeddingClosednessData
  normalizedSourceTriangulationData :=
    normalizedSourceTriangulationDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
      input
  endpointStrictExact := input.endpointStrictExact
  localizedUnitData := input.localizedUnitData

/-- W1456 builds W949 endpoint-localized-unit data through W1455. -/
def endpointLocalizedUnitDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
    (input :
      W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456) :
    EndpointStrictExactLocalizedUnitDataProviderW949 :=
  endpointLocalizedUnitDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
    (w1455InputOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
      input)

/-- W1456 builds W950 normalized-source/endpoint data through W1455. -/
def normalizedSourceEndpointLocalizedUnitDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
    (input :
      W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456) :
    NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950 :=
  normalizedSourceEndpointLocalizedUnitDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
    (w1455InputOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
      input)

/-- W1456 builds W984 target/closedness data through W1455. -/
def targetClosedEmbeddingClosednessDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
    (input :
      W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456) :
    TargetNoUnivClosedEmbeddingClosednessDataProviderW984 :=
  targetClosedEmbeddingClosednessDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
    (w1455InputOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
      input)

/-- W1456 builds W717 relation data through W1455. -/
def relationDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
    (input :
      W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456) :
    ClosedNatTransOrdinaryRelationDataProviderW717 :=
  relationDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
    (w1455InputOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
      input)

/-- W1456 builds W716 boundary data through W1455. -/
def boundaryDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
    (input :
      W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456) :
    MetrizableWppLimitBoundaryDataW716 :=
  boundaryDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
    (w1455InputOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
      input)

/-- W1456 builds W730 boundary/relation data through W1455. -/
def boundaryRelationDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
    (input :
      W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
    (w1455InputOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
      input)

/-- W1456 builds W986 target/endpoint data through W1455. -/
def targetNormalizedEndpointDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
    (input :
      W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetNormalizedEndpointDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
    (w1455InputOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
      input)

/-- W1456 builds the remaining W987 full-data provider through W1455. -/
noncomputable def fullDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
    (input :
      W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfW987BoundaryRelationTargetEndpointLocalizedUnitFieldDataW1455
    (w1455InputOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
      input)

/-- W1456's constructed W948 data keeps the W719 normalized fixed-target data. -/
theorem w1456NormalizedSourceDataKeepsNormalizedFixedTargetData
    (input :
      W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456) :
    normalizedFixedTargetDataOfNormalizedSourceTriangulationDataW948
        (normalizedSourceTriangulationDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
          input) =
      input.normalizedFixedTargetData :=
  rfl

/-- W1456's constructed W948 data keeps the W722 source-triangulation data. -/
theorem w1456NormalizedSourceDataKeepsSourceTriangulationData
    (input :
      W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456) :
    sourceTriangulationDataOfNormalizedSourceTriangulationDataW948
        (normalizedSourceTriangulationDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
          input) =
      input.sourceTriangulationData :=
  rfl

/-- W1456's constructed W949 data keeps the endpoint strict-exact witnesses. -/
theorem w1456EndpointLocalizedUnitDataKeepsEndpointStrictExact
    (input :
      W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456) :
    endpointStrictExactOfEndpointLocalizedUnitDataW949
        (endpointLocalizedUnitDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
          input) =
      input.endpointStrictExact :=
  rfl

/-- W1456's constructed W949 data keeps the W945 localized-unit data. -/
theorem w1456EndpointLocalizedUnitDataKeepsLocalizedUnitData
    (input :
      W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456) :
    localizedUnitDataOfEndpointLocalizedUnitDataW949
        (endpointLocalizedUnitDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
          input) =
      input.localizedUnitData :=
  rfl

/-- W1456's constructed W950 data keeps the constructed W948 data. -/
theorem w1456NormalizedEndpointDataKeepsConstructedNormalizedSourceData
    (input :
      W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456) :
    normalizedSourceTriangulationDataOfNormalizedSourceEndpointLocalizedUnitDataW950
        (normalizedSourceEndpointLocalizedUnitDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
          input) =
      normalizedSourceTriangulationDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
        input :=
  rfl

/-- W1456's constructed W950 data keeps the constructed W949 data. -/
theorem w1456NormalizedEndpointDataKeepsConstructedEndpointLocalizedUnitData
    (input :
      W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456) :
    endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitDataW950
        (normalizedSourceEndpointLocalizedUnitDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
          input) =
      endpointLocalizedUnitDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
        input :=
  rfl

/-- W1456's W1455 input keeps the raw right-open boundary field. -/
theorem w1456InputKeepsRightOpenBoundary
    (input :
      W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456) :
    (w1455InputOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
        input).rightOpenBoundary =
      input.rightOpenBoundary :=
  rfl

/-- W1456's W1455 input keeps the raw source-pi-zero boundary field. -/
theorem w1456InputKeepsSourcePiZeroBoundary
    (input :
      W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456) :
    (w1455InputOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
        input).sourcePiZeroBoundary =
      input.sourcePiZeroBoundary :=
  rfl

/-- W1456's W1455 input keeps the raw relation-pullback field. -/
theorem w1456InputKeepsRelationPullbackProvider
    (input :
      W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456) :
    (w1455InputOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
        input).relationPullbackProvider =
      input.relationPullbackProvider :=
  rfl

/-- W1456's W1455 input keeps the raw target-relation-lifts field. -/
theorem w1456InputKeepsTargetRelationLiftsProvider
    (input :
      W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456) :
    (w1455InputOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
        input).targetRelationLiftsProvider =
      input.targetRelationLiftsProvider :=
  rfl

/-- W1456's W1455 input keeps the W944 target no-univ provider. -/
theorem w1456InputKeepsTargetNoUnivData
    (input :
      W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456) :
    (w1455InputOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
        input).targetNoUnivData =
      input.targetNoUnivData :=
  rfl

/-- W1456's W1455 input keeps the W973 closedness provider. -/
theorem w1456InputKeepsClosedEmbeddingClosednessData
    (input :
      W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456) :
    (w1455InputOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
        input).closedEmbeddingClosednessData =
      input.closedEmbeddingClosednessData :=
  rfl

/-- W1456's W1455 input keeps the constructed W948 normalized-source data. -/
theorem w1456InputKeepsConstructedNormalizedSourceData
    (input :
      W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456) :
    (w1455InputOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
        input).normalizedSourceTriangulationData =
      normalizedSourceTriangulationDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
        input :=
  rfl

/-- W1456's W1455 input keeps the endpoint strict-exact witnesses. -/
theorem w1456InputKeepsEndpointStrictExact
    (input :
      W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456) :
    (w1455InputOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
        input).endpointStrictExact =
      input.endpointStrictExact :=
  rfl

/-- W1456's W1455 input keeps the W945 localized-unit data. -/
theorem w1456InputKeepsLocalizedUnitData
    (input :
      W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456) :
    (w1455InputOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
        input).localizedUnitData =
      input.localizedUnitData :=
  rfl

/-- W1456's W730 construction keeps the constructed W716 boundary data. -/
theorem w1456BoundaryRelationKeepsConstructedBoundaryData
    (input :
      W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456) :
    boundaryData_of_boundaryRelationDataW730
        (boundaryRelationDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
          input) =
      boundaryDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
        input :=
  rfl

/-- W1456's W730 construction keeps the constructed W717 relation data. -/
theorem w1456BoundaryRelationKeepsConstructedRelationData
    (input :
      W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456) :
    relationData_of_boundaryRelationDataW730
        (boundaryRelationDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
          input) =
      relationDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
        input :=
  rfl

/-- W1456's W986 construction keeps the constructed W984 target/closedness data. -/
theorem w1456TargetNormalizedEndpointKeepsConstructedTargetClosedness
    (input :
      W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456) :
    targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
        (targetNormalizedEndpointDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
          input) =
      targetClosedEmbeddingClosednessDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
        input :=
  rfl

/-- W1456's W986 construction keeps the constructed W950 normalized-endpoint data. -/
theorem w1456TargetNormalizedEndpointKeepsConstructedNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456) :
    normalizedSourceEndpointLocalizedUnitDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
        (targetNormalizedEndpointDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
          input) =
      normalizedSourceEndpointLocalizedUnitDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
        input :=
  rfl

/-- W1456's W987 provider projects to the constructed W730 data. -/
theorem w1456FullDataKeepsConstructedBoundaryRelation
    (input :
      W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456) :
    boundaryRelationDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
          input) =
      boundaryRelationDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
        input :=
  rfl

/-- W1456's W987 provider projects to the constructed W986 target/endpoint data. -/
theorem w1456FullDataKeepsConstructedTargetNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
          input) =
      targetNormalizedEndpointDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456
        input :=
  rfl

def w987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputNamesW1456 :
    List String :=
  ["raw right-open closed-quotient-cover WPP-limit boundary field",
    "raw source-difference cokernel-pi-zero WPP-limit boundary field",
    "raw closed-natural-transformation relation-pullback provider",
    "raw closed-natural-transformation target-relation-lifts provider",
    "W944 target no-univ data",
    "W973 closed-embedding closedness data",
    "W719 normalized fixed-target data",
    "W722 source-triangulation data",
    "endpoint strict short-exact witnesses",
    "W945 localized-unit data"]

theorem w987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputNamesW1456_count :
    w987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputNamesW1456.length =
      10 :=
  rfl

def w987BoundaryRelationTargetNormalizedSourceFieldDataConstructionBundledNormalizedSourceInputNamesW1456 :
    List String :=
  ["W948 normalized-source-triangulation data"]

theorem w987BoundaryRelationTargetNormalizedSourceFieldDataConstructionBundledNormalizedSourceInputNamesW1456_count :
    w987BoundaryRelationTargetNormalizedSourceFieldDataConstructionBundledNormalizedSourceInputNamesW1456.length =
      1 :=
  rfl

def w987BoundaryRelationTargetNormalizedSourceFieldDataConstructionNormalizedSourceInputNamesW1456 :
    List String :=
  ["W719 normalized fixed-target data", "W722 source-triangulation data"]

theorem w987BoundaryRelationTargetNormalizedSourceFieldDataConstructionNormalizedSourceInputNamesW1456_count :
    w987BoundaryRelationTargetNormalizedSourceFieldDataConstructionNormalizedSourceInputNamesW1456.length =
      2 :=
  rfl

/-- W1456 splits W1455's one W948 normalized-source input into two fields. -/
theorem w1456BoundaryRelationTargetNormalizedSourceFieldDataConstructionSplitsW948Input :
    w987BoundaryRelationTargetNormalizedSourceFieldDataConstructionBundledNormalizedSourceInputNamesW1456.length <
      w987BoundaryRelationTargetNormalizedSourceFieldDataConstructionNormalizedSourceInputNamesW1456.length := by
  rw [
    w987BoundaryRelationTargetNormalizedSourceFieldDataConstructionBundledNormalizedSourceInputNamesW1456_count,
    w987BoundaryRelationTargetNormalizedSourceFieldDataConstructionNormalizedSourceInputNamesW1456_count]
  norm_num

/-- W1456 replaces the nine W1455 inputs by ten named construction inputs. -/
theorem w1456BoundaryRelationTargetNormalizedSourceFieldDataConstructionExpandsW1455InputCount :
    w987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputNamesW1455.length <
      w987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputNamesW1456.length := by
  rw [w987BoundaryRelationTargetEndpointLocalizedUnitFieldDataConstructionInputNamesW1455_count,
    w987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputNamesW1456_count]
  norm_num

/-- Current W1456 nonterminal normalized-source construction state. -/
structure W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionStateW1456 :
    Type where
  seed : String
  declarations : List String
  constructionResult : String
  projectionResult : String
  normalizedSourceInputNames : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1456 records the W719/W722 construction path into W1455. -/
def currentW987BoundaryRelationTargetNormalizedSourceFieldDataConstructionStateW1456 :
    W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionStateW1456 where
  seed :=
    "w1456-w987-boundary-relation-target-normalized-source-field-data-construction"
  declarations :=
    ["W987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputW1456",
      "normalizedSourceTriangulationDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456",
      "w1455InputOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456",
      "endpointLocalizedUnitDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456",
      "normalizedSourceEndpointLocalizedUnitDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456",
      "targetClosedEmbeddingClosednessDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456",
      "relationDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456",
      "boundaryDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456",
      "boundaryRelationDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456",
      "targetNormalizedEndpointDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456",
      "fullDataOfW987BoundaryRelationTargetNormalizedSourceFieldDataW1456",
      "w1456NormalizedSourceDataKeepsNormalizedFixedTargetData",
      "w1456NormalizedSourceDataKeepsSourceTriangulationData",
      "w1456EndpointLocalizedUnitDataKeepsEndpointStrictExact",
      "w1456EndpointLocalizedUnitDataKeepsLocalizedUnitData",
      "w1456NormalizedEndpointDataKeepsConstructedNormalizedSourceData",
      "w1456NormalizedEndpointDataKeepsConstructedEndpointLocalizedUnitData",
      "w1456InputKeepsRightOpenBoundary",
      "w1456InputKeepsSourcePiZeroBoundary",
      "w1456InputKeepsRelationPullbackProvider",
      "w1456InputKeepsTargetRelationLiftsProvider",
      "w1456InputKeepsTargetNoUnivData",
      "w1456InputKeepsClosedEmbeddingClosednessData",
      "w1456InputKeepsConstructedNormalizedSourceData",
      "w1456InputKeepsEndpointStrictExact",
      "w1456InputKeepsLocalizedUnitData",
      "w1456BoundaryRelationKeepsConstructedBoundaryData",
      "w1456BoundaryRelationKeepsConstructedRelationData",
      "w1456TargetNormalizedEndpointKeepsConstructedTargetClosedness",
      "w1456TargetNormalizedEndpointKeepsConstructedNormalizedEndpoint",
      "w1456FullDataKeepsConstructedBoundaryRelation",
      "w1456FullDataKeepsConstructedTargetNormalizedEndpoint",
      "w987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputNamesW1456_count",
      "w1456BoundaryRelationTargetNormalizedSourceFieldDataConstructionSplitsW948Input",
      "w1456BoundaryRelationTargetNormalizedSourceFieldDataConstructionExpandsW1455InputCount"]
  constructionResult :=
    "proved: W948 normalized-source-triangulation data can be assembled from\
      W719 normalized fixed-target data and W722 source-triangulation data\
      before running W1455's W987 construction"
  projectionResult :=
    "proved: the constructed W948, W949, W950, W730, W986, and W987 providers\
      project back to the W1456 normalized-source fields, endpoint fields,\
      target fields, relation fields, and boundary fields"
  normalizedSourceInputNames :=
    w987BoundaryRelationTargetNormalizedSourceFieldDataConstructionNormalizedSourceInputNamesW1456
  remainingInputs :=
    w987BoundaryRelationTargetNormalizedSourceFieldDataConstructionInputNamesW1456
  productSuccessClaimed := false

theorem currentW1456W987BoundaryRelationTargetNormalizedSourceFieldDataConstruction_productSuccess :
    currentW987BoundaryRelationTargetNormalizedSourceFieldDataConstructionStateW1456.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
