import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987FieldDataConstructionGuardW1450
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryFieldsComponentFieldsMappedCokernelFieldTargetDataEndpointFactsRoute

/-!
W1451 refines W1450 by constructing its W716 boundary-data input from the two
raw boundary fields already used by W907, then runs the resulting data through
the W1450 W987 field-data construction.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

/-- W1451 replaces the W1450 W716 boundary-data input by two raw boundary fields. -/
structure W987BoundaryFieldDataConstructionInputW1451 : Type 2 where
  rightOpenBoundary :
    Dbounded.MetrizableWppLimitRightOpenClosedQuotientCoverBoundary
  sourcePiZeroBoundary :
    Dbounded.MetrizableWppLimitSourceDifferenceCokernelPiZeroBoundary
  relationData :
    ClosedNatTransOrdinaryRelationDataProviderW717
  targetClosedEmbeddingClosednessData :
    TargetNoUnivClosedEmbeddingClosednessDataProviderW984
  normalizedSourceEndpointLocalizedUnitData :
    NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950

/-- W1451 builds W716 boundary data from the two raw boundary fields. -/
def boundaryDataOfW987BoundaryFieldDataW1451
    (input : W987BoundaryFieldDataConstructionInputW1451) :
    MetrizableWppLimitBoundaryDataW716 :=
  boundaryDataOfFieldsW907 input.rightOpenBoundary input.sourcePiZeroBoundary

/-- W1451 builds the W1450 input after constructing W716 boundary data. -/
def w1450InputOfW987BoundaryFieldDataW1451
    (input : W987BoundaryFieldDataConstructionInputW1451) :
    W987FieldDataConstructionInputW1450 where
  boundaryData := boundaryDataOfW987BoundaryFieldDataW1451 input
  relationData := input.relationData
  targetClosedEmbeddingClosednessData :=
    input.targetClosedEmbeddingClosednessData
  normalizedSourceEndpointLocalizedUnitData :=
    input.normalizedSourceEndpointLocalizedUnitData

/-- W1451 builds W730 boundary/relation data through W1450. -/
def boundaryRelationDataOfW987BoundaryFieldDataW1451
    (input : W987BoundaryFieldDataConstructionInputW1451) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfW987FieldDataW1450
    (w1450InputOfW987BoundaryFieldDataW1451 input)

/-- W1451 builds W986 target/endpoint data through W1450. -/
def targetNormalizedEndpointDataOfW987BoundaryFieldDataW1451
    (input : W987BoundaryFieldDataConstructionInputW1451) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetNormalizedEndpointDataOfW987FieldDataW1450
    (w1450InputOfW987BoundaryFieldDataW1451 input)

/-- W1451 builds the remaining W987 full-data provider through W1450. -/
noncomputable def fullDataOfW987BoundaryFieldDataW1451
    (input : W987BoundaryFieldDataConstructionInputW1451) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfW987FieldDataW1450
    (w1450InputOfW987BoundaryFieldDataW1451 input)

/-- W1451's constructed W716 data keeps the raw right-open boundary field. -/
theorem w1451BoundaryDataKeepsRightOpenBoundary
    (input : W987BoundaryFieldDataConstructionInputW1451) :
    (boundaryDataOfW987BoundaryFieldDataW1451 input).rightOpenBoundary =
      input.rightOpenBoundary :=
  rfl

/-- W1451's constructed W716 data keeps the raw source-pi-zero boundary field. -/
theorem w1451BoundaryDataKeepsSourcePiZeroBoundary
    (input : W987BoundaryFieldDataConstructionInputW1451) :
    (boundaryDataOfW987BoundaryFieldDataW1451 input).sourcePiZeroBoundary =
      input.sourcePiZeroBoundary :=
  rfl

/-- W1451's W1450 input keeps the constructed W716 boundary data. -/
theorem w1451InputKeepsConstructedBoundaryData
    (input : W987BoundaryFieldDataConstructionInputW1451) :
    (w1450InputOfW987BoundaryFieldDataW1451 input).boundaryData =
      boundaryDataOfW987BoundaryFieldDataW1451 input :=
  rfl

/-- W1451's W1450 input keeps the original W717 relation data. -/
theorem w1451InputKeepsRelationData
    (input : W987BoundaryFieldDataConstructionInputW1451) :
    (w1450InputOfW987BoundaryFieldDataW1451 input).relationData =
      input.relationData :=
  rfl

/-- W1451's W1450 input keeps the original W984 target/closedness data. -/
theorem w1451InputKeepsTargetClosednessData
    (input : W987BoundaryFieldDataConstructionInputW1451) :
    (w1450InputOfW987BoundaryFieldDataW1451
        input).targetClosedEmbeddingClosednessData =
      input.targetClosedEmbeddingClosednessData :=
  rfl

/-- W1451's W1450 input keeps the original W950 normalized-endpoint data. -/
theorem w1451InputKeepsNormalizedEndpointData
    (input : W987BoundaryFieldDataConstructionInputW1451) :
    (w1450InputOfW987BoundaryFieldDataW1451
        input).normalizedSourceEndpointLocalizedUnitData =
      input.normalizedSourceEndpointLocalizedUnitData :=
  rfl

/-- W1451's W730 construction keeps the constructed W716 boundary data. -/
theorem w1451BoundaryRelationKeepsConstructedBoundaryData
    (input : W987BoundaryFieldDataConstructionInputW1451) :
    boundaryData_of_boundaryRelationDataW730
        (boundaryRelationDataOfW987BoundaryFieldDataW1451 input) =
      boundaryDataOfW987BoundaryFieldDataW1451 input :=
  rfl

/-- W1451's W730 construction keeps the W717 relation data. -/
theorem w1451BoundaryRelationKeepsRelationData
    (input : W987BoundaryFieldDataConstructionInputW1451) :
    relationData_of_boundaryRelationDataW730
        (boundaryRelationDataOfW987BoundaryFieldDataW1451 input) =
      input.relationData :=
  rfl

/-- W1451's W987 provider projects to the constructed W730 data. -/
theorem w1451FullDataKeepsConstructedBoundaryRelation
    (input : W987BoundaryFieldDataConstructionInputW1451) :
    boundaryRelationDataOfFullDataW987
        (fullDataOfW987BoundaryFieldDataW1451 input) =
      boundaryRelationDataOfW987BoundaryFieldDataW1451 input :=
  rfl

/-- W1451's W987 provider projects to the constructed W986 target/endpoint data. -/
theorem w1451FullDataKeepsConstructedTargetNormalizedEndpoint
    (input : W987BoundaryFieldDataConstructionInputW1451) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (fullDataOfW987BoundaryFieldDataW1451 input) =
      targetNormalizedEndpointDataOfW987BoundaryFieldDataW1451 input :=
  rfl

def w987BoundaryFieldDataConstructionInputNamesW1451 : List String :=
  ["raw right-open closed-quotient-cover WPP-limit boundary field",
    "raw source-difference cokernel-pi-zero WPP-limit boundary field",
    "W717 closed natural-transformation relation data",
    "W984 target/closed-embedding closedness data",
    "W950 normalized-source/endpoint-localized-unit data"]

theorem w987BoundaryFieldDataConstructionInputNamesW1451_count :
    w987BoundaryFieldDataConstructionInputNamesW1451.length = 5 :=
  rfl

def w987BoundaryFieldDataConstructionBundledBoundaryInputNamesW1451 :
    List String :=
  ["W716 WPP-limit boundary data"]

theorem w987BoundaryFieldDataConstructionBundledBoundaryInputNamesW1451_count :
    w987BoundaryFieldDataConstructionBundledBoundaryInputNamesW1451.length = 1 :=
  rfl

def w987BoundaryFieldDataConstructionBoundaryInputNamesW1451 :
    List String :=
  ["raw right-open closed-quotient-cover WPP-limit boundary field",
    "raw source-difference cokernel-pi-zero WPP-limit boundary field"]

theorem w987BoundaryFieldDataConstructionBoundaryInputNamesW1451_count :
    w987BoundaryFieldDataConstructionBoundaryInputNamesW1451.length = 2 :=
  rfl

/-- W1451 splits W1450's one W716 boundary-data input into two raw fields. -/
theorem w1451BoundaryFieldDataConstructionSplitsW716Input :
    w987BoundaryFieldDataConstructionBundledBoundaryInputNamesW1451.length <
      w987BoundaryFieldDataConstructionBoundaryInputNamesW1451.length := by
  rw [w987BoundaryFieldDataConstructionBundledBoundaryInputNamesW1451_count,
    w987BoundaryFieldDataConstructionBoundaryInputNamesW1451_count]
  norm_num

/-- W1451 replaces the four W1450 inputs by five named construction inputs. -/
theorem w1451BoundaryFieldDataConstructionExpandsW1450InputCount :
    w987FieldDataConstructionInputNamesW1450.length <
      w987BoundaryFieldDataConstructionInputNamesW1451.length := by
  rw [w987FieldDataConstructionInputNamesW1450_count,
    w987BoundaryFieldDataConstructionInputNamesW1451_count]
  norm_num

/-- Current W1451 nonterminal boundary-field construction state. -/
structure W987BoundaryFieldDataConstructionStateW1451 : Type where
  seed : String
  declarations : List String
  constructionResult : String
  projectionResult : String
  boundaryInputNames : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1451 records the raw-boundary-field construction path into W1450. -/
def currentW987BoundaryFieldDataConstructionStateW1451 :
    W987BoundaryFieldDataConstructionStateW1451 where
  seed := "w1451-w987-boundary-field-data-construction"
  declarations :=
    ["W987BoundaryFieldDataConstructionInputW1451",
      "boundaryDataOfW987BoundaryFieldDataW1451",
      "w1450InputOfW987BoundaryFieldDataW1451",
      "boundaryRelationDataOfW987BoundaryFieldDataW1451",
      "targetNormalizedEndpointDataOfW987BoundaryFieldDataW1451",
      "fullDataOfW987BoundaryFieldDataW1451",
      "w1451BoundaryDataKeepsRightOpenBoundary",
      "w1451BoundaryDataKeepsSourcePiZeroBoundary",
      "w1451InputKeepsConstructedBoundaryData",
      "w1451InputKeepsRelationData",
      "w1451InputKeepsTargetClosednessData",
      "w1451InputKeepsNormalizedEndpointData",
      "w1451BoundaryRelationKeepsConstructedBoundaryData",
      "w1451BoundaryRelationKeepsRelationData",
      "w1451FullDataKeepsConstructedBoundaryRelation",
      "w1451FullDataKeepsConstructedTargetNormalizedEndpoint",
      "w987BoundaryFieldDataConstructionInputNamesW1451_count",
      "w1451BoundaryFieldDataConstructionSplitsW716Input",
      "w1451BoundaryFieldDataConstructionExpandsW1450InputCount"]
  constructionResult :=
    "proved: W716 boundary data can be assembled from raw right-open and\
      source-pi-zero boundary fields before running W1450's W987 construction"
  projectionResult :=
    "proved: the constructed W716, W730, W986, and W987 providers project back\
      to the W1451 boundary fields and carried W717/W984/W950 data"
  boundaryInputNames :=
    w987BoundaryFieldDataConstructionBoundaryInputNamesW1451
  remainingInputs := w987BoundaryFieldDataConstructionInputNamesW1451
  productSuccessClaimed := false

theorem currentW1451W987BoundaryFieldDataConstruction_productSuccess :
    currentW987BoundaryFieldDataConstructionStateW1451.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
