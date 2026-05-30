import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosedMapBranchFullDataW987RewrappedStableRouteGuardW1449

/-!
W1450 gives the remaining W987 provider a concrete construction surface. Instead
of reusing a W987 or W1007 wrapper, it builds W730 from W716 boundary data and
W717 relation data, builds W986 from W984 target/closedness data and W950
normalized-source/endpoint data, and then assembles the W987 full-data provider.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

/-- W1450 field data for constructing the remaining W987 full-data provider. -/
structure W987FieldDataConstructionInputW1450 : Type 2 where
  boundaryData :
    MetrizableWppLimitBoundaryDataW716
  relationData :
    ClosedNatTransOrdinaryRelationDataProviderW717
  targetClosedEmbeddingClosednessData :
    TargetNoUnivClosedEmbeddingClosednessDataProviderW984
  normalizedSourceEndpointLocalizedUnitData :
    NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950

/-- W1450 builds W730 boundary/relation data from W716 and W717 data. -/
def boundaryRelationDataOfW987FieldDataW1450
    (input : W987FieldDataConstructionInputW1450) :
    MetrizableWppBoundaryRelationDataProviderW730
    where
  boundaryData := input.boundaryData
  relationData := input.relationData

/-- W1450 builds W986 target/normalized-endpoint data from W984 and W950 data. -/
def targetNormalizedEndpointDataOfW987FieldDataW1450
    (input : W987FieldDataConstructionInputW1450) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986
    where
  targetClosedEmbeddingClosednessData := input.targetClosedEmbeddingClosednessData
  normalizedSourceEndpointLocalizedUnitData :=
    input.normalizedSourceEndpointLocalizedUnitData

/-- W1450 builds the W986 full-data surface from field data. -/
noncomputable def w986FullDataOfW987FieldDataW1450
    (input : W987FieldDataConstructionInputW1450) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986
    where
  boundaryRelationData := boundaryRelationDataOfW987FieldDataW1450 input
  targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitData :=
    targetNormalizedEndpointDataOfW987FieldDataW1450 input

/-- W1450 builds the remaining W987 full-data provider from W716/W717/W984/W950 data. -/
noncomputable def fullDataOfW987FieldDataW1450
    (input : W987FieldDataConstructionInputW1450) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987
    where
  boundaryRelationData := boundaryRelationDataOfW987FieldDataW1450 input
  targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitData :=
    targetNormalizedEndpointDataOfW987FieldDataW1450 input

/-- W1450's W987 provider projects to the constructed W730 data. -/
theorem w1450FullDataKeepsConstructedBoundaryRelation
    (input : W987FieldDataConstructionInputW1450) :
    boundaryRelationDataOfFullDataW987
        (fullDataOfW987FieldDataW1450 input) =
      boundaryRelationDataOfW987FieldDataW1450 input :=
  rfl

/-- W1450's W987 provider projects to the constructed W986 target/endpoint data. -/
theorem w1450FullDataKeepsConstructedTargetNormalizedEndpoint
    (input : W987FieldDataConstructionInputW1450) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (fullDataOfW987FieldDataW1450 input) =
      targetNormalizedEndpointDataOfW987FieldDataW1450 input :=
  rfl

/-- W1450's W730 construction keeps the original W716 boundary data. -/
theorem w1450BoundaryRelationKeepsBoundaryData
    (input : W987FieldDataConstructionInputW1450) :
    boundaryData_of_boundaryRelationDataW730
        (boundaryRelationDataOfW987FieldDataW1450 input) =
      input.boundaryData :=
  rfl

/-- W1450's W730 construction keeps the original W717 relation data. -/
theorem w1450BoundaryRelationKeepsRelationData
    (input : W987FieldDataConstructionInputW1450) :
    relationData_of_boundaryRelationDataW730
        (boundaryRelationDataOfW987FieldDataW1450 input) =
      input.relationData :=
  rfl

/-- W1450's W986 construction keeps the original W984 target/closedness data. -/
theorem w1450TargetNormalizedEndpointKeepsTargetClosedness
    (input : W987FieldDataConstructionInputW1450) :
    targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
        (targetNormalizedEndpointDataOfW987FieldDataW1450 input) =
      input.targetClosedEmbeddingClosednessData :=
  rfl

/-- W1450's W986 construction keeps the original W950 normalized-endpoint data. -/
theorem w1450TargetNormalizedEndpointKeepsNormalizedEndpoint
    (input : W987FieldDataConstructionInputW1450) :
    normalizedSourceEndpointLocalizedUnitDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
        (targetNormalizedEndpointDataOfW987FieldDataW1450 input) =
      input.normalizedSourceEndpointLocalizedUnitData :=
  rfl

/-- W1450's W986 full-data construction keeps the constructed W730 data. -/
theorem w1450W986FullDataKeepsConstructedBoundaryRelation
    (input : W987FieldDataConstructionInputW1450) :
    (w986FullDataOfW987FieldDataW1450 input).boundaryRelationData =
      boundaryRelationDataOfW987FieldDataW1450 input :=
  rfl

/-- W1450's W986 full-data construction keeps the constructed W986 target/endpoint data. -/
theorem w1450W986FullDataKeepsConstructedTargetNormalizedEndpoint
    (input : W987FieldDataConstructionInputW1450) :
    (w986FullDataOfW987FieldDataW1450
        input).targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitData =
      targetNormalizedEndpointDataOfW987FieldDataW1450 input :=
  rfl

def w987FieldDataConstructionInputNamesW1450 : List String :=
  ["W716 WPP-limit boundary data",
    "W717 closed natural-transformation relation data",
    "W984 target/closed-embedding closedness data",
    "W950 normalized-source/endpoint-localized-unit data"]

theorem w987FieldDataConstructionInputNamesW1450_count :
    w987FieldDataConstructionInputNamesW1450.length = 4 :=
  rfl

/-- W1450 replaces the one W987 provider input by four named construction inputs. -/
theorem w1450W987FieldDataConstructionExpandsCurrentProvider :
    w1007W987RewrappedInputNamesW1448.length <
      w987FieldDataConstructionInputNamesW1450.length := by
  rw [w1007W987RewrappedInputNamesW1448_count,
    w987FieldDataConstructionInputNamesW1450_count]
  norm_num

/-- Current W1450 nonterminal W987 field-data construction state. -/
structure W987FieldDataConstructionStateW1450 : Type where
  seed : String
  declarations : List String
  constructionResult : String
  projectionResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1450 records the direct W716/W717/W984/W950 construction surface for W987. -/
def currentW987FieldDataConstructionStateW1450 :
    W987FieldDataConstructionStateW1450 where
  seed := "w1450-w987-field-data-construction"
  declarations :=
    ["W987FieldDataConstructionInputW1450",
      "boundaryRelationDataOfW987FieldDataW1450",
      "targetNormalizedEndpointDataOfW987FieldDataW1450",
      "w986FullDataOfW987FieldDataW1450",
      "fullDataOfW987FieldDataW1450",
      "w1450FullDataKeepsConstructedBoundaryRelation",
      "w1450FullDataKeepsConstructedTargetNormalizedEndpoint",
      "w1450BoundaryRelationKeepsBoundaryData",
      "w1450BoundaryRelationKeepsRelationData",
      "w1450TargetNormalizedEndpointKeepsTargetClosedness",
      "w1450TargetNormalizedEndpointKeepsNormalizedEndpoint",
      "w1450W986FullDataKeepsConstructedBoundaryRelation",
      "w1450W986FullDataKeepsConstructedTargetNormalizedEndpoint",
      "w987FieldDataConstructionInputNamesW1450_count",
      "w1450W987FieldDataConstructionExpandsCurrentProvider"]
  constructionResult :=
    "proved: W987 can be assembled directly from W716 boundary data, W717\
      relation data, W984 target/closedness data, and W950 normalized-endpoint\
      data without a W987 or W1007 wrapper"
  projectionResult :=
    "proved: the constructed W987 and W986 providers project back to exactly\
      those W716/W717/W984/W950 construction inputs"
  remainingInputs := w987FieldDataConstructionInputNamesW1450
  productSuccessClaimed := false

theorem currentW1450W987FieldDataConstruction_productSuccess :
    currentW987FieldDataConstructionStateW1450.productSuccessClaimed = false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
