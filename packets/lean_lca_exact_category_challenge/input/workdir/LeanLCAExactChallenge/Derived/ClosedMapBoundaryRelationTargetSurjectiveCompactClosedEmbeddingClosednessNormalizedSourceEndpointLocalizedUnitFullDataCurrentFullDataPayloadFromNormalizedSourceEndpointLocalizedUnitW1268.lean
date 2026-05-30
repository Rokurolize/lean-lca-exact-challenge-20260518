import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataCurrentFullDataPayloadFromTargetClosedEmbeddingClosednessW1267
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitChoiceDataRoute

/-!
W1268 composes the W985 normalized-source/endpoint-localized-unit route with
W1267. This replaces W1267's four-input target/closedness surface by W985's
three-input normalized-source/endpoint-localized-unit surface.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

/-- W1268 constructs the W977 current full-data payload from W985 data. -/
noncomputable def currentFullDataPayloadOfNormalizedSourceEndpointLocalizedUnitW1268
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitChoiceDataProviderW985) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataPayloadOfTargetClosedEmbeddingClosednessW1267
    (fullDataOfNormalizedSourceEndpointLocalizedUnitW985 data)

/-- W1268 wraps the W985-built W977 payload as the W1008 current-full-data provider. -/
noncomputable def currentFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1268
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitChoiceDataProviderW985) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008
    where
  currentFullData := currentFullDataPayloadOfNormalizedSourceEndpointLocalizedUnitW1268 data

def currentFullDataPayloadFromNormalizedSourceEndpointLocalizedUnitInputNamesW1268 :
    List String :=
  normalizedSourceEndpointLocalizedUnitChoiceInputNamesW985

theorem currentFullDataPayloadFromNormalizedSourceEndpointLocalizedUnitInputNamesW1268_count :
    currentFullDataPayloadFromNormalizedSourceEndpointLocalizedUnitInputNamesW1268.length =
      3 :=
  normalizedSourceEndpointLocalizedUnitChoiceInputNamesW985_count

theorem currentFullDataPayloadFromNormalizedSourceEndpointLocalizedUnitReducesW1268 :
    currentFullDataPayloadFromNormalizedSourceEndpointLocalizedUnitInputNamesW1268.length <
      currentFullDataPayloadFromTargetClosedEmbeddingClosednessInputNamesW1267.length := by
  rw [currentFullDataPayloadFromNormalizedSourceEndpointLocalizedUnitInputNamesW1268_count,
    currentFullDataPayloadFromTargetClosedEmbeddingClosednessInputNamesW1267_count]
  decide

structure MetrizableCurrentFullDataPayloadFromNormalizedSourceEndpointLocalizedUnitStateW1268 :
    Type where
  seed : String
  declarations : List String
  payloadConstructionResult : String
  inputComparisonResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableCurrentFullDataPayloadFromNormalizedSourceEndpointLocalizedUnitStateW1268 :
    MetrizableCurrentFullDataPayloadFromNormalizedSourceEndpointLocalizedUnitStateW1268
    where
  seed := "w1268-current-full-data-payload-from-normalized-source-endpoint-localized-unit"
  declarations :=
    ["currentFullDataPayloadOfNormalizedSourceEndpointLocalizedUnitW1268",
      "currentFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1268",
      "currentFullDataPayloadFromNormalizedSourceEndpointLocalizedUnitInputNamesW1268",
      "currentFullDataPayloadFromNormalizedSourceEndpointLocalizedUnitInputNamesW1268_count",
      "currentFullDataPayloadFromNormalizedSourceEndpointLocalizedUnitReducesW1268"]
  payloadConstructionResult :=
    "proved: W1268 constructs the W977 current full-data payload from the\
      existing W985 normalized-source/endpoint-localized route through W1267"
  inputComparisonResult :=
    "proved: W1268 reduces the W1267 W984 replacement surface from four\
      explicit inputs to the W985 three-input normalized-source/endpoint surface"
  remainingInputs :=
    currentFullDataPayloadFromNormalizedSourceEndpointLocalizedUnitInputNamesW1268
  productSuccessClaimed := false

theorem currentW1268CurrentFullDataPayloadFromNormalizedSourceEndpointLocalizedUnit_productSuccess :
    (let state :=
        currentMetrizableCurrentFullDataPayloadFromNormalizedSourceEndpointLocalizedUnitStateW1268;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
