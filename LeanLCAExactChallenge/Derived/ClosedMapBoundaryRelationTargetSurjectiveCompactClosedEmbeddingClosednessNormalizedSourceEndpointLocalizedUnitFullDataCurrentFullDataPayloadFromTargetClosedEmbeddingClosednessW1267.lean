import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataCurrentFullDataPayloadFromEndpointLocalizedUnitChoiceW1266
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessEndpointLocalizedUnitChoiceDataRoute

/-!
W1267 composes the W984 target/closed-embedding-closedness route with W1266.
This replaces W1266's five-input endpoint-localized-unit surface by W984's
four-input target/closedness endpoint-localized-unit surface.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

/-- W1267 constructs the W977 current full-data payload from W984 data. -/
noncomputable def currentFullDataPayloadOfTargetClosedEmbeddingClosednessW1267
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessEndpointLocalizedUnitChoiceDataProviderW984) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataPayloadOfEndpointLocalizedUnitChoiceW1266
    (fullDataOfTargetClosedEmbeddingClosednessW984 data)

/-- W1267 wraps the W984-built W977 payload as the W1008 current-full-data provider. -/
noncomputable def currentFullDataProviderOfTargetClosedEmbeddingClosednessW1267
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessEndpointLocalizedUnitChoiceDataProviderW984) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008
    where
  currentFullData := currentFullDataPayloadOfTargetClosedEmbeddingClosednessW1267 data

def currentFullDataPayloadFromTargetClosedEmbeddingClosednessInputNamesW1267 :
    List String :=
  targetClosedEmbeddingClosednessEndpointLocalizedUnitChoiceFullDataInputNamesW984

theorem currentFullDataPayloadFromTargetClosedEmbeddingClosednessInputNamesW1267_count :
    currentFullDataPayloadFromTargetClosedEmbeddingClosednessInputNamesW1267.length =
      4 :=
  targetClosedEmbeddingClosednessEndpointLocalizedUnitChoiceFullDataInputNamesW984_count

theorem currentFullDataPayloadFromTargetClosedEmbeddingClosednessReducesW1267 :
    currentFullDataPayloadFromTargetClosedEmbeddingClosednessInputNamesW1267.length <
      currentFullDataPayloadFromEndpointLocalizedUnitChoiceInputNamesW1266.length := by
  rw [currentFullDataPayloadFromTargetClosedEmbeddingClosednessInputNamesW1267_count,
    currentFullDataPayloadFromEndpointLocalizedUnitChoiceInputNamesW1266_count]
  decide

structure MetrizableCurrentFullDataPayloadFromTargetClosedEmbeddingClosednessStateW1267 :
    Type where
  seed : String
  declarations : List String
  payloadConstructionResult : String
  inputComparisonResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableCurrentFullDataPayloadFromTargetClosedEmbeddingClosednessStateW1267 :
    MetrizableCurrentFullDataPayloadFromTargetClosedEmbeddingClosednessStateW1267
    where
  seed := "w1267-current-full-data-payload-from-target-closed-embedding-closedness"
  declarations :=
    ["currentFullDataPayloadOfTargetClosedEmbeddingClosednessW1267",
      "currentFullDataProviderOfTargetClosedEmbeddingClosednessW1267",
      "currentFullDataPayloadFromTargetClosedEmbeddingClosednessInputNamesW1267",
      "currentFullDataPayloadFromTargetClosedEmbeddingClosednessInputNamesW1267_count",
      "currentFullDataPayloadFromTargetClosedEmbeddingClosednessReducesW1267"]
  payloadConstructionResult :=
    "proved: W1267 constructs the W977 current full-data payload from the\
      existing W984 target/closed-embedding-closedness route through W1266"
  inputComparisonResult :=
    "proved: W1267 reduces the W1266 W983 replacement surface from five\
      explicit inputs to the W984 four-input target/closedness surface"
  remainingInputs :=
    currentFullDataPayloadFromTargetClosedEmbeddingClosednessInputNamesW1267
  productSuccessClaimed := false

theorem currentW1267CurrentFullDataPayloadFromTargetClosedEmbeddingClosedness_productSuccess :
    (let state :=
        currentMetrizableCurrentFullDataPayloadFromTargetClosedEmbeddingClosednessStateW1267;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
