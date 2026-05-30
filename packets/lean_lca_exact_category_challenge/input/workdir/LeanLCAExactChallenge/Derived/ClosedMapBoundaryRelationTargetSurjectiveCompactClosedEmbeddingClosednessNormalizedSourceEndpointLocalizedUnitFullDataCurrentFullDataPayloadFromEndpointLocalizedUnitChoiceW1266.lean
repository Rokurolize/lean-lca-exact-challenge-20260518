import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataCurrentFullDataPayloadFromLocalizedUnitChoiceW1265
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitChoiceDataRoute

/-!
W1266 composes the W983 endpoint-localized-unit route with W1265. This
replaces W1265's six-input localized-unit-choice surface by W983's five-input
endpoint-localized-unit surface.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

/-- W1266 constructs the W977 current full-data payload from W983 data. -/
noncomputable def currentFullDataPayloadOfEndpointLocalizedUnitChoiceW1266
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitChoiceDataProviderW983) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataPayloadOfLocalizedUnitChoiceW1265
    (fullDataOfEndpointLocalizedUnitChoiceW983 data)

/-- W1266 wraps the W983-built W977 payload as the W1008 current-full-data provider. -/
noncomputable def currentFullDataProviderOfEndpointLocalizedUnitChoiceW1266
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitChoiceDataProviderW983) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008
    where
  currentFullData := currentFullDataPayloadOfEndpointLocalizedUnitChoiceW1266 data

def currentFullDataPayloadFromEndpointLocalizedUnitChoiceInputNamesW1266 : List String :=
  endpointLocalizedUnitChoiceFullDataInputNamesW983

theorem currentFullDataPayloadFromEndpointLocalizedUnitChoiceInputNamesW1266_count :
    currentFullDataPayloadFromEndpointLocalizedUnitChoiceInputNamesW1266.length = 5 :=
  endpointLocalizedUnitChoiceFullDataInputNamesW983_count

theorem currentFullDataPayloadFromEndpointLocalizedUnitChoiceReducesW1266 :
    currentFullDataPayloadFromEndpointLocalizedUnitChoiceInputNamesW1266.length <
      currentFullDataPayloadFromLocalizedUnitChoiceInputNamesW1265.length := by
  rw [currentFullDataPayloadFromEndpointLocalizedUnitChoiceInputNamesW1266_count,
    currentFullDataPayloadFromLocalizedUnitChoiceInputNamesW1265_count]
  decide

structure MetrizableCurrentFullDataPayloadFromEndpointLocalizedUnitChoiceStateW1266 :
    Type where
  seed : String
  declarations : List String
  payloadConstructionResult : String
  inputComparisonResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableCurrentFullDataPayloadFromEndpointLocalizedUnitChoiceStateW1266 :
    MetrizableCurrentFullDataPayloadFromEndpointLocalizedUnitChoiceStateW1266
    where
  seed := "w1266-current-full-data-payload-from-endpoint-localized-unit-choice"
  declarations :=
    ["currentFullDataPayloadOfEndpointLocalizedUnitChoiceW1266",
      "currentFullDataProviderOfEndpointLocalizedUnitChoiceW1266",
      "currentFullDataPayloadFromEndpointLocalizedUnitChoiceInputNamesW1266",
      "currentFullDataPayloadFromEndpointLocalizedUnitChoiceInputNamesW1266_count",
      "currentFullDataPayloadFromEndpointLocalizedUnitChoiceReducesW1266"]
  payloadConstructionResult :=
    "proved: W1266 constructs the W977 current full-data payload from the\
      existing W983 endpoint-localized-unit route through W1265"
  inputComparisonResult :=
    "proved: W1266 reduces the W1265 W982 replacement surface from six\
      explicit inputs to the W983 five-input endpoint-localized-unit surface"
  remainingInputs := currentFullDataPayloadFromEndpointLocalizedUnitChoiceInputNamesW1266
  productSuccessClaimed := false

theorem currentW1266CurrentFullDataPayloadFromEndpointLocalizedUnitChoice_productSuccess :
    (let state :=
        currentMetrizableCurrentFullDataPayloadFromEndpointLocalizedUnitChoiceStateW1266;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
