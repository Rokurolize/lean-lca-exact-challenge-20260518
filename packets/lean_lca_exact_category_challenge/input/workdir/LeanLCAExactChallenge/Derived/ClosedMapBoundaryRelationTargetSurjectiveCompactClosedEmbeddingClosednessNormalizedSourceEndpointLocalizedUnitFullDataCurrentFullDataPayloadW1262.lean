import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataCurrentFullDataCycleGuardW1261
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitFullDataRoute

/-!
W1262 makes the remaining W1261/W1008 input precise: W1008 is a one-field
wrapper around the W977 current full-data provider, and W977 is the real
payload that still has to be constructed without external input.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

/-- W1262 projects the W977 current full-data payload from the W1008 wrapper. -/
def currentFullDataPayloadOfCurrentFullDataW1262
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataInputOfCurrentFullDataW1008 data

def currentFullDataPayloadInputNamesW1262 : List String :=
  closedEmbeddingEndpointLocalizedUnitFullDataInputNamesW977

theorem currentFullDataPayloadInputNamesW1262_count :
    currentFullDataPayloadInputNamesW1262.length = 1 :=
  closedEmbeddingEndpointLocalizedUnitFullDataInputNamesW977_count

theorem currentFullDataPayloadMatchesW977InputCountW1262 :
    currentFullDataPayloadInputNamesW1262.length =
      closedEmbeddingEndpointLocalizedUnitFullDataInputNamesW977.length :=
  rfl

theorem currentFullDataPayloadMatchesW1261InputCountW1262 :
    currentFullDataPayloadInputNamesW1262.length =
      currentFullDataCycleGuardInputNamesW1261.length := by
  rw [currentFullDataPayloadInputNamesW1262_count,
    currentFullDataCycleGuardInputNamesW1261_count]

structure MetrizableCurrentFullDataPayloadStateW1262 : Type where
  seed : String
  declarations : List String
  payloadResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableCurrentFullDataPayloadStateW1262 :
    MetrizableCurrentFullDataPayloadStateW1262
    where
  seed := "w1262-current-full-data-payload"
  declarations :=
    ["currentFullDataPayloadOfCurrentFullDataW1262",
      "currentFullDataPayloadInputNamesW1262",
      "currentFullDataPayloadInputNamesW1262_count",
      "currentFullDataPayloadMatchesW977InputCountW1262",
      "currentFullDataPayloadMatchesW1261InputCountW1262"]
  payloadResult :=
    "proved: the remaining W1261/W1008 input is exactly the W977 current\
      full-data payload, whose route state records one current full-data\
      provider packaging seven provider leaves"
  remainingInputs := currentFullDataPayloadInputNamesW1262
  productSuccessClaimed := false

theorem currentW1262CurrentFullDataPayload_productSuccess :
    (let state := currentMetrizableCurrentFullDataPayloadStateW1262;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
