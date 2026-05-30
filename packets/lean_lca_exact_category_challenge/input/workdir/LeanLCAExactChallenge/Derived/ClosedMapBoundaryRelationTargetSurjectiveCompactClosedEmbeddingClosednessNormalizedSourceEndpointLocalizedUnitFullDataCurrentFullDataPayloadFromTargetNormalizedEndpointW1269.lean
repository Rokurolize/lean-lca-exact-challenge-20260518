import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataCurrentFullDataPayloadFromNormalizedSourceEndpointLocalizedUnitW1268
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataRoute

/-!
W1269 composes the W986 target/closedness/normalized-source/endpoint route
with W1268. This replaces W1268's three-input surface by W986's two-input
target/normalized/endpoint surface.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

/-- W1269 constructs the W977 current full-data payload from W986 data. -/
noncomputable def currentFullDataPayloadOfTargetNormalizedEndpointW1269
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataPayloadOfNormalizedSourceEndpointLocalizedUnitW1268
    (fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
      data)

/-- W1269 wraps the W986-built W977 payload as the W1008 current-full-data provider. -/
noncomputable def currentFullDataProviderOfTargetNormalizedEndpointW1269
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008
    where
  currentFullData := currentFullDataPayloadOfTargetNormalizedEndpointW1269 data

def currentFullDataPayloadFromTargetNormalizedEndpointInputNamesW1269 :
    List String :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitInputNamesW986

theorem currentFullDataPayloadFromTargetNormalizedEndpointInputNamesW1269_count :
    currentFullDataPayloadFromTargetNormalizedEndpointInputNamesW1269.length =
      2 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitInputNamesW986_count

theorem currentFullDataPayloadFromTargetNormalizedEndpointReducesW1269 :
    currentFullDataPayloadFromTargetNormalizedEndpointInputNamesW1269.length <
      currentFullDataPayloadFromNormalizedSourceEndpointLocalizedUnitInputNamesW1268.length := by
  rw [currentFullDataPayloadFromTargetNormalizedEndpointInputNamesW1269_count,
    currentFullDataPayloadFromNormalizedSourceEndpointLocalizedUnitInputNamesW1268_count]
  decide

structure MetrizableCurrentFullDataPayloadFromTargetNormalizedEndpointStateW1269 :
    Type where
  seed : String
  declarations : List String
  payloadConstructionResult : String
  inputComparisonResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableCurrentFullDataPayloadFromTargetNormalizedEndpointStateW1269 :
    MetrizableCurrentFullDataPayloadFromTargetNormalizedEndpointStateW1269
    where
  seed := "w1269-current-full-data-payload-from-target-normalized-endpoint"
  declarations :=
    ["currentFullDataPayloadOfTargetNormalizedEndpointW1269",
      "currentFullDataProviderOfTargetNormalizedEndpointW1269",
      "currentFullDataPayloadFromTargetNormalizedEndpointInputNamesW1269",
      "currentFullDataPayloadFromTargetNormalizedEndpointInputNamesW1269_count",
      "currentFullDataPayloadFromTargetNormalizedEndpointReducesW1269"]
  payloadConstructionResult :=
    "proved: W1269 constructs the W977 current full-data payload from the\
      existing W986 target/closedness/normalized-source/endpoint route\
      through W1268"
  inputComparisonResult :=
    "proved: W1269 reduces the W1268 W985 replacement surface from three\
      explicit inputs to the W986 two-input target/normalized/endpoint surface"
  remainingInputs := currentFullDataPayloadFromTargetNormalizedEndpointInputNamesW1269
  productSuccessClaimed := false

theorem currentW1269CurrentFullDataPayloadFromTargetNormalizedEndpoint_productSuccess :
    (let state :=
        currentMetrizableCurrentFullDataPayloadFromTargetNormalizedEndpointStateW1269;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
