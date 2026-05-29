import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW977LeafExpansionGuardW1263
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataRoute

/-!
W1264 records the direct W981-to-W977 payload construction. It replaces the
single W977 payload assumption by the existing W981 endpoint/unit strict-exact
data surface, which still has seven explicit inputs.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

/-- W1264 constructs the W977 current full-data payload from W981 data. -/
def currentFullDataPayloadOfUnitStrictExactIsoDataW1264
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  fullDataOfEndpointStrictExactW980
    (fullDataOfUnitStrictExactIsoW981 data)

/-- W1264 wraps the W981-built W977 payload as the W1008 current-full-data provider. -/
def currentFullDataProviderOfUnitStrictExactIsoDataW1264
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008
    where
  currentFullData := currentFullDataPayloadOfUnitStrictExactIsoDataW1264 data

def currentFullDataPayloadFromUnitStrictExactIsoDataInputNamesW1264 : List String :=
  endpointUnitStrictExactLocalizedUnitFullDataInputNamesW981

theorem currentFullDataPayloadFromUnitStrictExactIsoDataInputNamesW1264_count :
    currentFullDataPayloadFromUnitStrictExactIsoDataInputNamesW1264.length = 7 :=
  endpointUnitStrictExactLocalizedUnitFullDataInputNamesW981_count

theorem currentFullDataPayloadFromUnitStrictExactIsoDataExpandsW1264 :
    currentFullDataPayloadInputNamesW1262.length <
      currentFullDataPayloadFromUnitStrictExactIsoDataInputNamesW1264.length := by
  rw [currentFullDataPayloadInputNamesW1262_count,
    currentFullDataPayloadFromUnitStrictExactIsoDataInputNamesW1264_count]
  decide

structure MetrizableCurrentFullDataPayloadFromUnitStrictExactIsoDataStateW1264 :
    Type where
  seed : String
  declarations : List String
  payloadConstructionResult : String
  inputComparisonResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableCurrentFullDataPayloadFromUnitStrictExactIsoDataStateW1264 :
    MetrizableCurrentFullDataPayloadFromUnitStrictExactIsoDataStateW1264
    where
  seed := "w1264-current-full-data-payload-from-unit-strict-exact-iso-data"
  declarations :=
    ["currentFullDataPayloadOfUnitStrictExactIsoDataW1264",
      "currentFullDataProviderOfUnitStrictExactIsoDataW1264",
      "currentFullDataPayloadFromUnitStrictExactIsoDataInputNamesW1264",
      "currentFullDataPayloadFromUnitStrictExactIsoDataInputNamesW1264_count",
      "currentFullDataPayloadFromUnitStrictExactIsoDataExpandsW1264"]
  payloadConstructionResult :=
    "proved: W1264 constructs the W977 current full-data payload from the\
      existing W981 endpoint/unit strict-exact data route through W980"
  inputComparisonResult :=
    "proved: replacing the single W977 payload input by W981 exposes seven\
      explicit inputs, so this is a construction bridge rather than a\
      completion witness"
  remainingInputs := currentFullDataPayloadFromUnitStrictExactIsoDataInputNamesW1264
  productSuccessClaimed := false

theorem currentW1264CurrentFullDataPayloadFromUnitStrictExactIsoData_productSuccess :
    (let state :=
        currentMetrizableCurrentFullDataPayloadFromUnitStrictExactIsoDataStateW1264;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
