import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataCurrentFullDataPayloadFromUnitStrictExactIsoDataW1264
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataRoute

/-!
W1265 composes the W982 localized-unit-choice route with W1264. This replaces
the W981 endpoint/unit strict-exact data input surface by W982's six-input
localized-unit-choice surface.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

/-- W1265 constructs the W977 current full-data payload from W982 data. -/
noncomputable def currentFullDataPayloadOfLocalizedUnitChoiceW1265
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataPayloadOfUnitStrictExactIsoDataW1264
    (fullDataOfLocalizedUnitChoiceW982 data)

/-- W1265 wraps the W982-built W977 payload as the W1008 current-full-data provider. -/
noncomputable def currentFullDataProviderOfLocalizedUnitChoiceW1265
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008
    where
  currentFullData := currentFullDataPayloadOfLocalizedUnitChoiceW1265 data

def currentFullDataPayloadFromLocalizedUnitChoiceInputNamesW1265 : List String :=
  endpointStrictExactLocalizedUnitChoiceFullDataInputNamesW982

theorem currentFullDataPayloadFromLocalizedUnitChoiceInputNamesW1265_count :
    currentFullDataPayloadFromLocalizedUnitChoiceInputNamesW1265.length = 6 :=
  endpointStrictExactLocalizedUnitChoiceFullDataInputNamesW982_count

theorem currentFullDataPayloadFromLocalizedUnitChoiceReducesW1265 :
    currentFullDataPayloadFromLocalizedUnitChoiceInputNamesW1265.length <
      currentFullDataPayloadFromUnitStrictExactIsoDataInputNamesW1264.length := by
  rw [currentFullDataPayloadFromLocalizedUnitChoiceInputNamesW1265_count,
    currentFullDataPayloadFromUnitStrictExactIsoDataInputNamesW1264_count]
  decide

structure MetrizableCurrentFullDataPayloadFromLocalizedUnitChoiceStateW1265 :
    Type where
  seed : String
  declarations : List String
  payloadConstructionResult : String
  inputComparisonResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableCurrentFullDataPayloadFromLocalizedUnitChoiceStateW1265 :
    MetrizableCurrentFullDataPayloadFromLocalizedUnitChoiceStateW1265
    where
  seed := "w1265-current-full-data-payload-from-localized-unit-choice"
  declarations :=
    ["currentFullDataPayloadOfLocalizedUnitChoiceW1265",
      "currentFullDataProviderOfLocalizedUnitChoiceW1265",
      "currentFullDataPayloadFromLocalizedUnitChoiceInputNamesW1265",
      "currentFullDataPayloadFromLocalizedUnitChoiceInputNamesW1265_count",
      "currentFullDataPayloadFromLocalizedUnitChoiceReducesW1265"]
  payloadConstructionResult :=
    "proved: W1265 constructs the W977 current full-data payload from the\
      existing W982 localized-unit-choice route through W1264"
  inputComparisonResult :=
    "proved: W1265 reduces the W1264 W981 replacement surface from seven\
      explicit inputs to the W982 six-input localized-unit-choice surface"
  remainingInputs := currentFullDataPayloadFromLocalizedUnitChoiceInputNamesW1265
  productSuccessClaimed := false

theorem currentW1265CurrentFullDataPayloadFromLocalizedUnitChoice_productSuccess :
    (let state :=
        currentMetrizableCurrentFullDataPayloadFromLocalizedUnitChoiceStateW1265;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
