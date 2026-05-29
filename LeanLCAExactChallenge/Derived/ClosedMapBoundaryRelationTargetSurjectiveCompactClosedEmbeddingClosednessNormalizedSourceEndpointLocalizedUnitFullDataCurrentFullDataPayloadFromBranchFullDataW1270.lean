import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataCurrentFullDataPayloadFromTargetNormalizedEndpointW1269
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataRoute

/-!
W1270 composes the W987 branch-full-data route with W1269. This replaces
W1269's two-input target/normalized/endpoint surface by W987's one-input
branch-full-data surface.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

/-- W1270 constructs the W977 current full-data payload from W987 data. -/
noncomputable def currentFullDataPayloadOfBranchFullDataW1270
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataPayloadOfTargetNormalizedEndpointW1269
    (w986FullDataOfFullDataW987 data)

/-- W1270 wraps the W987-built W977 payload as the W1008 current-full-data provider. -/
noncomputable def currentFullDataProviderOfBranchFullDataW1270
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008
    where
  currentFullData := currentFullDataPayloadOfBranchFullDataW1270 data

def currentFullDataPayloadFromBranchFullDataInputNamesW1270 : List String :=
  fullDataInputNamesW987

theorem currentFullDataPayloadFromBranchFullDataInputNamesW1270_count :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length = 1 :=
  fullDataInputNamesW987_count

theorem currentFullDataPayloadFromBranchFullDataReducesW1270 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      currentFullDataPayloadFromTargetNormalizedEndpointInputNamesW1269.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    currentFullDataPayloadFromTargetNormalizedEndpointInputNamesW1269_count]
  decide

structure MetrizableCurrentFullDataPayloadFromBranchFullDataStateW1270 :
    Type where
  seed : String
  declarations : List String
  payloadConstructionResult : String
  inputComparisonResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableCurrentFullDataPayloadFromBranchFullDataStateW1270 :
    MetrizableCurrentFullDataPayloadFromBranchFullDataStateW1270
    where
  seed := "w1270-current-full-data-payload-from-branch-full-data"
  declarations :=
    ["currentFullDataPayloadOfBranchFullDataW1270",
      "currentFullDataProviderOfBranchFullDataW1270",
      "currentFullDataPayloadFromBranchFullDataInputNamesW1270",
      "currentFullDataPayloadFromBranchFullDataInputNamesW1270_count",
      "currentFullDataPayloadFromBranchFullDataReducesW1270"]
  payloadConstructionResult :=
    "proved: W1270 constructs the W977 current full-data payload from the\
      existing W987 branch-full-data route through W1269"
  inputComparisonResult :=
    "proved: W1270 reduces the W1269 W986 replacement surface from two\
      explicit inputs to the W987 one-input branch-full-data surface"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1270CurrentFullDataPayloadFromBranchFullData_productSuccess :
    (let state :=
        currentMetrizableCurrentFullDataPayloadFromBranchFullDataStateW1270;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
