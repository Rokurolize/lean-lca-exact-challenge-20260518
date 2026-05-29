import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataCurrentFullDataPayloadW1262
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationDataTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoDataRoute

/-!
W1263 guards the W977 payload boundary: the W976 leaf surface has seven
explicit inputs, so replacing the single W977 payload by those leaves is an
expansion, not a completion witness.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def currentFullDataPayloadLeafInputNamesW1263 : List String :=
  closedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopIsoBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoDataInputNamesW976

theorem currentFullDataPayloadLeafInputNamesW1263_count :
    currentFullDataPayloadLeafInputNamesW1263.length = 7 :=
  closedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopIsoBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoDataInputNamesW976_count

theorem currentFullDataPayloadLeafExpansionW1263 :
    currentFullDataPayloadInputNamesW1262.length <
      currentFullDataPayloadLeafInputNamesW1263.length := by
  rw [currentFullDataPayloadInputNamesW1262_count,
    currentFullDataPayloadLeafInputNamesW1263_count]
  decide

structure MetrizableCurrentFullDataPayloadLeafExpansionGuardStateW1263 :
    Type where
  seed : String
  declarations : List String
  payloadResult : String
  leafExpansionResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableCurrentFullDataPayloadLeafExpansionGuardStateW1263 :
    MetrizableCurrentFullDataPayloadLeafExpansionGuardStateW1263
    where
  seed := "w1263-current-full-data-payload-leaf-expansion-guard"
  declarations :=
    ["currentFullDataPayloadLeafInputNamesW1263",
      "currentFullDataPayloadLeafInputNamesW1263_count",
      "currentFullDataPayloadLeafExpansionW1263"]
  payloadResult :=
    "proved: W1263 preserves the W1262 one-entry W977 current full-data\
      payload as the current remaining input"
  leafExpansionResult :=
    "proved: expanding that W977 payload to the W976 leaf surface exposes\
      seven explicit inputs, so the expansion is not a completion witness"
  remainingInputs := currentFullDataPayloadInputNamesW1262
  productSuccessClaimed := false

theorem currentW1263CurrentFullDataPayloadLeafExpansionGuard_productSuccess :
    (let state :=
        currentMetrizableCurrentFullDataPayloadLeafExpansionGuardStateW1263;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
