import LeanLCAExactChallenge.Derived.TargetExactAtClosedRangeProductRoute

/-!
W797 exposes the terminal evidence projections already carried by the W796
target ExactAt closed-range product evidence.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W797 closed-map exact/stable evidence projected from W796 product evidence. -/
noncomputable def closedMapExactStableEvidenceOfTargetExactAtTerminalW797
    (data : MetrizableClosedMapTargetExactAtClosedRangeBranchDataW796) :
    MetrizableWppExactStableEvidenceW758 :=
  (productEvidence_of_closedMapTargetExactAtClosedRangeRouteW796 data).exactStableEvidence

/-!
W797 closed-embedding exact/stable evidence projected from W796 product evidence.
-/
noncomputable def closedEmbeddingExactStableEvidenceOfTargetExactAtTerminalW797
    (data : MetrizableClosedEmbeddingTargetExactAtClosedRangeBranchDataW796) :
    MetrizableWppExactStableEvidenceW758 :=
  (productEvidence_of_closedEmbeddingTargetExactAtClosedRangeRouteW796 data).exactStableEvidence

/-- W797 closed-map stable certificate projected from W796 product evidence. -/
noncomputable def closedMapStableCertificateOfTargetExactAtTerminalW797
    (data : MetrizableClosedMapTargetExactAtClosedRangeBranchDataW796) :
    Dbounded.StableFourProjectionCertificate MetrizableLCA.{0} :=
  let evidence :=
    productEvidence_of_closedMapTargetExactAtClosedRangeRouteW796 data
  evidence.kernelCokernelStableCertificate

/-!
W797 closed-embedding stable certificate projected from W796 product evidence.
-/
noncomputable def closedEmbeddingStableCertificateOfTargetExactAtTerminalW797
    (data : MetrizableClosedEmbeddingTargetExactAtClosedRangeBranchDataW796) :
    Dbounded.StableFourProjectionCertificate MetrizableLCA.{0} :=
  let evidence :=
    productEvidence_of_closedEmbeddingTargetExactAtClosedRangeRouteW796 data
  evidence.kernelCokernelStableCertificate

/-- W797 closed-map stable certificate readiness from W796 product evidence. -/
theorem closedMapStableCertificateReadyOfTargetExactAtTerminalW797
    (data : MetrizableClosedMapTargetExactAtClosedRangeBranchDataW796) :
    (closedMapStableCertificateOfTargetExactAtTerminalW797 data).ready :=
  (productEvidence_of_closedMapTargetExactAtClosedRangeRouteW796 data).kernelCokernelStableReady

/-!
W797 closed-embedding stable certificate readiness from W796 product evidence.
-/
theorem closedEmbeddingStableCertificateReadyOfTargetExactAtTerminalW797
    (data : MetrizableClosedEmbeddingTargetExactAtClosedRangeBranchDataW796) :
    (closedEmbeddingStableCertificateOfTargetExactAtTerminalW797 data).ready :=
  let evidence :=
    productEvidence_of_closedEmbeddingTargetExactAtClosedRangeRouteW796 data
  evidence.kernelCokernelStableReady

/-- W797 closed-map stable certificate acceptance from W796 product evidence. -/
theorem closedMapStableCertificateAcceptedOfTargetExactAtTerminalW797
    (data : MetrizableClosedMapTargetExactAtClosedRangeBranchDataW796) :
    StableRouteAttempt.accepted (C := MetrizableLCA.{0})
      (.fullCertificate
        (closedMapStableCertificateOfTargetExactAtTerminalW797 data)) =
        true :=
  (productEvidence_of_closedMapTargetExactAtClosedRangeRouteW796 data).kernelCokernelStableAccepted

/-!
W797 closed-embedding stable certificate acceptance from W796 product evidence.
-/
theorem closedEmbeddingStableCertificateAcceptedOfTargetExactAtTerminalW797
    (data : MetrizableClosedEmbeddingTargetExactAtClosedRangeBranchDataW796) :
    StableRouteAttempt.accepted (C := MetrizableLCA.{0})
      (.fullCertificate
        (closedEmbeddingStableCertificateOfTargetExactAtTerminalW797 data)) =
        true :=
  let evidence :=
    productEvidence_of_closedEmbeddingTargetExactAtClosedRangeRouteW796 data
  evidence.kernelCokernelStableAccepted

/-- W797 input names for the terminal evidence projection route. -/
def targetExactAtTerminalEvidenceProductRouteInputNamesW797 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data",
    "exact-acyclic homotopy-object target ExactAt realization data"]

theorem targetExactAtTerminalEvidenceProductRouteInputNamesW797_count :
    targetExactAtTerminalEvidenceProductRouteInputNamesW797.length = 3 :=
  rfl

/-- Current checked W797 state. -/
structure MetrizableTargetExactAtTerminalEvidenceRouteStateW797 : Type where
  seed : String
  declarations : List String
  exactStableResult : String
  stableCertificateResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W797 state for the target ExactAt terminal evidence route. -/
def currentMetrizableTargetExactAtTerminalEvidenceRouteStateW797 :
    MetrizableTargetExactAtTerminalEvidenceRouteStateW797
    where
  seed := "w797-target-exact-at-terminal-evidence-route"
  declarations :=
    ["closedMapExactStableEvidenceOfTargetExactAtTerminalW797",
      "closedEmbeddingExactStableEvidenceOfTargetExactAtTerminalW797",
      "closedMapStableCertificateOfTargetExactAtTerminalW797",
      "closedEmbeddingStableCertificateOfTargetExactAtTerminalW797",
      "closedMapStableCertificateReadyOfTargetExactAtTerminalW797",
      "closedEmbeddingStableCertificateReadyOfTargetExactAtTerminalW797",
      "closedMapStableCertificateAcceptedOfTargetExactAtTerminalW797",
      "closedEmbeddingStableCertificateAcceptedOfTargetExactAtTerminalW797",
      "targetExactAtTerminalEvidenceProductRouteInputNamesW797",
      "targetExactAtTerminalEvidenceProductRouteInputNamesW797_count"]
  exactStableResult :=
    "proved: W796 product evidence projects exact/stable WPP evidence"
  stableCertificateResult :=
    "proved: W796 product evidence projects ready accepted stable certificates"
  replacedInputs :=
    ["separate Dbounded stable-infinity input listed after W796 evidence\
      projection"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "construct exact-acyclic homotopy-object target ExactAt realization data"]
  productSuccessClaimed := false

theorem currentW797TargetExactAtTerminalEvidenceRoute_productSuccess :
    (have state := currentMetrizableTargetExactAtTerminalEvidenceRouteStateW797;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
