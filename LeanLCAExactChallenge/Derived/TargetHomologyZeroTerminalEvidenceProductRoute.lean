import LeanLCAExactChallenge.Derived.TargetHomologyZeroComparisonHomologyProductRoute

/-!
W798 exposes the terminal evidence projections carried by the W794 target
homology-zero comparison-homology product evidence.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W798 closed-map exact/stable evidence projected from W794 product evidence. -/
noncomputable def closedMapExactStableEvidenceOfTargetHomologyZeroTerminalW798
    (data : MetrizableClosedMapTargetHomologyZeroComparisonHomologyBranchDataW794) :
    MetrizableWppExactStableEvidenceW758 :=
  (productEvidence_of_closedMapComparisonHomologyRouteW794 data).exactStableEvidence

noncomputable def
    closedEmbeddingExactStableEvidenceOfTargetHomologyZeroTerminalW798
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroComparisonHomologyBranchDataW794) :
    MetrizableWppExactStableEvidenceW758 :=
  (productEvidence_of_closedEmbeddingComparisonHomologyRouteW794
    data).exactStableEvidence

noncomputable def closedMapStableCertificateOfTargetHomologyZeroTerminalW798
    (data : MetrizableClosedMapTargetHomologyZeroComparisonHomologyBranchDataW794) :
    Dbounded.StableFourProjectionCertificate MetrizableLCA.{0} :=
  let evidence := productEvidence_of_closedMapComparisonHomologyRouteW794 data
  evidence.kernelCokernelStableCertificate

noncomputable def
    closedEmbeddingStableCertificateOfTargetHomologyZeroTerminalW798
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroComparisonHomologyBranchDataW794) :
    Dbounded.StableFourProjectionCertificate MetrizableLCA.{0} :=
  let evidence :=
    productEvidence_of_closedEmbeddingComparisonHomologyRouteW794 data
  evidence.kernelCokernelStableCertificate

theorem closedMapStableCertificateReadyOfTargetHomologyZeroTerminalW798
    (data : MetrizableClosedMapTargetHomologyZeroComparisonHomologyBranchDataW794) :
    (closedMapStableCertificateOfTargetHomologyZeroTerminalW798 data).ready :=
  (productEvidence_of_closedMapComparisonHomologyRouteW794
    data).kernelCokernelStableReady

theorem closedEmbeddingStableCertificateReadyOfTargetHomologyZeroTerminalW798
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroComparisonHomologyBranchDataW794) :
    (closedEmbeddingStableCertificateOfTargetHomologyZeroTerminalW798
      data).ready :=
  let evidence :=
    productEvidence_of_closedEmbeddingComparisonHomologyRouteW794 data
  evidence.kernelCokernelStableReady

theorem closedMapStableCertificateAcceptedOfTargetHomologyZeroTerminalW798
    (data : MetrizableClosedMapTargetHomologyZeroComparisonHomologyBranchDataW794) :
    StableRouteAttempt.accepted (C := MetrizableLCA.{0})
      (.fullCertificate
        (closedMapStableCertificateOfTargetHomologyZeroTerminalW798 data)) =
        true :=
  (productEvidence_of_closedMapComparisonHomologyRouteW794
    data).kernelCokernelStableAccepted

theorem closedEmbeddingStableCertificateAcceptedOfTargetHomologyZeroTerminalW798
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroComparisonHomologyBranchDataW794) :
    StableRouteAttempt.accepted (C := MetrizableLCA.{0})
      (.fullCertificate
        (closedEmbeddingStableCertificateOfTargetHomologyZeroTerminalW798
          data)) =
        true :=
  let evidence :=
    productEvidence_of_closedEmbeddingComparisonHomologyRouteW794 data
  evidence.kernelCokernelStableAccepted

/-- W798 closed-map terminal evidence converted to the W769 stable-data surface. -/
noncomputable def
    directFiniteShapeStableDataOfClosedMapTargetHomologyZeroTerminalEvidenceW798
    (data :
      MetrizableClosedMapTargetHomologyZeroComparisonHomologyBranchDataW794) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapTargetHomologyZeroComparisonHomologyW794
    data

/--
W798 closed-embedding terminal evidence converted to the W769 stable-data
surface.
-/
noncomputable def
    directFiniteShapeStableDataOfClosedEmbeddingTargetHomologyZeroTerminalEvidenceW798
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroComparisonHomologyBranchDataW794) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingTargetHomologyZeroComparisonHomologyW794
    data

/-- W798 closed-map terminal evidence as canonical stable-instance boundary inputs. -/
noncomputable def
    stableBoundaryInputsOfClosedMapTargetHomologyZeroTerminalEvidenceW798
    (data :
      MetrizableClosedMapTargetHomologyZeroComparisonHomologyBranchDataW794) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapTargetHomologyZeroComparisonHomologyW794 data

/--
W798 closed-embedding terminal evidence as canonical stable-instance boundary
inputs.
-/
noncomputable def
    stableBoundaryInputsOfClosedEmbeddingTargetHomologyZeroTerminalEvidenceW798
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroComparisonHomologyBranchDataW794) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingTargetHomologyZeroComparisonHomologyW794
    data

/-- W798 closed-map terminal evidence passes the accepted stable boundary gate. -/
noncomputable def acceptedStableOfClosedMapTargetHomologyZeroTerminalEvidenceW798
    (data :
      MetrizableClosedMapTargetHomologyZeroComparisonHomologyBranchDataW794) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapTargetHomologyZeroComparisonHomologyW794 data

/--
W798 closed-embedding terminal evidence passes the accepted stable boundary gate.
-/
noncomputable def
    acceptedStableOfClosedEmbeddingTargetHomologyZeroTerminalEvidenceW798
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroComparisonHomologyBranchDataW794) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingTargetHomologyZeroComparisonHomologyW794 data

/-- W798 closed-map terminal evidence produces the canonical stable-boundary package. -/
noncomputable def
    boundedDerivedOfClosedMapTargetHomologyZeroTerminalEvidenceStableBoundaryW798
    (data :
      MetrizableClosedMapTargetHomologyZeroComparisonHomologyBranchDataW794) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapTargetHomologyZeroComparisonHomologyStableBoundaryW794
    data

/--
W798 closed-embedding terminal evidence produces the canonical stable-boundary
package.
-/
noncomputable def
    boundedDerivedOfClosedEmbeddingTargetHomologyZeroTerminalEvidenceStableBoundaryW798
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroComparisonHomologyBranchDataW794) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingTargetHomologyZeroComparisonHomologyStableBoundaryW794
    data

/-- W798 input names for the target homology-zero terminal evidence route. -/
def targetHomologyZeroTerminalEvidenceProductRouteInputNamesW798 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data",
    "target homology-zero realization data indexed by W768-derived homology\
      existence"]

theorem targetHomologyZeroTerminalEvidenceProductRouteInputNamesW798_count :
    targetHomologyZeroTerminalEvidenceProductRouteInputNamesW798.length = 3 :=
  rfl

/-- Current checked W798 state. -/
structure MetrizableTargetHomologyZeroTerminalEvidenceRouteStateW798 : Type where
  seed : String
  declarations : List String
  exactStableResult : String
  stableCertificateResult : String
  stableBoundaryResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W798 state for the target homology-zero terminal route. -/
def currentMetrizableTargetHomologyZeroTerminalEvidenceRouteStateW798 :
    MetrizableTargetHomologyZeroTerminalEvidenceRouteStateW798
    where
  seed := "w798-target-homology-zero-terminal-evidence-route"
  declarations :=
    ["closedMapExactStableEvidenceOfTargetHomologyZeroTerminalW798",
      "closedEmbeddingExactStableEvidenceOfTargetHomologyZeroTerminalW798",
      "closedMapStableCertificateOfTargetHomologyZeroTerminalW798",
      "closedEmbeddingStableCertificateOfTargetHomologyZeroTerminalW798",
      "closedMapStableCertificateReadyOfTargetHomologyZeroTerminalW798",
      "closedEmbeddingStableCertificateReadyOfTargetHomologyZeroTerminalW798",
      "closedMapStableCertificateAcceptedOfTargetHomologyZeroTerminalW798",
      "closedEmbeddingStableCertificateAcceptedOfTargetHomologyZeroTerminalW798",
      "directFiniteShapeStableDataOfClosedMapTargetHomologyZeroTerminalEvidenceW798",
      "directFiniteShapeStableDataOfClosedEmbeddingTargetHomologyZeroTerminalEvidenceW798",
      "stableBoundaryInputsOfClosedMapTargetHomologyZeroTerminalEvidenceW798",
      "stableBoundaryInputsOfClosedEmbeddingTargetHomologyZeroTerminalEvidenceW798",
      "acceptedStableOfClosedMapTargetHomologyZeroTerminalEvidenceW798",
      "acceptedStableOfClosedEmbeddingTargetHomologyZeroTerminalEvidenceW798",
      "boundedDerivedOfClosedMapTargetHomologyZeroTerminalEvidenceStableBoundaryW798",
      "boundedDerivedOfClosedEmbeddingTargetHomologyZeroTerminalEvidenceStableBoundaryW798",
      "targetHomologyZeroTerminalEvidenceProductRouteInputNamesW798",
      "targetHomologyZeroTerminalEvidenceProductRouteInputNamesW798_count"]
  exactStableResult :=
    "proved: W794 product evidence projects exact/stable WPP evidence"
  stableCertificateResult :=
    "proved: W794 product evidence projects ready accepted stable certificates"
  stableBoundaryResult :=
    "proved: W798 terminal evidence exposes the W794/W774/W773/W769 canonical\
      stable-boundary gate"
  replacedInputs :=
    ["target ExactAt realization data listed by the W797 terminal-evidence route",
      "separate W794 comparison-homology stable-boundary branch input"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "construct target homology-zero realization data indexed by the\
        comparison-derived homology existence"]
  productSuccessClaimed := false

theorem currentW798TargetHomologyZeroTerminalEvidenceRoute_productSuccess :
    (have state :=
      currentMetrizableTargetHomologyZeroTerminalEvidenceRouteStateW798;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
