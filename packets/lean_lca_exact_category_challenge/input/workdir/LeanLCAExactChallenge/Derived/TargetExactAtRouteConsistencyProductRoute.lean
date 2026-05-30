import LeanLCAExactChallenge.Derived.TargetExactAtW664TerminalProductRoute
import LeanLCAExactChallenge.Derived.TargetExactAtTerminalEvidenceProductRoute

/-!
W804 records that the W803 target-ExactAt W664 terminal route and the W796/W797
target-ExactAt closed-range route compute the same evidence for the same data.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W804 closed-map W803 data viewed as W796 target-ExactAt closed-range data. -/
noncomputable def closedMapClosedRangeDataOfTargetExactAtW804
    (data : MetrizableClosedMapTargetExactAtW664TerminalBranchDataW803) :
    MetrizableClosedMapTargetExactAtClosedRangeBranchDataW796
    where
  comparisonIso := data.comparisonIso
  targetExactAtPayload := data.targetExactAtPayload
  exactInputs := data.exactInputs

/-!
W804 closed-embedding W803 data viewed as W796 target-ExactAt closed-range data.
-/
noncomputable def closedEmbeddingClosedRangeDataOfTargetExactAtW804
    (data : MetrizableClosedEmbeddingTargetExactAtW664TerminalBranchDataW803) :
    MetrizableClosedEmbeddingTargetExactAtClosedRangeBranchDataW796
    where
  comparisonIso := data.comparisonIso
  targetExactAtPayload := data.targetExactAtPayload
  exactInputs := data.exactInputs

/-- W804 closed-map product evidence agrees between W803 and W796. -/
theorem closedMapProductEvidenceTargetExactAtW664_eq_closedRangeW804
    (data : MetrizableClosedMapTargetExactAtW664TerminalBranchDataW803) :
    productEvidence_of_closedMapTargetExactAtW664TerminalRouteW803 data =
      productEvidence_of_closedMapTargetExactAtClosedRangeRouteW796
        (closedMapClosedRangeDataOfTargetExactAtW804 data) :=
  rfl

/-- W804 closed-embedding product evidence agrees between W803 and W796. -/
theorem closedEmbeddingProductEvidenceTargetExactAtW664_eq_closedRangeW804
    (data : MetrizableClosedEmbeddingTargetExactAtW664TerminalBranchDataW803) :
    productEvidence_of_closedEmbeddingTargetExactAtW664TerminalRouteW803 data =
      productEvidence_of_closedEmbeddingTargetExactAtClosedRangeRouteW796
        (closedEmbeddingClosedRangeDataOfTargetExactAtW804 data) :=
  rfl

/-- W804 closed-map exact/stable evidence agrees between W803 and W797. -/
theorem closedMapExactStableEvidenceTargetExactAtW664_eq_terminalW804
    (data : MetrizableClosedMapTargetExactAtW664TerminalBranchDataW803) :
    closedMapExactStableEvidenceOfTargetExactAtW664TerminalW803 data =
      closedMapExactStableEvidenceOfTargetExactAtTerminalW797
        (closedMapClosedRangeDataOfTargetExactAtW804 data) :=
  rfl

/-!
W804 closed-embedding exact/stable evidence agrees between W803 and W797.
-/
theorem closedEmbeddingExactStableEvidenceTargetExactAtW664_eq_terminalW804
    (data : MetrizableClosedEmbeddingTargetExactAtW664TerminalBranchDataW803) :
    closedEmbeddingExactStableEvidenceOfTargetExactAtW664TerminalW803 data =
      closedEmbeddingExactStableEvidenceOfTargetExactAtTerminalW797
        (closedEmbeddingClosedRangeDataOfTargetExactAtW804 data) :=
  rfl

/-- W804 closed-map stable certificate agrees between W803 and W797. -/
theorem closedMapStableCertificateTargetExactAtW664_eq_terminalW804
    (data : MetrizableClosedMapTargetExactAtW664TerminalBranchDataW803) :
    (productEvidence_of_closedMapTargetExactAtW664TerminalRouteW803
        data).kernelCokernelStableCertificate =
      closedMapStableCertificateOfTargetExactAtTerminalW797
        (closedMapClosedRangeDataOfTargetExactAtW804 data) :=
  rfl

/-- W804 closed-embedding stable certificate agrees between W803 and W797. -/
theorem closedEmbeddingStableCertificateTargetExactAtW664_eq_terminalW804
    (data : MetrizableClosedEmbeddingTargetExactAtW664TerminalBranchDataW803) :
    (productEvidence_of_closedEmbeddingTargetExactAtW664TerminalRouteW803
        data).kernelCokernelStableCertificate =
      closedEmbeddingStableCertificateOfTargetExactAtTerminalW797
        (closedEmbeddingClosedRangeDataOfTargetExactAtW804 data) :=
  rfl

/-- W804 closed-map W803 stable certificate is accepted. -/
theorem closedMapStableCertificateAcceptedOfTargetExactAtW664TerminalW804
    (data : MetrizableClosedMapTargetExactAtW664TerminalBranchDataW803) :
    StableRouteAttempt.accepted (C := MetrizableLCA.{0})
      (.fullCertificate
        ((productEvidence_of_closedMapTargetExactAtW664TerminalRouteW803
          data).kernelCokernelStableCertificate)) =
        true :=
  (productEvidence_of_closedMapTargetExactAtW664TerminalRouteW803
    data).kernelCokernelStableAccepted

/-- W804 closed-embedding W803 stable certificate is accepted. -/
theorem closedEmbeddingStableCertificateAcceptedOfTargetExactAtW664TerminalW804
    (data : MetrizableClosedEmbeddingTargetExactAtW664TerminalBranchDataW803) :
    StableRouteAttempt.accepted (C := MetrizableLCA.{0})
      (.fullCertificate
        ((productEvidence_of_closedEmbeddingTargetExactAtW664TerminalRouteW803
          data).kernelCokernelStableCertificate)) =
        true :=
  (productEvidence_of_closedEmbeddingTargetExactAtW664TerminalRouteW803
    data).kernelCokernelStableAccepted

/-- W804 input names for target-ExactAt route consistency. -/
def targetExactAtRouteConsistencyProductRouteInputNamesW804 : List String :=
  ["W803 target-ExactAt W664 terminal branch data",
    "W796 target-ExactAt closed-range product route",
    "W797 target-ExactAt terminal evidence projections"]

theorem targetExactAtRouteConsistencyProductRouteInputNamesW804_count :
    targetExactAtRouteConsistencyProductRouteInputNamesW804.length = 3 :=
  rfl

structure MetrizableTargetExactAtRouteConsistencyStateW804 : Type where
  seed : String
  declarations : List String
  productEvidenceConsistency : String
  exactStableConsistency : String
  stableCertificateConsistency : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetExactAtRouteConsistencyStateW804 :
    MetrizableTargetExactAtRouteConsistencyStateW804
    where
  seed := "w804-target-exactat-route-consistency"
  declarations :=
    ["closedMapClosedRangeDataOfTargetExactAtW804",
      "closedEmbeddingClosedRangeDataOfTargetExactAtW804",
      "closedMapProductEvidenceTargetExactAtW664_eq_closedRangeW804",
      "closedEmbeddingProductEvidenceTargetExactAtW664_eq_closedRangeW804",
      "closedMapExactStableEvidenceTargetExactAtW664_eq_terminalW804",
      "closedEmbeddingExactStableEvidenceTargetExactAtW664_eq_terminalW804",
      "closedMapStableCertificateTargetExactAtW664_eq_terminalW804",
      "closedEmbeddingStableCertificateTargetExactAtW664_eq_terminalW804",
      "closedMapStableCertificateAcceptedOfTargetExactAtW664TerminalW804",
      "closedEmbeddingStableCertificateAcceptedOfTargetExactAtW664TerminalW804",
      "targetExactAtRouteConsistencyProductRouteInputNamesW804",
      "targetExactAtRouteConsistencyProductRouteInputNamesW804_count"]
  productEvidenceConsistency :=
    "proved: W803 target-ExactAt W664 terminal evidence agrees with W796"
  exactStableConsistency :=
    "proved: W803 exact/stable projections agree with W797"
  stableCertificateConsistency :=
    "proved: W803 stable certificates agree with W797 and are accepted"
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "construct target ExactAt realization data for exact-acyclic homotopy\
        objects"]
  productSuccessClaimed := false

theorem currentW804TargetExactAtRouteConsistency_productSuccess :
    (have state := currentMetrizableTargetExactAtRouteConsistencyStateW804;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
