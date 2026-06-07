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

/-!
W804 closed-map direct stable data agrees between W803 and the W796/W774
closed-range route.
-/
theorem closedMapDirectFiniteShapeStableDataTargetExactAtW664_eq_closedRangeW804
    (data : MetrizableClosedMapTargetExactAtW664TerminalBranchDataW803) :
    directFiniteShapeStableDataOfClosedMapTargetExactAtW664TerminalW803 data =
      directFiniteShapeStableDataOfClosedMapNormalizedDirectSourceClosedRangeW774
        (closedMapNormalizedDataOfTargetExactAtClosedRangeW796
          (closedMapClosedRangeDataOfTargetExactAtW804 data)) :=
  rfl

/-!
W804 closed-embedding direct stable data agrees between W803 and the W796/W774
closed-range route.
-/
theorem closedEmbeddingDirectFiniteShapeStableDataTargetExactAtW664_eq_closedRangeW804
    (data : MetrizableClosedEmbeddingTargetExactAtW664TerminalBranchDataW803) :
    directFiniteShapeStableDataOfClosedEmbeddingTargetExactAtW664TerminalW803 data =
      directFiniteShapeStableDataOfClosedEmbeddingNormalizedDirectSourceClosedRangeW774
        (closedEmbeddingNormalizedDataOfTargetExactAtClosedRangeW796
          (closedEmbeddingClosedRangeDataOfTargetExactAtW804 data)) :=
  rfl

/-!
W804 closed-map stable-boundary inputs agree between W803 and the W796/W774
closed-range route.
-/
theorem closedMapStableBoundaryInputsTargetExactAtW664_eq_closedRangeW804
    (data : MetrizableClosedMapTargetExactAtW664TerminalBranchDataW803) :
    stableBoundaryInputsOfClosedMapTargetExactAtW664TerminalW803 data =
      stableBoundaryInputsOfClosedMapNormalizedDirectSourceClosedRangeW774
        (closedMapNormalizedDataOfTargetExactAtClosedRangeW796
          (closedMapClosedRangeDataOfTargetExactAtW804 data)) :=
  rfl

/-!
W804 closed-embedding stable-boundary inputs agree between W803 and the
W796/W774 closed-range route.
-/
theorem closedEmbeddingStableBoundaryInputsTargetExactAtW664_eq_closedRangeW804
    (data : MetrizableClosedEmbeddingTargetExactAtW664TerminalBranchDataW803) :
    stableBoundaryInputsOfClosedEmbeddingTargetExactAtW664TerminalW803 data =
      stableBoundaryInputsOfClosedEmbeddingNormalizedDirectSourceClosedRangeW774
        (closedEmbeddingNormalizedDataOfTargetExactAtClosedRangeW796
          (closedEmbeddingClosedRangeDataOfTargetExactAtW804 data)) :=
  rfl

/-!
W804 closed-map accepted stable packages agree between W803 and the W796/W774
closed-range route.
-/
theorem closedMapAcceptedStableTargetExactAtW664_eq_closedRangeW804
    (data : MetrizableClosedMapTargetExactAtW664TerminalBranchDataW803) :
    acceptedStableOfClosedMapTargetExactAtW664TerminalW803 data =
      acceptedStableOfClosedMapNormalizedDirectSourceClosedRangeW774
        (closedMapNormalizedDataOfTargetExactAtClosedRangeW796
          (closedMapClosedRangeDataOfTargetExactAtW804 data)) :=
  rfl

/-!
W804 closed-embedding accepted stable packages agree between W803 and the
W796/W774 closed-range route.
-/
theorem closedEmbeddingAcceptedStableTargetExactAtW664_eq_closedRangeW804
    (data : MetrizableClosedEmbeddingTargetExactAtW664TerminalBranchDataW803) :
    acceptedStableOfClosedEmbeddingTargetExactAtW664TerminalW803 data =
      acceptedStableOfClosedEmbeddingNormalizedDirectSourceClosedRangeW774
        (closedEmbeddingNormalizedDataOfTargetExactAtClosedRangeW796
          (closedEmbeddingClosedRangeDataOfTargetExactAtW804 data)) :=
  rfl

/-!
W804 closed-map bounded-derived stable-boundary packages agree between W803 and
the W796/W774 closed-range route.
-/
theorem closedMapBoundedDerivedStableBoundaryTargetExactAtW664_eq_closedRangeW804
    (data : MetrizableClosedMapTargetExactAtW664TerminalBranchDataW803) :
    boundedDerivedOfClosedMapTargetExactAtW664TerminalStableBoundaryW803 data =
      boundedDerivedOfClosedMapNormalizedDirectSourceClosedRangeStableBoundaryW774
        (closedMapNormalizedDataOfTargetExactAtClosedRangeW796
          (closedMapClosedRangeDataOfTargetExactAtW804 data)) :=
  rfl

/-!
W804 closed-embedding bounded-derived stable-boundary packages agree between
W803 and the W796/W774 closed-range route.
-/
theorem closedEmbeddingBoundedDerivedStableBoundaryTargetExactAtW664_eq_closedRangeW804
    (data : MetrizableClosedEmbeddingTargetExactAtW664TerminalBranchDataW803) :
    boundedDerivedOfClosedEmbeddingTargetExactAtW664TerminalStableBoundaryW803 data =
      boundedDerivedOfClosedEmbeddingNormalizedDirectSourceClosedRangeStableBoundaryW774
        (closedEmbeddingNormalizedDataOfTargetExactAtClosedRangeW796
          (closedEmbeddingClosedRangeDataOfTargetExactAtW804 data)) :=
  rfl

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
  stableBoundaryConsistency : String
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
      "closedMapDirectFiniteShapeStableDataTargetExactAtW664_eq_closedRangeW804",
      "closedEmbeddingDirectFiniteShapeStableDataTargetExactAtW664_eq_closedRangeW804",
      "closedMapStableBoundaryInputsTargetExactAtW664_eq_closedRangeW804",
      "closedEmbeddingStableBoundaryInputsTargetExactAtW664_eq_closedRangeW804",
      "closedMapAcceptedStableTargetExactAtW664_eq_closedRangeW804",
      "closedEmbeddingAcceptedStableTargetExactAtW664_eq_closedRangeW804",
      "closedMapBoundedDerivedStableBoundaryTargetExactAtW664_eq_closedRangeW804",
      "closedEmbeddingBoundedDerivedStableBoundaryTargetExactAtW664_eq_closedRangeW804",
      "targetExactAtRouteConsistencyProductRouteInputNamesW804",
      "targetExactAtRouteConsistencyProductRouteInputNamesW804_count"]
  productEvidenceConsistency :=
    "proved: W803 target-ExactAt W664 terminal evidence agrees with W796"
  exactStableConsistency :=
    "proved: W803 exact/stable projections agree with W797"
  stableCertificateConsistency :=
    "proved: W803 stable certificates agree with W797 and are accepted"
  stableBoundaryConsistency :=
    "proved: W803 stable-boundary packages agree with the W796/W774\
      closed-range route"
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
