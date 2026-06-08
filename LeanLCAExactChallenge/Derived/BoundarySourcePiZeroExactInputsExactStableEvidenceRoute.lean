import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroExactInputsOpClosureProductRoute

/-!
W1605 projects the existing W762/W758 exact/stable evidence route at the
boundary-source-pi-zero W735 exact-input surface.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/--
W1605 closed-map exact/stable evidence data: one universal W736 comparison
isomorphism premise and one W735 closed-map exact-input record.
-/
structure
    MetrizableClosedMapBoundarySourcePiZeroExactInputsExactStableBranchDataW1605 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735

/--
W1605 closed-embedding exact/stable evidence data: one universal W736
comparison isomorphism premise and one W735 closed-embedding exact-input
record.
-/
structure
    MetrizableClosedEmbeddingBoundarySourcePiZeroExactInputsExactStableBranchDataW1605 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735

/-! Closed-map projections from the two-input W1605 surface. -/

/-- Closed-map W1605 exact/stable evidence from W762. -/
noncomputable def exactStableEvidenceOfClosedMapBoundarySourcePiZeroExactInputsW1605
    (data :
      MetrizableClosedMapBoundarySourcePiZeroExactInputsExactStableBranchDataW1605) :
    MetrizableWppExactStableEvidenceW758 :=
  exactStableEvidence_of_closedMapLeftRightComparisonConcreteLeavesW762
    data.comparisonIso data.exactInputs

/-- Closed-map W1605 projection to the WPP-op exact-acyclic closure input. -/
noncomputable def
    wppOpExactAcyclicClosureOfClosedMapBoundarySourcePiZeroExactInputsW1605
    (data :
      MetrizableClosedMapBoundarySourcePiZeroExactInputsExactStableBranchDataW1605) :
    MetrizableWppOpExactAcyclicClosureInput :=
  (exactStableEvidenceOfClosedMapBoundarySourcePiZeroExactInputsW1605 data).exactAcyclic

/-- Closed-map W1605 projection to accepted stable bounded-derived evidence. -/
noncomputable def acceptedStableOfClosedMapBoundarySourcePiZeroExactInputsW1605
    (data :
      MetrizableClosedMapBoundarySourcePiZeroExactInputsExactStableBranchDataW1605) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  (exactStableEvidenceOfClosedMapBoundarySourcePiZeroExactInputsW1605 data).acceptedStable

/-- Closed-map W1605 accepted stable evidence passes the canonical gate. -/
theorem acceptedStableOfClosedMapBoundarySourcePiZeroExactInputsW1605_accepted
    (data :
      MetrizableClosedMapBoundarySourcePiZeroExactInputsExactStableBranchDataW1605) :
    StableRouteAttempt.accepted
        (C := MetrizableLCA.{0})
        (.fullCertificate
          (acceptedStableOfClosedMapBoundarySourcePiZeroExactInputsW1605 data).certificate) =
      true :=
  (exactStableEvidenceOfClosedMapBoundarySourcePiZeroExactInputsW1605 data).acceptedStableAccepted

/-! Closed-embedding projections from the two-input W1605 surface. -/

/-- Closed-embedding W1605 exact/stable evidence from W762. -/
noncomputable def
    exactStableEvidenceOfClosedEmbeddingBoundarySourcePiZeroExactInputsW1605
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroExactInputsExactStableBranchDataW1605) :
    MetrizableWppExactStableEvidenceW758 :=
  exactStableEvidence_of_closedEmbeddingLeftRightComparisonConcreteLeavesW762
    data.comparisonIso data.exactInputs

/--
Closed-embedding W1605 projection to the WPP-op exact-acyclic closure input.
-/
noncomputable def
    wppOpExactAcyclicClosureOfClosedEmbeddingBoundarySourcePiZeroExactInputsW1605
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroExactInputsExactStableBranchDataW1605) :
    MetrizableWppOpExactAcyclicClosureInput :=
  (exactStableEvidenceOfClosedEmbeddingBoundarySourcePiZeroExactInputsW1605 data).exactAcyclic

/--
Closed-embedding W1605 projection to accepted stable bounded-derived evidence.
-/
noncomputable def
    acceptedStableOfClosedEmbeddingBoundarySourcePiZeroExactInputsW1605
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroExactInputsExactStableBranchDataW1605) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  (exactStableEvidenceOfClosedEmbeddingBoundarySourcePiZeroExactInputsW1605 data).acceptedStable

/-- Closed-embedding W1605 accepted stable evidence passes the canonical gate. -/
theorem acceptedStableOfClosedEmbeddingBoundarySourcePiZeroExactInputsW1605_accepted
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroExactInputsExactStableBranchDataW1605) :
    StableRouteAttempt.accepted
        (C := MetrizableLCA.{0})
        (.fullCertificate
          (acceptedStableOfClosedEmbeddingBoundarySourcePiZeroExactInputsW1605 data).certificate) =
      true :=
  let evidence :=
    exactStableEvidenceOfClosedEmbeddingBoundarySourcePiZeroExactInputsW1605 data
  evidence.acceptedStableAccepted

/-- Top-level input names for the W1605 exact/stable evidence route. -/
def boundarySourcePiZeroExactInputsExactStableEvidenceRouteInputNamesW1605 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data, including W716 boundary\
      data, W519 mapped-cokernel closedness, and W720 endpoint topology data"]

theorem boundarySourcePiZeroExactInputsExactStableEvidenceRouteInputNamesW1605_count :
    boundarySourcePiZeroExactInputsExactStableEvidenceRouteInputNamesW1605.length =
      2 :=
  rfl

/-- Current checked W1605 exact/stable evidence route state. -/
structure MetrizableBoundarySourcePiZeroExactInputsExactStableEvidenceRouteStateW1605 :
    Type where
  seed : String
  declarations : List String
  exactStableResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  inputsEliminatedAtEvidenceSurface : List String
  remainingEvidenceSurfaceInputs : List String
  remainingProductBlockers : List String
  productSuccessClaimed : Bool

/--
Current checked W1605 state: W735 exact inputs plus the W736 comparison
premise already project to exact/stable evidence, including the WPP-op
exact-acyclic closure input.
-/
def currentMetrizableBoundarySourcePiZeroExactInputsExactStableEvidenceRouteStateW1605 :
    MetrizableBoundarySourcePiZeroExactInputsExactStableEvidenceRouteStateW1605
    where
  seed := "w1605-boundary-source-pi-zero-exact-inputs-exact-stable-evidence-route"
  declarations :=
    ["MetrizableClosedMapBoundarySourcePiZeroExactInputsExactStableBranchDataW1605",
      "MetrizableClosedEmbeddingBoundarySourcePiZeroExactInputsExactStableBranchDataW1605",
      "exactStableEvidenceOfClosedMapBoundarySourcePiZeroExactInputsW1605",
      "exactStableEvidenceOfClosedEmbeddingBoundarySourcePiZeroExactInputsW1605",
      "wppOpExactAcyclicClosureOfClosedMapBoundarySourcePiZeroExactInputsW1605",
      "wppOpExactAcyclicClosureOfClosedEmbeddingBoundarySourcePiZeroExactInputsW1605",
      "acceptedStableOfClosedMapBoundarySourcePiZeroExactInputsW1605",
      "acceptedStableOfClosedEmbeddingBoundarySourcePiZeroExactInputsW1605",
      "acceptedStableOfClosedMapBoundarySourcePiZeroExactInputsW1605_accepted",
      "acceptedStableOfClosedEmbeddingBoundarySourcePiZeroExactInputsW1605_accepted",
      "boundarySourcePiZeroExactInputsExactStableEvidenceRouteInputNamesW1605",
      "boundarySourcePiZeroExactInputsExactStableEvidenceRouteInputNamesW1605_count"]
  exactStableResult :=
    "proved: W1605 uses W762/W758 to derive WPP-op exact-acyclic closure and\
      accepted stable evidence from comparisonIso plus W735 exactInputs"
  closedMapResult :=
    "proved: closed-map W735 exact inputs project to MetrizableWppExactStableEvidenceW758"
  closedEmbeddingResult :=
    "proved: closed-embedding W735 exact inputs project to MetrizableWppExactStableEvidenceW758"
  inputsEliminatedAtEvidenceSurface :=
    ["separate WPP-op exact-acyclic colimit closure input",
      "separate accepted stable evidence input"]
  remainingEvidenceSurfaceInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch, including W716 boundary\
        data, W519 mapped-cokernel closedness, and W720 endpoint topology data"]
  remainingProductBlockers :=
    ["replace the accepted stable bounded-derived boundary gate with the final\
        bounded derived infinity-category API required by the product contract",
      "construct the original four-task positive witness declarations",
      "if routing through W1604 stable-boundary packaging, also prove\
        exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed"]
  productSuccessClaimed := false

theorem
    currentW1605BoundarySourcePiZeroExactInputsExactStableEvidenceRoute_productSuccess :
    (have state :=
      currentMetrizableBoundarySourcePiZeroExactInputsExactStableEvidenceRouteStateW1605;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
