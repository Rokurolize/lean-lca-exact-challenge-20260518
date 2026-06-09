import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroExactInputsOpClosureProductRoute
import LeanLCAExactChallenge.Derived.ComparisonBijectivityLeftCalculusRoute

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

/-! Comparison-bijectivity specializations of the W1605 evidence surface. -/

/--
W831 supplies the comparison premise, leaving only closed-map W735 exact
inputs at the W1605 exact/stable evidence surface.
-/
noncomputable def
    closedMapExactStableBranchDataOfW831W1605
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableClosedMapBoundarySourcePiZeroExactInputsExactStableBranchDataW1605
    where
  comparisonIso := universalLeftRightComparisonIso_of_comparisonBijectivityW831
  exactInputs := exactInputs

/--
W831 supplies the comparison premise, leaving only closed-embedding W735 exact
inputs at the W1605 exact/stable evidence surface.
-/
noncomputable def
    closedEmbeddingExactStableBranchDataOfW831W1605
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableClosedEmbeddingBoundarySourcePiZeroExactInputsExactStableBranchDataW1605
    where
  comparisonIso := universalLeftRightComparisonIso_of_comparisonBijectivityW831
  exactInputs := exactInputs

/-- Closed-map W1605 exact/stable evidence with W831 discharging comparison. -/
noncomputable def
    exactStableEvidenceOfClosedMapW831ExactInputsW1605
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableWppExactStableEvidenceW758 :=
  exactStableEvidenceOfClosedMapBoundarySourcePiZeroExactInputsW1605
    (closedMapExactStableBranchDataOfW831W1605 exactInputs)

/--
Closed-map W1605 WPP-op exact-acyclic closure with W831 discharging
comparison.
-/
noncomputable def
    wppOpExactAcyclicClosureOfClosedMapW831ExactInputsW1605
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableWppOpExactAcyclicClosureInput :=
  (exactStableEvidenceOfClosedMapW831ExactInputsW1605
    exactInputs).exactAcyclic

/-- Closed-map accepted stable evidence with W831 discharging comparison. -/
noncomputable def
    acceptedStableOfClosedMapW831ExactInputsW1605
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  (exactStableEvidenceOfClosedMapW831ExactInputsW1605
    exactInputs).acceptedStable

/-- The closed-map comparison-bijectivity W1605 accepted stable evidence is accepted. -/
theorem
    acceptedStableOfClosedMapW831ExactInputsW1605_accepted
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    StableRouteAttempt.accepted
        (C := MetrizableLCA.{0})
        (.fullCertificate
          (acceptedStableOfClosedMapW831ExactInputsW1605 exactInputs).certificate) =
      true :=
  (exactStableEvidenceOfClosedMapW831ExactInputsW1605
    exactInputs).acceptedStableAccepted

/-- Closed-embedding W1605 exact/stable evidence with W831 discharging comparison. -/
noncomputable def
    exactStableEvidenceOfClosedEmbeddingW831ExactInputsW1605
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableWppExactStableEvidenceW758 :=
  exactStableEvidenceOfClosedEmbeddingBoundarySourcePiZeroExactInputsW1605
    (closedEmbeddingExactStableBranchDataOfW831W1605 exactInputs)

/--
Closed-embedding W1605 WPP-op exact-acyclic closure with W831 discharging
comparison.
-/
noncomputable def
    wppOpExactAcyclicClosureOfClosedEmbeddingW831ExactInputsW1605
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableWppOpExactAcyclicClosureInput :=
  (exactStableEvidenceOfClosedEmbeddingW831ExactInputsW1605
    exactInputs).exactAcyclic

/-- Closed-embedding accepted stable evidence with W831 discharging comparison. -/
noncomputable def
    acceptedStableOfClosedEmbeddingW831ExactInputsW1605
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  (exactStableEvidenceOfClosedEmbeddingW831ExactInputsW1605
    exactInputs).acceptedStable

/--
The closed-embedding comparison-bijectivity W1605 accepted stable evidence is
accepted.
-/
theorem
    acceptedStableOfClosedEmbeddingW831ExactInputsW1605_accepted
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    StableRouteAttempt.accepted
        (C := MetrizableLCA.{0})
        (.fullCertificate
          (acceptedStableOfClosedEmbeddingW831ExactInputsW1605 exactInputs).certificate) =
      true :=
  (exactStableEvidenceOfClosedEmbeddingW831ExactInputsW1605
    exactInputs).acceptedStableAccepted

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

/--
Top-level input names for the comparison-bijectivity-specialized W1605
exact/stable evidence route.
-/
def
    boundarySourcePiZeroW831ExactStableEvidenceInputNamesW1605 :
    List String :=
  ["W735 closed-map or closed-embedding branch data, including W716 boundary\
      data, W519 mapped-cokernel closedness, and W720 endpoint topology data"]

theorem
    boundarySourcePiZeroW831ExactStableEvidenceInputNamesW1605_count :
    boundarySourcePiZeroW831ExactStableEvidenceInputNamesW1605.length =
      1 :=
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

/--
Current checked W1605 comparison-bijectivity specialization: W831 removes the
comparison premise from the exact/stable evidence surface.
-/
def
    currentMetrizableBoundarySourcePiZeroW831ExactStableEvidenceRouteStateW1605 :
    MetrizableBoundarySourcePiZeroExactInputsExactStableEvidenceRouteStateW1605
    where
  seed :=
    "w1605-boundary-source-pi-zero-comparison-bijectivity-exact-inputs-exact-stable-evidence-route"
  declarations :=
    ["closedMapExactStableBranchDataOfW831W1605",
      "closedEmbeddingExactStableBranchDataOfW831W1605",
      "exactStableEvidenceOfClosedMapW831ExactInputsW1605",
      "exactStableEvidenceOfClosedEmbeddingW831ExactInputsW1605",
      "wppOpExactAcyclicClosureOfClosedMapW831ExactInputsW1605",
      "wppOpExactAcyclicClosureOfClosedEmbeddingW831ExactInputsW1605",
      "acceptedStableOfClosedMapW831ExactInputsW1605",
      "acceptedStableOfClosedEmbeddingW831ExactInputsW1605",
      "acceptedStableOfClosedMapW831ExactInputsW1605_accepted",
      "acceptedStableOfClosedEmbeddingW831ExactInputsW1605_accepted",
      "boundarySourcePiZeroW831ExactStableEvidenceInputNamesW1605",
      "boundarySourcePiZeroW831ExactStableEvidenceInputNamesW1605_count"]
  exactStableResult :=
    "proved: W831 supplies the universal comparison isomorphism, so W1605\
      derives WPP-op exact-acyclic closure and accepted stable evidence from\
      one W735 exact-input branch"
  closedMapResult :=
    "proved: closed-map W735 exact inputs alone project to\
      MetrizableWppExactStableEvidenceW758 through W831-specialized W1605"
  closedEmbeddingResult :=
    "proved: closed-embedding W735 exact inputs alone project to\
      MetrizableWppExactStableEvidenceW758 through W831-specialized W1605"
  inputsEliminatedAtEvidenceSurface :=
    ["universal left-right comparison isomorphism for arbitrary MetrizableLCA\
        short complexes",
      "separate WPP-op exact-acyclic colimit closure input",
      "separate accepted stable evidence input"]
  remainingEvidenceSurfaceInputs :=
    ["construct concrete values for one W735 branch, including W716 boundary\
        data, W519 mapped-cokernel closedness, and W720 endpoint topology data"]
  remainingProductBlockers :=
    ["replace the accepted stable bounded-derived boundary gate with the final\
        bounded derived infinity-category API required by the product contract",
      "construct the original four-task positive witness declarations",
      "if routing through W1604 stable-boundary packaging, also prove\
        exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed"]
  productSuccessClaimed := false

theorem
    currentW1605BoundarySourcePiZeroW831ExactStableEvidenceRoute_productSuccess :
    (have state :=
      currentMetrizableBoundarySourcePiZeroW831ExactStableEvidenceRouteStateW1605;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
