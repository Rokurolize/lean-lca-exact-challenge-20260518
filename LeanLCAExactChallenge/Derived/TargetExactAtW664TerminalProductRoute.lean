import LeanLCAExactChallenge.Derived.TargetHomologyZeroW664RouteConsistencyProductRoute

/-!
W803 replaces the explicit W664 target homology-zero payload premise by target
ExactAt realization data plus the homology existence derived from W768.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/--
W803 turns target ExactAt realization data into the W664 target homology-zero
payload once global homology existence is available.
-/
theorem targetHomologyZeroPayloadOfTargetExactAtW803
    (hasHomology :
      ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ), K.HasHomology i)
    (payload : MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785) :
    MetrizableExactAcyclicHomotopyObjectTrianglehIso13TargetHomologyZeroPayloadW664
      hasHomology := by
  intro T hT h₁ h₃
  rcases payload hT h₁ h₃ with
    ⟨K, L, Lexact, f, e₁, e₃, eL, comm, hExactAt⟩
  refine ⟨K, L, Lexact, f, e₁, e₃, eL, comm, ?_⟩
  intro i
  letI : Lexact.HasHomology i := hasHomology Lexact i
  exact HomologicalComplex.ExactAt.isZero_homology (hExactAt i)

/-- W803 closed-map branch data using target ExactAt data instead of W664 data. -/
structure MetrizableClosedMapTargetExactAtW664TerminalBranchDataW803 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  targetExactAtPayload :
    MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735

/-!
W803 closed-embedding branch data using target ExactAt data instead of W664
data.
-/
structure MetrizableClosedEmbeddingTargetExactAtW664TerminalBranchDataW803 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  targetExactAtPayload :
    MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735

/-- W803 closed-map target ExactAt data converted to W799 W664 data. -/
noncomputable def closedMapW664TerminalDataOfTargetExactAtW803
    (data : MetrizableClosedMapTargetExactAtW664TerminalBranchDataW803) :
    MetrizableClosedMapTargetHomologyZeroW664TerminalBranchDataW799
    where
  comparisonIso := data.comparisonIso
  targetHomologyZeroPayload :=
    targetHomologyZeroPayloadOfTargetExactAtW803
      (cochainHasHomology_of_leftRightComparisonIsoW768 data.comparisonIso)
      data.targetExactAtPayload
  exactInputs := data.exactInputs

/-- W803 closed-embedding target ExactAt data converted to W799 W664 data. -/
noncomputable def closedEmbeddingW664TerminalDataOfTargetExactAtW803
    (data : MetrizableClosedEmbeddingTargetExactAtW664TerminalBranchDataW803) :
    MetrizableClosedEmbeddingTargetHomologyZeroW664TerminalBranchDataW799
    where
  comparisonIso := data.comparisonIso
  targetHomologyZeroPayload :=
    targetHomologyZeroPayloadOfTargetExactAtW803
      (cochainHasHomology_of_leftRightComparisonIsoW768 data.comparisonIso)
      data.targetExactAtPayload
  exactInputs := data.exactInputs

/-- W803 closed-map product evidence through target ExactAt-derived W664 data. -/
noncomputable def productEvidence_of_closedMapTargetExactAtW664TerminalRouteW803
    (data : MetrizableClosedMapTargetExactAtW664TerminalBranchDataW803) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapW664TerminalRouteW799
    (closedMapW664TerminalDataOfTargetExactAtW803 data)

/-!
W803 closed-embedding product evidence through target ExactAt-derived W664
data.
-/
noncomputable def
    productEvidence_of_closedEmbeddingTargetExactAtW664TerminalRouteW803
    (data : MetrizableClosedEmbeddingTargetExactAtW664TerminalBranchDataW803) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingW664TerminalRouteW799
    (closedEmbeddingW664TerminalDataOfTargetExactAtW803 data)

/-- W803 closed-map exact/stable evidence from target ExactAt-derived W664 data. -/
noncomputable def closedMapExactStableEvidenceOfTargetExactAtW664TerminalW803
    (data : MetrizableClosedMapTargetExactAtW664TerminalBranchDataW803) :
    MetrizableWppExactStableEvidenceW758 :=
  (productEvidence_of_closedMapTargetExactAtW664TerminalRouteW803
    data).exactStableEvidence

/-!
W803 closed-embedding exact/stable evidence from target ExactAt-derived W664
data.
-/
noncomputable def
    closedEmbeddingExactStableEvidenceOfTargetExactAtW664TerminalW803
    (data : MetrizableClosedEmbeddingTargetExactAtW664TerminalBranchDataW803) :
    MetrizableWppExactStableEvidenceW758 :=
  (productEvidence_of_closedEmbeddingTargetExactAtW664TerminalRouteW803
    data).exactStableEvidence

/-- W803 closed-map stable-certificate readiness. -/
theorem closedMapStableCertificateReadyOfTargetExactAtW664TerminalW803
    (data : MetrizableClosedMapTargetExactAtW664TerminalBranchDataW803) :
    (productEvidence_of_closedMapTargetExactAtW664TerminalRouteW803
      data).kernelCokernelStableCertificate.ready :=
  (productEvidence_of_closedMapTargetExactAtW664TerminalRouteW803
    data).kernelCokernelStableReady

/-- W803 closed-embedding stable-certificate readiness. -/
theorem closedEmbeddingStableCertificateReadyOfTargetExactAtW664TerminalW803
    (data : MetrizableClosedEmbeddingTargetExactAtW664TerminalBranchDataW803) :
    (productEvidence_of_closedEmbeddingTargetExactAtW664TerminalRouteW803
      data).kernelCokernelStableCertificate.ready :=
  (productEvidence_of_closedEmbeddingTargetExactAtW664TerminalRouteW803
    data).kernelCokernelStableReady

/-- W803 input names after target ExactAt data supplies the W664 payload. -/
def targetExactAtW664TerminalProductRouteInputNamesW803 : List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data",
    "target ExactAt realization data for exact-acyclic homotopy objects"]

theorem targetExactAtW664TerminalProductRouteInputNamesW803_count :
    targetExactAtW664TerminalProductRouteInputNamesW803.length = 3 :=
  rfl

structure MetrizableTargetExactAtW664TerminalRouteStateW803 : Type where
  seed : String
  declarations : List String
  payloadConversionResult : String
  terminalEvidenceResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetExactAtW664TerminalRouteStateW803 :
    MetrizableTargetExactAtW664TerminalRouteStateW803
    where
  seed := "w803-target-exactat-w664-terminal-route"
  declarations :=
    ["targetHomologyZeroPayloadOfTargetExactAtW803",
      "MetrizableClosedMapTargetExactAtW664TerminalBranchDataW803",
      "MetrizableClosedEmbeddingTargetExactAtW664TerminalBranchDataW803",
      "closedMapW664TerminalDataOfTargetExactAtW803",
      "closedEmbeddingW664TerminalDataOfTargetExactAtW803",
      "productEvidence_of_closedMapTargetExactAtW664TerminalRouteW803",
      "productEvidence_of_closedEmbeddingTargetExactAtW664TerminalRouteW803",
      "closedMapExactStableEvidenceOfTargetExactAtW664TerminalW803",
      "closedEmbeddingExactStableEvidenceOfTargetExactAtW664TerminalW803",
      "closedMapStableCertificateReadyOfTargetExactAtW664TerminalW803",
      "closedEmbeddingStableCertificateReadyOfTargetExactAtW664TerminalW803",
      "targetExactAtW664TerminalProductRouteInputNamesW803",
      "targetExactAtW664TerminalProductRouteInputNamesW803_count"]
  payloadConversionResult :=
    "proved: target ExactAt data plus W768-derived homology supplies W664 data"
  terminalEvidenceResult :=
    "proved: target ExactAt-derived W664 data feed W799 terminal evidence"
  replacedInputs :=
    ["explicit W664 target homology-zero payload"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "construct target ExactAt realization data for exact-acyclic homotopy\
        objects"]
  productSuccessClaimed := false

theorem currentW803TargetExactAtW664TerminalRoute_productSuccess :
    (have state := currentMetrizableTargetExactAtW664TerminalRouteStateW803;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
