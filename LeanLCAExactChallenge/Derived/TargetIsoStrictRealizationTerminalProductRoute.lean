import LeanLCAExactChallenge.Derived.TargetIsoToTargetExactAtTerminalProductRoute

/-!
W809 removes W808's target-isomorphism realization input as a separate named
premise: strict triangleh realization already supplies target-isomorphism
realization by choosing the exact target to be the displayed target and using
the reflexive isomorphism.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/--
Strict triangleh realization data supplies the target-isomorphism realization
data used by W808.
-/
theorem targetIsoRealizationOfTrianglehRealizationW809
    (realize :
      MetrizableExactAcyclicHomotopyObjectTrianglehIso13RealizationW783) :
    MetrizableExactAcyclicHomotopyObjectTargetIsoRealizationW784 := by
  intro T hT h₁ h₃
  rcases realize hT h₁ h₃ with ⟨K, L, f, e₁, e₃, comm, hL⟩
  exact ⟨K, L, L, f, e₁, e₃, Iso.refl L, comm, hL⟩

/--
W809 closed-map branch data replaces W808's target-isomorphism realization
field with the strict triangleh realization input.
-/
structure MetrizableClosedMapStrictRealizationTerminalBranchDataW809 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  trianglehRealization :
    MetrizableExactAcyclicHomotopyObjectTrianglehIso13RealizationW783
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735

/--
W809 closed-embedding branch data replaces W808's target-isomorphism
realization field with the strict triangleh realization input.
-/
structure MetrizableClosedEmbeddingStrictRealizationTerminalBranchDataW809 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  trianglehRealization :
    MetrizableExactAcyclicHomotopyObjectTrianglehIso13RealizationW783
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735

/-- W809 closed-map strict realization data converted to W808 data. -/
noncomputable def closedMapTargetIsoDataOfStrictRealizationW809
    (data : MetrizableClosedMapStrictRealizationTerminalBranchDataW809) :
    MetrizableClosedMapTargetIsoTerminalBranchDataW808
    where
  comparisonIso := data.comparisonIso
  targetIsoRealization :=
    targetIsoRealizationOfTrianglehRealizationW809 data.trianglehRealization
  exactInputs := data.exactInputs

/-- W809 closed-embedding strict realization data converted to W808 data. -/
noncomputable def closedEmbeddingTargetIsoDataOfStrictRealizationW809
    (data : MetrizableClosedEmbeddingStrictRealizationTerminalBranchDataW809) :
    MetrizableClosedEmbeddingTargetIsoTerminalBranchDataW808
    where
  comparisonIso := data.comparisonIso
  targetIsoRealization :=
    targetIsoRealizationOfTrianglehRealizationW809 data.trianglehRealization
  exactInputs := data.exactInputs

/-- W809 closed-map product evidence through strict triangleh realization. -/
noncomputable def productEvidence_of_closedMapStrictRealizationTerminalRouteW809
    (data : MetrizableClosedMapStrictRealizationTerminalBranchDataW809) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapTargetIsoTerminalRouteW808
    (closedMapTargetIsoDataOfStrictRealizationW809 data)

/-- W809 closed-embedding product evidence through strict triangleh realization. -/
noncomputable def productEvidence_of_closedEmbeddingStrictRealizationTerminalRouteW809
    (data : MetrizableClosedEmbeddingStrictRealizationTerminalBranchDataW809) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingTargetIsoTerminalRouteW808
    (closedEmbeddingTargetIsoDataOfStrictRealizationW809 data)

def strictRealizationTerminalProductRouteInputNamesW809 : List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data",
    "exact-acyclic homotopy-object strict triangleh realization data"]

theorem strictRealizationTerminalProductRouteInputNamesW809_count :
    strictRealizationTerminalProductRouteInputNamesW809.length = 3 :=
  rfl

structure MetrizableStrictRealizationTerminalRouteStateW809 : Type where
  seed : String
  declarations : List String
  targetIsoReductionResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableStrictRealizationTerminalRouteStateW809 :
    MetrizableStrictRealizationTerminalRouteStateW809
    where
  seed := "w809-strict-realization-terminal-route"
  declarations :=
    ["targetIsoRealizationOfTrianglehRealizationW809",
      "MetrizableClosedMapStrictRealizationTerminalBranchDataW809",
      "MetrizableClosedEmbeddingStrictRealizationTerminalBranchDataW809",
      "closedMapTargetIsoDataOfStrictRealizationW809",
      "closedEmbeddingTargetIsoDataOfStrictRealizationW809",
      "productEvidence_of_closedMapStrictRealizationTerminalRouteW809",
      "productEvidence_of_closedEmbeddingStrictRealizationTerminalRouteW809",
      "strictRealizationTerminalProductRouteInputNamesW809",
      "strictRealizationTerminalProductRouteInputNamesW809_count"]
  targetIsoReductionResult :=
    "proved: strict triangleh realization supplies W808 target-isomorphism\
      realization by reflexive target isomorphism"
  closedMapResult :=
    "proved: closed-map strict realization branch data feed W808 terminal\
      product evidence"
  closedEmbeddingResult :=
    "proved: closed-embedding strict realization branch data feed W808 terminal\
      product evidence"
  replacedInputs :=
    ["exact-acyclic homotopy-object target-isomorphism realization data"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "construct exact-acyclic homotopy-object strict triangleh realization\
        data"]
  productSuccessClaimed := false

theorem currentW809StrictRealizationTerminalRoute_productSuccess :
    (have state := currentMetrizableStrictRealizationTerminalRouteStateW809;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
