import LeanLCAExactChallenge.Derived.TargetIsoStrictRealizationTerminalProductRoute

/-!
W810 consolidates W809's strict homotopy-object realization input with the
older W651 exact-acyclic iso-closure realization input. Since every exact
acyclic homotopy object lies in its isomorphism closure by the reflexive
isomorphism, W651 realization data supplies the W809 terminal route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/--
W651 iso-closure strict realization data supplies the W809 exact-acyclic
homotopy-object strict realization input.
-/
theorem strictRealizationOfIsoClosureRealizationW810
    (realize :
      MetrizableExactAcyclicIsoClosureTrianglehIso13RealizationInputW651) :
    MetrizableExactAcyclicHomotopyObjectTrianglehIso13RealizationW783 := by
  intro T hT h₁ h₃
  exact realize hT ⟨_, h₁, ⟨Iso.refl T.obj₁⟩⟩
    ⟨_, h₃, ⟨Iso.refl T.obj₃⟩⟩

/--
W810 closed-map branch data replaces W809's homotopy-object strict realization
field with W651 iso-closure realization data.
-/
structure MetrizableClosedMapIsoClosureRealizationTerminalBranchDataW810 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  isoClosureRealization :
    MetrizableExactAcyclicIsoClosureTrianglehIso13RealizationInputW651
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735

/--
W810 closed-embedding branch data replaces W809's homotopy-object strict
realization field with W651 iso-closure realization data.
-/
structure MetrizableClosedEmbeddingIsoClosureRealizationTerminalBranchDataW810 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  isoClosureRealization :
    MetrizableExactAcyclicIsoClosureTrianglehIso13RealizationInputW651
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735

/-- W810 closed-map iso-closure realization data converted to W809 data. -/
noncomputable def closedMapStrictDataOfIsoClosureRealizationW810
    (data : MetrizableClosedMapIsoClosureRealizationTerminalBranchDataW810) :
    MetrizableClosedMapStrictRealizationTerminalBranchDataW809
    where
  comparisonIso := data.comparisonIso
  trianglehRealization :=
    strictRealizationOfIsoClosureRealizationW810 data.isoClosureRealization
  exactInputs := data.exactInputs

/-- W810 closed-embedding iso-closure realization data converted to W809 data. -/
noncomputable def closedEmbeddingStrictDataOfIsoClosureRealizationW810
    (data : MetrizableClosedEmbeddingIsoClosureRealizationTerminalBranchDataW810) :
    MetrizableClosedEmbeddingStrictRealizationTerminalBranchDataW809
    where
  comparisonIso := data.comparisonIso
  trianglehRealization :=
    strictRealizationOfIsoClosureRealizationW810 data.isoClosureRealization
  exactInputs := data.exactInputs

/-- W810 closed-map product evidence through W651 iso-closure realization. -/
noncomputable def productEvidence_of_closedMapIsoClosureRealizationTerminalRouteW810
    (data : MetrizableClosedMapIsoClosureRealizationTerminalBranchDataW810) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapStrictRealizationTerminalRouteW809
    (closedMapStrictDataOfIsoClosureRealizationW810 data)

/--
W810 closed-embedding product evidence through W651 iso-closure realization.
-/
noncomputable def
    productEvidence_of_closedEmbeddingIsoClosureRealizationTerminalRouteW810
    (data : MetrizableClosedEmbeddingIsoClosureRealizationTerminalBranchDataW810) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingStrictRealizationTerminalRouteW809
    (closedEmbeddingStrictDataOfIsoClosureRealizationW810 data)

def isoClosureRealizationTerminalProductRouteInputNamesW810 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data",
    "W651 exact-acyclic homotopy-object iso-closure strict realization data"]

theorem isoClosureRealizationTerminalProductRouteInputNamesW810_count :
    isoClosureRealizationTerminalProductRouteInputNamesW810.length = 3 :=
  rfl

structure MetrizableIsoClosureRealizationTerminalRouteStateW810 :
    Type where
  seed : String
  declarations : List String
  strictRealizationReductionResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableIsoClosureRealizationTerminalRouteStateW810 :
    MetrizableIsoClosureRealizationTerminalRouteStateW810
    where
  seed := "w810-iso-closure-realization-terminal-route"
  declarations :=
    ["strictRealizationOfIsoClosureRealizationW810",
      "MetrizableClosedMapIsoClosureRealizationTerminalBranchDataW810",
      "MetrizableClosedEmbeddingIsoClosureRealizationTerminalBranchDataW810",
      "closedMapStrictDataOfIsoClosureRealizationW810",
      "closedEmbeddingStrictDataOfIsoClosureRealizationW810",
      "productEvidence_of_closedMapIsoClosureRealizationTerminalRouteW810",
      "productEvidence_of_closedEmbeddingIsoClosureRealizationTerminalRouteW810",
      "isoClosureRealizationTerminalProductRouteInputNamesW810",
      "isoClosureRealizationTerminalProductRouteInputNamesW810_count"]
  strictRealizationReductionResult :=
    "proved: W651 iso-closure strict realization supplies W809 strict\
      homotopy-object realization by reflexive endpoint isomorphisms"
  closedMapResult :=
    "proved: closed-map iso-closure realization branch data feed W809 terminal\
      product evidence"
  closedEmbeddingResult :=
    "proved: closed-embedding iso-closure realization branch data feed W809\
      terminal product evidence"
  replacedInputs :=
    ["exact-acyclic homotopy-object strict triangleh realization data"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "construct W651 exact-acyclic homotopy-object iso-closure strict\
        realization data"]
  productSuccessClaimed := false

theorem currentW810IsoClosureRealizationTerminalRoute_productSuccess :
    (have state :=
      currentMetrizableIsoClosureRealizationTerminalRouteStateW810;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
