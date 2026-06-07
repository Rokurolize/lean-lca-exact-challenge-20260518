import LeanLCAExactChallenge.Derived.TargetExactAtW664TerminalProductRoute
import LeanLCAExactChallenge.Derived.TargetIsoRealizationTrianglehSelectedW461RowsProductRoute
import LeanLCAExactChallenge.Derived.TargetHomologyZeroExactInputsClosedRangeProductRoute

/-!
W808 converts W784 target-isomorphism realization data into the W803 target
ExactAt terminal route, using W768 homology existence and W790/W696 forgetful
homology preservation from the concrete W735 exact-input branch.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-!
Target-isomorphism realization gives exact acyclicity of the selected target
object; homology existence plus forgetful homology preservation turns that into
degreewise ExactAt data.
-/
theorem targetExactAtPayloadOfTargetIsoRealizationW808
    (hasHomology :
      ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ), K.HasHomology i)
    (forgetPreservesHomology :
      (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).PreservesHomology)
    (realize : MetrizableExactAcyclicHomotopyObjectTargetIsoRealizationW784) :
    MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785 := by
  intro T hT h₁ h₃
  rcases realize hT h₁ h₃ with
    ⟨K, L, Lexact, f, e₁, e₃, eL, comm, hLexact⟩
  exact
    ⟨K, L, Lexact, f, e₁, e₃, eL, comm,
      exactAt_of_exactAcyclic_metrizableLCA
        hasHomology forgetPreservesHomology hLexact⟩

/-- W808 extracts forgetful homology preservation from closed-map W735 inputs. -/
@[reducible]
def forgetPreservesHomologyOfClosedMapExactInputsW808
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).PreservesHomology :=
  (metrizableExactAtKernelCokernelConditionedTopologyInputs_of_closedRangeEndpointTopologyW696
    (closedRangeEndpointTopologyOfClosedMapExactInputsW790 exactInputs)).forgetPreservesHomology

/-- W808 extracts forgetful homology preservation from closed-embedding W735 inputs. -/
@[reducible]
def forgetPreservesHomologyOfClosedEmbeddingExactInputsW808
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).PreservesHomology :=
  (metrizableExactAtKernelCokernelConditionedTopologyInputs_of_closedRangeEndpointTopologyW696
    (closedRangeEndpointTopologyOfClosedEmbeddingExactInputsW790
      exactInputs)).forgetPreservesHomology

structure MetrizableClosedMapTargetIsoTerminalBranchDataW808 : Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  targetIsoRealization :
    MetrizableExactAcyclicHomotopyObjectTargetIsoRealizationW784
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735

structure MetrizableClosedEmbeddingTargetIsoTerminalBranchDataW808 : Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  targetIsoRealization :
    MetrizableExactAcyclicHomotopyObjectTargetIsoRealizationW784
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735

/-- W808 closed-map target-isomorphism data converted to W803 data. -/
noncomputable def closedMapTargetExactAtDataOfTargetIsoW808
    (data : MetrizableClosedMapTargetIsoTerminalBranchDataW808) :
    MetrizableClosedMapTargetExactAtW664TerminalBranchDataW803
    where
  comparisonIso := data.comparisonIso
  targetExactAtPayload :=
    targetExactAtPayloadOfTargetIsoRealizationW808
      (cochainHasHomology_of_leftRightComparisonIsoW768 data.comparisonIso)
      (forgetPreservesHomologyOfClosedMapExactInputsW808 data.exactInputs)
      data.targetIsoRealization
  exactInputs := data.exactInputs

/-- W808 closed-embedding target-isomorphism data converted to W803 data. -/
noncomputable def closedEmbeddingTargetExactAtDataOfTargetIsoW808
    (data : MetrizableClosedEmbeddingTargetIsoTerminalBranchDataW808) :
    MetrizableClosedEmbeddingTargetExactAtW664TerminalBranchDataW803
    where
  comparisonIso := data.comparisonIso
  targetExactAtPayload :=
    targetExactAtPayloadOfTargetIsoRealizationW808
      (cochainHasHomology_of_leftRightComparisonIsoW768 data.comparisonIso)
      (forgetPreservesHomologyOfClosedEmbeddingExactInputsW808 data.exactInputs)
      data.targetIsoRealization
  exactInputs := data.exactInputs

/-- W808 closed-map product evidence through target-isomorphism data. -/
noncomputable def productEvidence_of_closedMapTargetIsoTerminalRouteW808
    (data : MetrizableClosedMapTargetIsoTerminalBranchDataW808) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapTargetExactAtW664TerminalRouteW803
    (closedMapTargetExactAtDataOfTargetIsoW808 data)

/-- W808 closed-embedding product evidence through target-isomorphism data. -/
noncomputable def productEvidence_of_closedEmbeddingTargetIsoTerminalRouteW808
    (data : MetrizableClosedEmbeddingTargetIsoTerminalBranchDataW808) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingTargetExactAtW664TerminalRouteW803
    (closedEmbeddingTargetExactAtDataOfTargetIsoW808 data)

/-!
W808 closed-map target-isomorphism data as W803/W799 direct stable data.
-/
noncomputable def directFiniteShapeStableDataOfClosedMapTargetIsoTerminalW808
    (data : MetrizableClosedMapTargetIsoTerminalBranchDataW808) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapTargetExactAtW664TerminalW803
    (closedMapTargetExactAtDataOfTargetIsoW808 data)

/-!
W808 closed-embedding target-isomorphism data as W803/W799 direct stable data.
-/
noncomputable def
    directFiniteShapeStableDataOfClosedEmbeddingTargetIsoTerminalW808
    (data : MetrizableClosedEmbeddingTargetIsoTerminalBranchDataW808) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingTargetExactAtW664TerminalW803
    (closedEmbeddingTargetExactAtDataOfTargetIsoW808 data)

/-! W808 closed-map target-isomorphism data as stable-boundary inputs. -/
noncomputable def stableBoundaryInputsOfClosedMapTargetIsoTerminalW808
    (data : MetrizableClosedMapTargetIsoTerminalBranchDataW808) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapTargetExactAtW664TerminalW803
    (closedMapTargetExactAtDataOfTargetIsoW808 data)

/-!
W808 closed-embedding target-isomorphism data as stable-boundary inputs.
-/
noncomputable def stableBoundaryInputsOfClosedEmbeddingTargetIsoTerminalW808
    (data : MetrizableClosedEmbeddingTargetIsoTerminalBranchDataW808) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingTargetExactAtW664TerminalW803
    (closedEmbeddingTargetExactAtDataOfTargetIsoW808 data)

/-! W808 closed-map target-isomorphism data passes the stable boundary. -/
noncomputable def acceptedStableOfClosedMapTargetIsoTerminalW808
    (data : MetrizableClosedMapTargetIsoTerminalBranchDataW808) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapTargetExactAtW664TerminalW803
    (closedMapTargetExactAtDataOfTargetIsoW808 data)

/-!
W808 closed-embedding target-isomorphism data passes the stable boundary.
-/
noncomputable def acceptedStableOfClosedEmbeddingTargetIsoTerminalW808
    (data : MetrizableClosedEmbeddingTargetIsoTerminalBranchDataW808) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingTargetExactAtW664TerminalW803
    (closedEmbeddingTargetExactAtDataOfTargetIsoW808 data)

/-!
W808 closed-map target-isomorphism data produces the stable-boundary package.
-/
noncomputable def boundedDerivedOfClosedMapTargetIsoTerminalStableBoundaryW808
    (data : MetrizableClosedMapTargetIsoTerminalBranchDataW808) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapTargetExactAtW664TerminalStableBoundaryW803
    (closedMapTargetExactAtDataOfTargetIsoW808 data)

/-!
W808 closed-embedding target-isomorphism data produces the stable-boundary
package.
-/
noncomputable def
    boundedDerivedOfClosedEmbeddingTargetIsoTerminalStableBoundaryW808
    (data : MetrizableClosedEmbeddingTargetIsoTerminalBranchDataW808) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingTargetExactAtW664TerminalStableBoundaryW803
    (closedEmbeddingTargetExactAtDataOfTargetIsoW808 data)

def targetIsoToTargetExactAtTerminalInputNamesW808 : List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data",
    "exact-acyclic homotopy-object target-isomorphism realization data"]

theorem targetIsoToTargetExactAtTerminalInputNamesW808_count :
    targetIsoToTargetExactAtTerminalInputNamesW808.length = 3 :=
  rfl

structure MetrizableTargetIsoToTargetExactAtTerminalRouteStateW808 :
    Type where
  seed : String
  declarations : List String
  payloadConversionResult : String
  terminalEvidenceResult : String
  stableBoundaryResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetIsoToTargetExactAtTerminalRouteStateW808 :
    MetrizableTargetIsoToTargetExactAtTerminalRouteStateW808
    where
  seed := "w808-target-iso-to-target-exactat-terminal-route"
  declarations :=
    ["targetExactAtPayloadOfTargetIsoRealizationW808",
      "forgetPreservesHomologyOfClosedMapExactInputsW808",
      "forgetPreservesHomologyOfClosedEmbeddingExactInputsW808",
      "MetrizableClosedMapTargetIsoTerminalBranchDataW808",
      "MetrizableClosedEmbeddingTargetIsoTerminalBranchDataW808",
      "closedMapTargetExactAtDataOfTargetIsoW808",
      "closedEmbeddingTargetExactAtDataOfTargetIsoW808",
      "productEvidence_of_closedMapTargetIsoTerminalRouteW808",
      "productEvidence_of_closedEmbeddingTargetIsoTerminalRouteW808",
      "directFiniteShapeStableDataOfClosedMapTargetIsoTerminalW808",
      "directFiniteShapeStableDataOfClosedEmbeddingTargetIsoTerminalW808",
      "stableBoundaryInputsOfClosedMapTargetIsoTerminalW808",
      "stableBoundaryInputsOfClosedEmbeddingTargetIsoTerminalW808",
      "acceptedStableOfClosedMapTargetIsoTerminalW808",
      "acceptedStableOfClosedEmbeddingTargetIsoTerminalW808",
      "boundedDerivedOfClosedMapTargetIsoTerminalStableBoundaryW808",
      "boundedDerivedOfClosedEmbeddingTargetIsoTerminalStableBoundaryW808",
      "targetIsoToTargetExactAtTerminalInputNamesW808",
      "targetIsoToTargetExactAtTerminalInputNamesW808_count"]
  payloadConversionResult :=
    "proved: W784 target-isomorphism realization plus W768/W790 data supplies\
      W803 target ExactAt payload data"
  terminalEvidenceResult :=
    "proved: target-isomorphism-derived target ExactAt data feed W803 terminal\
      product evidence"
  stableBoundaryResult :=
    "proved: target-isomorphism-derived W803 data expose the stable-boundary\
      gate"
  replacedInputs :=
    ["exact-acyclic homotopy-object target ExactAt realization data"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "construct exact-acyclic homotopy-object target-isomorphism realization\
        data"]
  productSuccessClaimed := false

theorem currentW808TargetIsoToTargetExactAtTerminalRoute_productSuccess :
    (have state :=
      currentMetrizableTargetIsoToTargetExactAtTerminalRouteStateW808;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
