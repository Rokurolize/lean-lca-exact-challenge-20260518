import LeanLCAExactChallenge.LCA.ExactCategory

/-!
W315: isolating the W313/W314 `HasHomology` input for `MetrizableLCA`.

Mathlib's `ShortComplex` API has a category-level typeclass
`CategoryWithHomology C`, meaning every short complex in `C` has homology.  This
file checks the consumer from that category-level input to the
WPP-op-colimit-point `HasHomology` input required by W313/W314.

This deliberately does not claim that the existing `MetrizableLCA` kernel and
cokernel instances already synthesize `CategoryWithHomology MetrizableLCA`.
Mathlib's homology data requires the left and right homology data to be connected
by the canonical comparison isomorphism, so this remains a real input rather than
a mere instance-search packaging issue.  No product-success claim is made.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace MetrizableLCACategoryWithHomologyW315

/-- Homology availability for WPP-op colimit points in short complexes. -/
abbrev hasHomology_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          cs.pt.HasHomology

/-- A category-level homology instance supplies the W313/W314 colimit-point input. -/
theorem hasHomology_walkingParallelPairOp_colimitClosure_of_categoryWithHomology
    [CategoryWithHomology MetrizableLCA.{0}] :
    hasHomology_walkingParallelPairOp_colimitClosure := by
  intro S cs hcs hS
  infer_instance

/-- Machine-readable W315 frontier state. -/
structure MetrizableLCACategoryWithHomologyState : Type where
  seed : String
  provedInput : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W315 state for downstream workers. -/
def currentMetrizableLCACategoryWithHomologyState :
    MetrizableLCACategoryWithHomologyState where
  seed := "w315-parent-20260521T0230Z"
  provedInput :=
    "hasHomology_walkingParallelPairOp_colimitClosure_of_categoryWithHomology"
  remainingInputs :=
    ["CategoryWithHomology MetrizableLCA",
      "PreservesHomology for forget₂ MetrizableLCA AddCommGrpCat",
      "exact_walkingParallelPairOp_colimitClosure",
      "leftClosedEmbedding_walkingParallelPairOp_colimitClosure",
      "rightOpenMap_walkingParallelPairOp_colimitClosure"]
  productSuccessClaimed := false

theorem currentMetrizableLCACategoryWithHomologyState_productSuccess :
    currentMetrizableLCACategoryWithHomologyState.productSuccessClaimed = false := rfl

section Checks

#check CategoryWithHomology MetrizableLCA.{0}
#check hasHomology_walkingParallelPairOp_colimitClosure
#check hasHomology_walkingParallelPairOp_colimitClosure_of_categoryWithHomology
#check currentMetrizableLCACategoryWithHomologyState
#check currentMetrizableLCACategoryWithHomologyState_productSuccess
#check ShortComplex.HomologyData
#check ShortComplex.HasHomology.mk'

end Checks

end MetrizableLCACategoryWithHomologyW315

end LeanLCAExactChallenge
