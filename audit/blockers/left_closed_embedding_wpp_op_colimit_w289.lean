import LeanLCAExactChallenge.LCA.ExactCategory

/-!
W289: left closed-embedding boundary for WPP-op strict short-exact colimits.

W307 identified the `leftClosedEmbedding_walkingParallelPairOp_colimitClosure`
field as one of the concrete inputs equivalent to the remaining strict-short-
exact WPP-op colimit closure.  This parent-owned audit file reduces that field
to the smaller categorical/topological preservation input actually needed on
the left maps: a WPP-op colimit of `ShortComplex MetrizableLCA` preserves closed
embeddings for the degree-one morphisms.

No product-completion claim is made here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace LeftClosedEmbeddingWppOpColimitW289

/-- The W307 left closed-embedding field restated locally for this audit file. -/
abbrev leftClosedEmbedding_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          IsClosedEmbedding (cs.pt.f : cs.pt.X₁ → cs.pt.X₂)

/--
The explicit remaining preservation input for W289: if every left map in a
`WalkingParallelPairᵒᵖ` diagram of short complexes is a closed embedding, then
the left map of any colimit point is a closed embedding.
-/
abbrev wppOp_colimit_preserves_leftClosedEmbedding : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ,
          IsClosedEmbedding ((S.obj j).f : (S.obj j).X₁ → (S.obj j).X₂)) →
          IsClosedEmbedding (cs.pt.f : cs.pt.X₁ → cs.pt.X₂)

/--
The W289 preservation input is enough for W307's left closed-embedding field.
The strictness assumptions are consumed only through their `closed_inclusion`
projections, leaving the real missing theorem as a closed-embedding preservation
statement rather than the full strict-exact closure.
-/
theorem leftClosedEmbedding_walkingParallelPairOp_colimitClosure_of_preserves_leftClosedEmbedding
    (hpres : wppOp_colimit_preserves_leftClosedEmbedding) :
    leftClosedEmbedding_walkingParallelPairOp_colimitClosure := by
  intro S cs hcs hS
  exact hpres S cs hcs (fun j => (hS j).closed_inclusion)

/-- Machine-readable frontier state for W289. -/
structure LeftClosedEmbeddingWppOpColimitState : Type where
  seed : String
  selectedRoute : String
  checkedBoundary : String
  provedConsumers : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W289 boundary state. -/
def currentLeftClosedEmbeddingWppOpColimitState :
    LeftClosedEmbeddingWppOpColimitState where
  seed := "w289-20260520T165211Z-19ec004b39201a57"
  selectedRoute := "closed-embedding-field-boundary-consumer"
  checkedBoundary :=
    "wppOp_colimit_preserves_leftClosedEmbedding"
  provedConsumers :=
    ["leftClosedEmbedding_walkingParallelPairOp_colimitClosure_of_preserves_leftClosedEmbedding"]
  remainingInputs :=
    ["prove that WalkingParallelPairᵒᵖ colimits of ShortComplex MetrizableLCA preserve closed embeddings of left maps"]
  productSuccessClaimed := false

theorem currentLeftClosedEmbeddingWppOpColimitState_productSuccess :
    currentLeftClosedEmbeddingWppOpColimitState.productSuccessClaimed = false := rfl

/-- Named declarations produced by this audit file. -/
def leftClosedEmbeddingWppOpColimitDeclarationNames : List String :=
  ["leftClosedEmbedding_walkingParallelPairOp_colimitClosure",
    "wppOp_colimit_preserves_leftClosedEmbedding",
    "leftClosedEmbedding_walkingParallelPairOp_colimitClosure_of_preserves_leftClosedEmbedding",
    "currentLeftClosedEmbeddingWppOpColimitState"]

theorem leftClosedEmbeddingWppOpColimitDeclarationNames_count :
    leftClosedEmbeddingWppOpColimitDeclarationNames.length = 4 := rfl

section Checks

#check wppOp_colimit_preserves_leftClosedEmbedding
#check leftClosedEmbedding_walkingParallelPairOp_colimitClosure
#check leftClosedEmbedding_walkingParallelPairOp_colimitClosure_of_preserves_leftClosedEmbedding
#check currentLeftClosedEmbeddingWppOpColimitState
#check currentLeftClosedEmbeddingWppOpColimitState_productSuccess
#check leftClosedEmbeddingWppOpColimitDeclarationNames
#check leftClosedEmbeddingWppOpColimitDeclarationNames_count
#check MetrizableLCA.StrictShortExact.closed_inclusion

end Checks

end LeftClosedEmbeddingWppOpColimitW289

end LeanLCAExactChallenge
