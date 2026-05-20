import LeanLCAExactChallenge.LCA.ExactCategory
import Mathlib.Algebra.Homology.ShortComplex.Limits

/-!
W297: component closed-embedding coequalizer boundary.

W294 reduced the W289/W318 left closed-embedding input to a component-level
map between the `X₁` and `X₂` colimits of a `WalkingParallelPairᵒᵖ` diagram of
short complexes.  This file removes the remaining `ShortComplex` structure from
that input: the missing theorem is a pure LCA statement for a natural
transformation between two `WalkingParallelPairᵒᵖ` diagrams.

For a walking parallel pair, these colimits are coequalizer-shaped.  The checked
consumer below shows that a coequalizer/colimit-map theorem for closed
embeddings of such natural transformations is exactly sufficient for W294's
component boundary, and hence for W289's left closed-embedding preservation
boundary.

No product-completion claim is made.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace ComponentClosedEmbeddingCoequalizerSupportW297

/-- W289/W318's left closed-embedding preservation boundary, restated locally. -/
abbrev wppOp_colimit_preserves_leftClosedEmbedding : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ,
          IsClosedEmbedding ((S.obj j).f : (S.obj j).X₁ → (S.obj j).X₂)) →
          IsClosedEmbedding (cs.pt.f : cs.pt.X₁ → cs.pt.X₂)

/--
W294's component-level input, restated locally.  It still mentions short
complexes only to obtain the two component cocones and the candidate map.
-/
abbrev wppOp_component_colimitMap_preserves_closedEmbedding : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit ((ShortComplex.π₁ : ShortComplex MetrizableLCA.{0} ⥤
        MetrizableLCA.{0}).mapCocone cs) →
        IsColimit ((ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤
          MetrizableLCA.{0}).mapCocone cs) →
          (∀ j : WalkingParallelPairᵒᵖ,
            IsClosedEmbedding ((S.obj j).f : (S.obj j).X₁ → (S.obj j).X₂)) →
            (∀ j : WalkingParallelPairᵒᵖ,
              ((ShortComplex.π₁ : ShortComplex MetrizableLCA.{0} ⥤
                MetrizableLCA.{0}).mapCocone cs).ι.app j ≫ cs.pt.f =
                (S.obj j).f ≫
                  ((ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤
                    MetrizableLCA.{0}).mapCocone cs).ι.app j) →
              IsClosedEmbedding (cs.pt.f : cs.pt.X₁ → cs.pt.X₂)

/--
The narrowed pure component/coequalizer boundary.  Given a natural
transformation `α : X ⟶ Y` between two `WalkingParallelPairᵒᵖ` diagrams in
`MetrizableLCA`, the induced map between colimit points should be a closed
embedding when every component of `α` is a closed embedding.

This is the smallest checked API this worker isolates: it has no reference to
short complexes, exactness, or the WPP-op acyclicity goal, only the
coequalizer-shaped component colimit map.
-/
abbrev wppOp_lca_colimitMap_preserves_closedEmbedding : Prop :=
  ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
      IsColimit cx →
        IsColimit cy →
          (∀ j : WalkingParallelPairᵒᵖ,
            IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
            (∀ j : WalkingParallelPairᵒᵖ, cx.ι.app j ≫ φ = α.app j ≫ cy.ι.app j) →
              IsClosedEmbedding (φ : cx.pt → cy.pt)

/--
The pure component/coequalizer boundary implies W294's component boundary.
-/
theorem wppOp_component_colimitMap_preserves_closedEmbedding_of_lca_colimitMap
    (hcomponent : wppOp_lca_colimitMap_preserves_closedEmbedding) :
    wppOp_component_colimitMap_preserves_closedEmbedding := by
  intro S cs h₁ h₂ hclosed hcompat
  let α : S ⋙ (ShortComplex.π₁ : ShortComplex MetrizableLCA.{0} ⥤
      MetrizableLCA.{0}) ⟶
      S ⋙ (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤
        MetrizableLCA.{0}) :=
    { app := fun j => (S.obj j).f
      naturality := fun _ _ f => (S.map f).comm₁₂ }
  exact hcomponent
    (S ⋙ (ShortComplex.π₁ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}))
    (S ⋙ (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}))
    α
    ((ShortComplex.π₁ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}).mapCocone cs)
    ((ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}).mapCocone cs)
    cs.pt.f
    h₁ h₂ hclosed hcompat

/--
The W294 component boundary implies the W289/W318 left closed-embedding
preservation boundary.
-/
theorem wppOp_colimit_preserves_leftClosedEmbedding_of_component_colimitMap
    (hcomponent : wppOp_component_colimitMap_preserves_closedEmbedding) :
    wppOp_colimit_preserves_leftClosedEmbedding := by
  intro S cs hcs hclosed
  exact hcomponent S cs
    (isColimitOfPreserves
      (ShortComplex.π₁ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}) hcs)
    (isColimitOfPreserves
      (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}) hcs)
    hclosed
    (fun j => (cs.ι.app j).comm₁₂)

/--
Direct checked consumer from the pure component/coequalizer boundary to the
W289/W318 left closed-embedding preservation boundary.
-/
theorem wppOp_colimit_preserves_leftClosedEmbedding_of_lca_colimitMap
    (hcomponent : wppOp_lca_colimitMap_preserves_closedEmbedding) :
    wppOp_colimit_preserves_leftClosedEmbedding :=
  wppOp_colimit_preserves_leftClosedEmbedding_of_component_colimitMap
    (wppOp_component_colimitMap_preserves_closedEmbedding_of_lca_colimitMap hcomponent)

/-- Machine-readable W297 boundary state. -/
structure ComponentClosedEmbeddingCoequalizerSupportState : Type where
  seed : String
  selectedRoute : String
  checkedBoundary : String
  provedConsumers : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W297 state for downstream workers. -/
def currentComponentClosedEmbeddingCoequalizerSupportState :
    ComponentClosedEmbeddingCoequalizerSupportState where
  seed := "w297-20260520T173131Z-693ec043ec4f72fb"
  selectedRoute := "component-natural-transformation-coequalizer-boundary"
  checkedBoundary := "wppOp_lca_colimitMap_preserves_closedEmbedding"
  provedConsumers :=
    ["wppOp_component_colimitMap_preserves_closedEmbedding_of_lca_colimitMap",
      "wppOp_colimit_preserves_leftClosedEmbedding_of_component_colimitMap",
      "wppOp_colimit_preserves_leftClosedEmbedding_of_lca_colimitMap"]
  remainingInputs :=
    ["prove the pure MetrizableLCA WalkingParallelPairᵒᵖ coequalizer/colimit-map theorem: colimits of a natural transformation whose components are closed embeddings induce a closed embedding on colimit points",
      "the inspected local quotient/cokernel/pushout files expose closed-subgroup quotients and pushout closed embeddings, but no API showing that this coequalizer quotient map has closed image or is a topological embedding"]
  productSuccessClaimed := false

theorem currentComponentClosedEmbeddingCoequalizerSupportState_productSuccess :
    currentComponentClosedEmbeddingCoequalizerSupportState.productSuccessClaimed = false := rfl

/-- Named declarations produced by this audit file. -/
def componentClosedEmbeddingCoequalizerSupportDeclarationNames : List String :=
  ["wppOp_colimit_preserves_leftClosedEmbedding",
    "wppOp_component_colimitMap_preserves_closedEmbedding",
    "wppOp_lca_colimitMap_preserves_closedEmbedding",
    "wppOp_component_colimitMap_preserves_closedEmbedding_of_lca_colimitMap",
    "wppOp_colimit_preserves_leftClosedEmbedding_of_component_colimitMap",
    "wppOp_colimit_preserves_leftClosedEmbedding_of_lca_colimitMap",
    "currentComponentClosedEmbeddingCoequalizerSupportState"]

theorem componentClosedEmbeddingCoequalizerSupportDeclarationNames_count :
    componentClosedEmbeddingCoequalizerSupportDeclarationNames.length = 7 := rfl

section Checks

#check wppOp_colimit_preserves_leftClosedEmbedding
#check wppOp_component_colimitMap_preserves_closedEmbedding
#check wppOp_lca_colimitMap_preserves_closedEmbedding
#check wppOp_component_colimitMap_preserves_closedEmbedding_of_lca_colimitMap
#check wppOp_colimit_preserves_leftClosedEmbedding_of_component_colimitMap
#check wppOp_colimit_preserves_leftClosedEmbedding_of_lca_colimitMap
#check currentComponentClosedEmbeddingCoequalizerSupportState
#check currentComponentClosedEmbeddingCoequalizerSupportState_productSuccess
#check componentClosedEmbeddingCoequalizerSupportDeclarationNames
#check componentClosedEmbeddingCoequalizerSupportDeclarationNames_count
#check ShortComplex.π₁
#check ShortComplex.π₂
#check isColimitOfPreserves
#check WalkingParallelPair
#check HasCoequalizers

end Checks

end ComponentClosedEmbeddingCoequalizerSupportW297

end LeanLCAExactChallenge
