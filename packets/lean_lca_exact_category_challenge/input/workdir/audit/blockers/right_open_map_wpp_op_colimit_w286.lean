import LeanLCAExactChallenge.LCA.ExactCategory
import Mathlib.Algebra.Homology.ShortComplex.Limits

/-!
W286: right open-map WPP-op colimit boundary.

This parent-owned audit file reimplements the useful support signal from W286.
It narrows the remaining right-open-map field to an explicit topological LCA
colimit API: the induced map between the `X₂` and `X₃` component colimits of a
WPP-op short-complex diagram is open when all component right maps are open.

No product-completion claim is made here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace RightOpenMapWppOpColimitW286

/-- Closure of the right open-map field under the chosen WPP-op colimit. -/
abbrev rightOpenMap_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          IsOpenMap (cs.pt.g : cs.pt.X₂ → cs.pt.X₃)

/--
Explicit topological LCA colimit API boundary for the right map.

The inputs are only the two degreewise colimit facts for the source and target
of the right maps, plus openness of the diagram's component right maps.
-/
abbrev openMap_walkingParallelPairOp_colimitMap_boundary : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit ((ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤
        MetrizableLCA.{0}).mapCocone cs) →
        IsColimit ((ShortComplex.π₃ : ShortComplex MetrizableLCA.{0} ⥤
          MetrizableLCA.{0}).mapCocone cs) →
          (∀ j : WalkingParallelPairᵒᵖ,
            IsOpenMap ((S.obj j).g : (S.obj j).X₂ → (S.obj j).X₃)) →
            IsOpenMap (cs.pt.g : cs.pt.X₂ → cs.pt.X₃)

/--
The explicit topological colimit-open-map boundary supplies the W305/W307
right-open-map field.
-/
theorem rightOpenMap_walkingParallelPairOp_colimitClosure_of_colimitMapBoundary
    (hboundary : openMap_walkingParallelPairOp_colimitMap_boundary) :
    rightOpenMap_walkingParallelPairOp_colimitClosure := by
  intro S cs hcs hS
  exact hboundary S cs
    (isColimitOfPreserves
      (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}) hcs)
    (isColimitOfPreserves
      (ShortComplex.π₃ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}) hcs)
    (fun j => (hS j).open_map)

/-- Machine-readable frontier state for W286. -/
structure RightOpenMapWppOpColimitState : Type where
  seed : String
  selectedBoundary : String
  provedConsumer : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W286 boundary state. -/
def currentRightOpenMapWppOpColimitState :
    RightOpenMapWppOpColimitState where
  seed := "w286-20260520T164318Z-75f9e2b44a4e3109"
  selectedBoundary :=
    "openMap_walkingParallelPairOp_colimitMap_boundary"
  provedConsumer :=
    "rightOpenMap_walkingParallelPairOp_colimitClosure_of_colimitMapBoundary"
  remainingInputs :=
    ["topological LCA API: WPP-op colimits preserve openness of the induced map",
      "degreewise source and target cocones are supplied by ShortComplex.π₂/π₃ colimit preservation"]
  productSuccessClaimed := false

theorem currentRightOpenMapWppOpColimitState_productSuccess :
    currentRightOpenMapWppOpColimitState.productSuccessClaimed = false := rfl

/-- Named declarations checked by this audit file. -/
def rightOpenMapWppOpColimitDeclarationNames : List String :=
  ["rightOpenMap_walkingParallelPairOp_colimitClosure",
    "openMap_walkingParallelPairOp_colimitMap_boundary",
    "rightOpenMap_walkingParallelPairOp_colimitClosure_of_colimitMapBoundary",
    "currentRightOpenMapWppOpColimitState"]

theorem rightOpenMapWppOpColimitDeclarationNames_count :
    rightOpenMapWppOpColimitDeclarationNames.length = 4 := rfl

section Checks

#check rightOpenMap_walkingParallelPairOp_colimitClosure
#check openMap_walkingParallelPairOp_colimitMap_boundary
#check rightOpenMap_walkingParallelPairOp_colimitClosure_of_colimitMapBoundary
#check currentRightOpenMapWppOpColimitState
#check currentRightOpenMapWppOpColimitState_productSuccess
#check rightOpenMapWppOpColimitDeclarationNames
#check rightOpenMapWppOpColimitDeclarationNames_count
#check ShortComplex.π₂
#check ShortComplex.π₃
#check isColimitOfPreserves

end Checks

end RightOpenMapWppOpColimitW286

end LeanLCAExactChallenge
