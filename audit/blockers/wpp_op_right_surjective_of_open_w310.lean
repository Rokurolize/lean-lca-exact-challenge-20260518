import LeanLCAExactChallenge.LCA.ExactCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-!
W310: right-surjectivity closure now only needs the right-open-map field.

W305 reduced right-surjectivity of the WPP-op colimit right map to:

* the right-open-map field; and
* categorical epi of the same right map.

W309 proves the categorical epi input directly using `Limits.colim.map_epi'`.
This file combines the two facts so the remaining right-surjectivity route has
only one explicit topological input: openness of the colimit right map.

No product-completion claim is made here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpRightSurjectiveOfOpenW310

/-- Closure of the right open-map field under the chosen WPP-op colimit. -/
abbrev rightOpenMap_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          IsOpenMap (cs.pt.g : cs.pt.X₂ → cs.pt.X₃)

/-- Closure of the right surjectivity field under the chosen WPP-op colimit. -/
abbrev rightSurjective_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          Function.Surjective (cs.pt.g : cs.pt.X₂ → cs.pt.X₃)

/-- The colimit right map is categorically epi. -/
theorem rightMapEpi_walkingParallelPairOp_colimitClosure_direct
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S)
    (hcs : IsColimit cs)
    (hS : ∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) :
    Epi cs.pt.g := by
  let φ : (S ⋙ ShortComplex.π₂) ⟶ (S ⋙ ShortComplex.π₃) :=
    { app := fun j => (S.obj j).g
      naturality := fun j j' f => (S.map f).comm₂₃ }
  haveI hφ : ∀ j, Epi (φ.app j) := fun j => by
    dsimp [φ]
    apply (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).epi_of_epi_map
    rw [AddCommGrpCat.epi_iff_surjective]
    exact (hS j).surjective
  exact colim.map_epi' φ (ShortComplex.π₂.mapCocone cs)
    (isColimitOfPreserves ShortComplex.π₃ hcs) cs.pt.g
    (fun j => by
      dsimp [φ]
      simpa using (cs.ι.app j).comm₂₃)

/--
The right-surjectivity field now follows from the right-open-map field alone.
-/
theorem rightSurjective_walkingParallelPairOp_colimitClosure_of_openMap
    (hopen : rightOpenMap_walkingParallelPairOp_colimitClosure) :
    rightSurjective_walkingParallelPairOp_colimitClosure := by
  intro S cs hcs hS
  haveI : Epi cs.pt.g :=
    rightMapEpi_walkingParallelPairOp_colimitClosure_direct S cs hcs hS
  exact MetrizableLCA.surjective_of_cokernelSubgroup_eq_top_of_isOpenMap cs.pt.g
    (MetrizableLCA.cokernelSubgroup_eq_top_of_cokernelπ_eq_zero cs.pt.g
      (MetrizableLCA.cokernelπ_eq_zero_of_epi cs.pt.g))
    (hopen S cs hcs hS)

/-- Machine-readable frontier state for W310. -/
structure WppOpRightSurjectiveOfOpenState : Type where
  seed : String
  provedInput : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W310 state. -/
def currentWppOpRightSurjectiveOfOpenState :
    WppOpRightSurjectiveOfOpenState where
  seed := "w310-parent-20260520T1635Z"
  provedInput := "rightSurjective_walkingParallelPairOp_colimitClosure_of_openMap"
  remainingInputs := ["rightOpenMap_walkingParallelPairOp_colimitClosure"]
  productSuccessClaimed := false

theorem currentWppOpRightSurjectiveOfOpenState_productSuccess :
    currentWppOpRightSurjectiveOfOpenState.productSuccessClaimed = false := rfl

section Checks

#check rightOpenMap_walkingParallelPairOp_colimitClosure
#check rightSurjective_walkingParallelPairOp_colimitClosure
#check rightMapEpi_walkingParallelPairOp_colimitClosure_direct
#check rightSurjective_walkingParallelPairOp_colimitClosure_of_openMap
#check currentWppOpRightSurjectiveOfOpenState
#check currentWppOpRightSurjectiveOfOpenState_productSuccess
#check colim.map_epi'
#check MetrizableLCA.surjective_of_cokernelSubgroup_eq_top_of_isOpenMap

end Checks

end WppOpRightSurjectiveOfOpenW310

end LeanLCAExactChallenge
