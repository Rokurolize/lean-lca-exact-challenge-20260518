import LeanLCAExactChallenge.LCA.ExactCategory
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
W305: one strict short-exact WPP-op colimit field boundary.

W301 decomposes strict short-exact WPP-op colimit closure into four fields.  This
file advances the right-surjectivity field: in `MetrizableLCA`, surjectivity of
the colimit right map follows from the already-isolated right-open-map field plus
a categorical epi proof for the same colimit right map.

No product-completion claim is made here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpStrictShortExactColimitFieldW305

/-- Closure of the right open-map field under the chosen WPP-op colimit. -/
abbrev rightOpenMap_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          IsOpenMap (cs.pt.g : cs.pt.X₂ → cs.pt.X₃)

/--
Categorical epi closure needed for the right map of a WPP-op colimit of strict
short exact complexes.
-/
abbrev rightMapEpi_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          Epi cs.pt.g

/-- Closure of the right surjectivity field under the chosen WPP-op colimit. -/
abbrev rightSurjective_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          Function.Surjective (cs.pt.g : cs.pt.X₂ → cs.pt.X₃)

/--
The right-surjectivity field is reduced to the topological open-map field and a
categorical epi proof for the colimit right map.
-/
theorem rightSurjective_walkingParallelPairOp_colimitClosure_of_openMap_and_epi
    (hopen : rightOpenMap_walkingParallelPairOp_colimitClosure)
    (hepi : rightMapEpi_walkingParallelPairOp_colimitClosure) :
    rightSurjective_walkingParallelPairOp_colimitClosure := by
  intro S cs hcs hS
  haveI : Epi cs.pt.g := hepi S cs hcs hS
  exact MetrizableLCA.surjective_of_cokernelSubgroup_eq_top_of_isOpenMap cs.pt.g
    (MetrizableLCA.cokernelSubgroup_eq_top_of_cokernelπ_eq_zero cs.pt.g
      (MetrizableLCA.cokernelπ_eq_zero_of_epi cs.pt.g))
    (hopen S cs hcs hS)

/-- Machine-readable frontier state for W305. -/
structure WppOpStrictShortExactColimitFieldState : Type where
  seed : String
  selectedField : String
  provedConsumer : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W305 boundary state. -/
def currentWppOpStrictShortExactColimitFieldState :
    WppOpStrictShortExactColimitFieldState where
  seed := "w305-worker-20260520T1624Z"
  selectedField := "rightSurjective_walkingParallelPairOp_colimitClosure"
  provedConsumer :=
    "rightSurjective_walkingParallelPairOp_colimitClosure_of_openMap_and_epi"
  remainingInputs :=
    ["rightOpenMap_walkingParallelPairOp_colimitClosure",
      "rightMapEpi_walkingParallelPairOp_colimitClosure"]
  productSuccessClaimed := false

theorem currentWppOpStrictShortExactColimitFieldState_productSuccess :
    currentWppOpStrictShortExactColimitFieldState.productSuccessClaimed = false := rfl

/-- Named declarations checked by this audit file. -/
def wppOpStrictShortExactColimitFieldDeclarationNames : List String :=
  ["rightOpenMap_walkingParallelPairOp_colimitClosure",
    "rightMapEpi_walkingParallelPairOp_colimitClosure",
    "rightSurjective_walkingParallelPairOp_colimitClosure",
    "rightSurjective_walkingParallelPairOp_colimitClosure_of_openMap_and_epi",
    "currentWppOpStrictShortExactColimitFieldState"]

theorem wppOpStrictShortExactColimitFieldDeclarationNames_count :
    wppOpStrictShortExactColimitFieldDeclarationNames.length = 5 := rfl

section Checks

#check rightOpenMap_walkingParallelPairOp_colimitClosure
#check rightMapEpi_walkingParallelPairOp_colimitClosure
#check rightSurjective_walkingParallelPairOp_colimitClosure
#check rightSurjective_walkingParallelPairOp_colimitClosure_of_openMap_and_epi
#check currentWppOpStrictShortExactColimitFieldState
#check currentWppOpStrictShortExactColimitFieldState_productSuccess
#check wppOpStrictShortExactColimitFieldDeclarationNames
#check wppOpStrictShortExactColimitFieldDeclarationNames_count
#check MetrizableLCA.surjective_of_cokernelSubgroup_eq_top_of_isOpenMap
#check MetrizableLCA.cokernelSubgroup_eq_top_of_cokernelπ_eq_zero
#check MetrizableLCA.cokernelπ_eq_zero_of_epi

end Checks

end WppOpStrictShortExactColimitFieldW305

end LeanLCAExactChallenge
