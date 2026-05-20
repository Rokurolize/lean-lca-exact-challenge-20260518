import LeanLCAExactChallenge.LCA.ExactCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-!
W311: narrowing the right-open-map field for WPP-op colimits.

W309 proves the categorical epi input for the right map of a WPP-op colimit, and
W310 shows that right-surjectivity follows once this right map is open.  This
file isolates a smaller, quotient-presentation-shaped input sufficient for the
remaining topological open-map field.

The intended next proof obligation is to instantiate `RightOpenMapColimitCover`
from the actual finite-colimit/coequalizer construction: `Q₂` should be a
surjective cover of the colimit middle term, `Q₃` should cover the colimit right
term by an open quotient map, and `G` should be the aggregate right map induced
from the component strict short-exact open maps.

No product-completion claim is made here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpRightOpenMapW311

/-- Closure of the right open-map field under the chosen WPP-op colimit. -/
abbrev rightOpenMap_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          IsOpenMap (cs.pt.g : cs.pt.X₂ → cs.pt.X₃)

/--
A quotient-presentation-shaped cover sufficient to prove that the colimit right
map is open.

The cover is deliberately stated independently of a specific coequalizer model.
For the expected WPP-op finite-colimit construction, `q₂` is the middle-term
quotient cover, `q₃` is the right-term quotient cover, and `G` is induced from
the component right maps.
-/
structure RightOpenMapColimitCover
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 2 where
  Q₂ : MetrizableLCA.{0}
  Q₃ : MetrizableLCA.{0}
  q₂ : Q₂ ⟶ cs.pt.X₂
  q₃ : Q₃ ⟶ cs.pt.X₃
  G : Q₂ ⟶ Q₃
  q₂_surjective : Function.Surjective (q₂ : Q₂ → cs.pt.X₂)
  G_open : IsOpenMap (G : Q₂ → Q₃)
  q₃_open : IsOpenMap (q₃ : Q₃ → cs.pt.X₃)
  comm : q₂ ≫ cs.pt.g = G ≫ q₃

/--
The original right-open-map field follows from the quotient-presentation cover.

This uses only the local topological lemma
`MetrizableLCA.isOpenMap_of_comp_surjective`: a map is open if it becomes open
after precomposition by a surjective cover.
-/
theorem rightOpenMap_of_colimitCover
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S} (hcover : RightOpenMapColimitCover S cs) :
    IsOpenMap (cs.pt.g : cs.pt.X₂ → cs.pt.X₃) := by
  have hcomp : IsOpenMap ((hcover.q₂ ≫ cs.pt.g : hcover.Q₂ ⟶ cs.pt.X₃) :
      hcover.Q₂ → cs.pt.X₃) := by
    rw [hcover.comm]
    exact hcover.q₃_open.comp hcover.G_open
  exact MetrizableLCA.isOpenMap_of_comp_surjective hcover.q₂ cs.pt.g
    hcover.q₂_surjective hcomp

/--
W311 narrowed target: it is enough to construct the cover data for every strict
short-exact WPP-op colimit.
-/
abbrev rightOpenMapColimitCover_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          Nonempty (RightOpenMapColimitCover S cs)

/--
The cover target is sufficient for the remaining right-open-map field.
-/
theorem rightOpenMap_walkingParallelPairOp_colimitClosure_of_cover
    (hcover : rightOpenMapColimitCover_walkingParallelPairOp_colimitClosure) :
    rightOpenMap_walkingParallelPairOp_colimitClosure := by
  intro S cs hcs hS
  rcases hcover S cs hcs hS with ⟨cover⟩
  exact rightOpenMap_of_colimitCover cover

/-- Machine-readable frontier state for W311. -/
structure WppOpRightOpenMapState : Type where
  seed : String
  selectedInput : String
  narrowedInput : String
  provedConsumer : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W311 boundary state. -/
def currentWppOpRightOpenMapState : WppOpRightOpenMapState where
  seed := "w311-worker-20260521T0133Z"
  selectedInput := "rightOpenMap_walkingParallelPairOp_colimitClosure"
  narrowedInput := "rightOpenMapColimitCover_walkingParallelPairOp_colimitClosure"
  provedConsumer := "rightOpenMap_walkingParallelPairOp_colimitClosure_of_cover"
  remainingInputs :=
    ["construct RightOpenMapColimitCover from the concrete WPP-op coequalizer/finite-colimit presentation"]
  productSuccessClaimed := false

theorem currentWppOpRightOpenMapState_productSuccess :
    currentWppOpRightOpenMapState.productSuccessClaimed = false := rfl

/-- Named declarations checked by this audit file. -/
def wppOpRightOpenMapDeclarationNames : List String :=
  ["rightOpenMap_walkingParallelPairOp_colimitClosure",
    "RightOpenMapColimitCover",
    "rightOpenMap_of_colimitCover",
    "rightOpenMapColimitCover_walkingParallelPairOp_colimitClosure",
    "rightOpenMap_walkingParallelPairOp_colimitClosure_of_cover",
    "currentWppOpRightOpenMapState"]

theorem wppOpRightOpenMapDeclarationNames_count :
    wppOpRightOpenMapDeclarationNames.length = 6 := rfl

section Checks

#check rightOpenMap_walkingParallelPairOp_colimitClosure
#check RightOpenMapColimitCover
#check rightOpenMap_of_colimitCover
#check rightOpenMapColimitCover_walkingParallelPairOp_colimitClosure
#check rightOpenMap_walkingParallelPairOp_colimitClosure_of_cover
#check currentWppOpRightOpenMapState
#check currentWppOpRightOpenMapState_productSuccess
#check wppOpRightOpenMapDeclarationNames
#check wppOpRightOpenMapDeclarationNames_count
#check MetrizableLCA.isOpenMap_of_comp_surjective
#check MetrizableLCA.quotientMap_openMap
#check colim.map_epi'

end Checks

end WppOpRightOpenMapW311

end LeanLCAExactChallenge
