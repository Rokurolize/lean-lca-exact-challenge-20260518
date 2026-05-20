import LeanLCAExactChallenge.LCA.ExactCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-!
W309: categorical right-map input for W305.

This file discharges the categorical epi input isolated by W305.  The proof uses
`Limits.colim.map_epi'`: the right map of the colimit short complex is the
colimit-induced map of the natural transformation `π₂Toπ₃`, and every component
is epi because each source short complex is strict short exact.

No product-completion claim is made here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpRightMapEpiOpenW309

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

/--
The colimit right map is epi because it is induced by a natural transformation
whose components are epi.
-/
theorem rightMapEpi_walkingParallelPairOp_colimitClosure_direct :
    rightMapEpi_walkingParallelPairOp_colimitClosure := by
  intro S cs hcs hS
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

/-- Machine-readable frontier state for W309. -/
structure WppOpRightMapEpiOpenState : Type where
  seed : String
  selectedInput : String
  provedInput : String
  proofRoute : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W309 boundary state. -/
def currentWppOpRightMapEpiOpenState : WppOpRightMapEpiOpenState where
  seed := "w309-worker-20260521T0130Z"
  selectedInput := "rightMapEpi_walkingParallelPairOp_colimitClosure"
  provedInput := "rightMapEpi_walkingParallelPairOp_colimitClosure_direct"
  proofRoute :=
    "Limits.colim.map_epi' applied to the componentwise ShortComplex right-map natural transformation"
  remainingInputs := ["rightOpenMap_walkingParallelPairOp_colimitClosure"]
  productSuccessClaimed := false

theorem currentWppOpRightMapEpiOpenState_productSuccess :
    currentWppOpRightMapEpiOpenState.productSuccessClaimed = false := rfl

/-- Named declarations checked by this audit file. -/
def wppOpRightMapEpiOpenDeclarationNames : List String :=
  ["rightMapEpi_walkingParallelPairOp_colimitClosure",
    "rightMapEpi_walkingParallelPairOp_colimitClosure_direct",
    "currentWppOpRightMapEpiOpenState"]

theorem wppOpRightMapEpiOpenDeclarationNames_count :
    wppOpRightMapEpiOpenDeclarationNames.length = 3 := rfl

section Checks

#check rightMapEpi_walkingParallelPairOp_colimitClosure
#check rightMapEpi_walkingParallelPairOp_colimitClosure_direct
#check currentWppOpRightMapEpiOpenState
#check currentWppOpRightMapEpiOpenState_productSuccess
#check wppOpRightMapEpiOpenDeclarationNames
#check wppOpRightMapEpiOpenDeclarationNames_count
#check colim.map_epi'
#check ShortComplex.π₂Toπ₃
#check isColimitOfPreserves
#check AddCommGrpCat.epi_iff_surjective

end Checks

end WppOpRightMapEpiOpenW309

end LeanLCAExactChallenge
