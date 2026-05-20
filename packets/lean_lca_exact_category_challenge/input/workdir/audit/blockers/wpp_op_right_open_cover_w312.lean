import LeanLCAExactChallenge.LCA.ExactCategory

/-!
W312: a checked identity-cover construction for the W311 right-open-map cover.

The full W311 cover still requires constructing quotient/coequalizer presentation
data for a WPP-op colimit.  This file proves a smaller field-complete cover
constructor: once the colimit short complex itself is known to be strict short
exact, the identity maps on the middle and right terms provide a
`RightOpenMapColimitCover`.

This is intentionally nonterminal progress.  It isolates the remaining work as
the actual strictness/open-map construction for the WPP-op colimit point, rather
than any additional packaging problem in `RightOpenMapColimitCover`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpRightOpenCoverW312

/--
The W311 cover shape, repeated locally because audit blocker files are checked
standalone rather than imported as compiled package modules.
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

/-- W311 cover target, repeated locally for standalone checking. -/
abbrev rightOpenMapColimitCover_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          Nonempty (RightOpenMapColimitCover S cs)

/--
If the colimit point short complex is already strict short exact, it supplies
the W311 cover by taking both cover maps to be identities and the aggregate map
to be the colimit right map.
-/
def rightOpenMapColimitCoverOfStrictColimitPoint
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S} (hpt : MetrizableLCA.strictShortExact cs.pt) :
    RightOpenMapColimitCover S cs where
  Q₂ := cs.pt.X₂
  Q₃ := cs.pt.X₃
  q₂ := 𝟙 cs.pt.X₂
  q₃ := 𝟙 cs.pt.X₃
  G := cs.pt.g
  q₂_surjective := by
    intro x
    exact ⟨x, rfl⟩
  G_open := hpt.open_map
  q₃_open := by
    simpa using (IsOpenMap.id : IsOpenMap (id : cs.pt.X₃ → cs.pt.X₃))
  comm := by
    simp

/--
W312 narrowed target: the W311 cover target follows from strict short exactness
of the chosen WPP-op colimit point.
-/
theorem rightOpenMapColimitCover_walkingParallelPairOp_colimitClosure_of_strictColimitPoint
    (hstrict :
      ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
        (cs : Cocone S),
          IsColimit cs →
            (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
              MetrizableLCA.strictShortExact cs.pt) :
    rightOpenMapColimitCover_walkingParallelPairOp_colimitClosure := by
  intro S cs hcs hS
  exact ⟨rightOpenMapColimitCoverOfStrictColimitPoint (hstrict S cs hcs hS)⟩

/-- Machine-readable frontier state for W312. -/
structure WppOpRightOpenCoverState : Type where
  seed : String
  selectedInput : String
  checkedConstructor : String
  narrowedInput : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W312 boundary state. -/
def currentWppOpRightOpenCoverState : WppOpRightOpenCoverState where
  seed := "w312-worker-20260521T0000Z"
  selectedInput := "rightOpenMapColimitCover_walkingParallelPairOp_colimitClosure"
  checkedConstructor := "rightOpenMapColimitCoverOfStrictColimitPoint"
  narrowedInput :=
    "strict short exactness of the chosen WPP-op colimit point"
  remainingInputs :=
    ["construct strictShortExact cs.pt from the concrete WPP-op finite-colimit/coequalizer presentation",
      "or construct quotient/coequalizer cover data with an open aggregate map directly"]
  productSuccessClaimed := false

theorem currentWppOpRightOpenCoverState_productSuccess :
    currentWppOpRightOpenCoverState.productSuccessClaimed = false := rfl

/-- Named declarations checked by this audit file. -/
def wppOpRightOpenCoverDeclarationNames : List String :=
  ["rightOpenMapColimitCoverOfStrictColimitPoint",
    "rightOpenMapColimitCover_walkingParallelPairOp_colimitClosure_of_strictColimitPoint",
    "currentWppOpRightOpenCoverState"]

theorem wppOpRightOpenCoverDeclarationNames_count :
    wppOpRightOpenCoverDeclarationNames.length = 3 := rfl

section Checks

#check RightOpenMapColimitCover
#check rightOpenMapColimitCoverOfStrictColimitPoint
#check rightOpenMapColimitCover_walkingParallelPairOp_colimitClosure_of_strictColimitPoint
#check currentWppOpRightOpenCoverState
#check currentWppOpRightOpenCoverState_productSuccess
#check wppOpRightOpenCoverDeclarationNames
#check wppOpRightOpenCoverDeclarationNames_count

end Checks

end WppOpRightOpenCoverW312

end LeanLCAExactChallenge
