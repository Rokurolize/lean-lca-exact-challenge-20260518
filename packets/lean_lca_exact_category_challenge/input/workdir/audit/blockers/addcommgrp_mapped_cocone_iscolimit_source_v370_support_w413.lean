import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Homology.ShortComplex.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
W413: mapped-cocone `IsColimit` source support for W410.

This standalone audit file isolates the missing source for W410's input
`hMapped : IsColimit (selectedForgottenTargetMappedCocone S cs)`.  A colimit
proof for the original WPP-op cocone maps through the short-complex forgetful
functor under the explicit preservation assumption for that diagram, then
whiskers along the ordinary-to-op equivalence of `WalkingParallelPair`.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpMappedCoconeIsColimitSourceV370SupportW413

open AddCommGrpSnakeInputDifferenceCokernel
open WppOpExactAcyclicFrontierConsolidatedW318

/-- The functor forgetting a short complex of metrizable LCA groups to abelian groups. -/
abbrev forgottenShortComplexFunctor :
    ShortComplex MetrizableLCA.{0} ⥤ ShortComplex AddCommGrpCat.{0} :=
  (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).mapShortComplex

/-- The ordinary forgotten diagram associated to the WPP-op short-complex diagram. -/
abbrev selectedForgottenTargetOrdinaryDiagram
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    WalkingParallelPair ⥤ ShortComplex AddCommGrpCat.{0} :=
  walkingParallelPairOpEquiv.functor ⋙ S ⋙ forgottenShortComplexFunctor

/--
The W410-shaped mapped cocone over the ordinary `WalkingParallelPair` diagram.

This is W410's hand-expanded cocone: its legs are the original WPP-op cocone
legs mapped by the short-complex forgetful functor after transporting ordinary
WPP indices through `walkingParallelPairOpEquiv`.
-/
def selectedForgottenTargetMappedCocone
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    Cocone (selectedForgottenTargetOrdinaryDiagram S) :=
  { pt := cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})
    ι :=
      { app := fun j =>
          forgottenShortComplexFunctor.map (cs.ι.app (walkingParallelPairOpEquiv.functor.obj j))
        naturality := fun {j j'} f => by
          simpa only [Functor.comp_obj, Functor.comp_map, Functor.const_obj_obj,
            Functor.const_obj_map, Category.comp_id] using
            congrArg forgottenShortComplexFunctor.map
              (cs.w (walkingParallelPairOpEquiv.functor.map f)) } }

/--
The W410 input source: an original WPP-op colimit cocone becomes a colimit of
the ordinary forgotten mapped cocone under the weakest local preservation
assumption, namely preservation of this one diagram by
`forgottenShortComplexFunctor`.
-/
def selectedForgottenTargetMappedCoconeIsColimitOfPreserves
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S)
    [PreservesColimit S forgottenShortComplexFunctor]
    (hcs : IsColimit cs) :
    IsColimit (selectedForgottenTargetMappedCocone S cs) := by
  change
    IsColimit
      ((forgottenShortComplexFunctor.mapCocone cs).whisker walkingParallelPairOpEquiv.functor)
  exact
    (PreservesColimit.preserves (F := forgottenShortComplexFunctor) hcs).some.whiskerEquivalence
      walkingParallelPairOpEquiv

/-- A W410-shaped consumer: any construction needing `hMapped` can be fed from `hcs`. -/
def consumeW410MappedCoconeInputOfOriginalColimit
    {α : Sort _}
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S)
    [PreservesColimit S forgottenShortComplexFunctor]
    (hcs : IsColimit cs)
    (consume :
      IsColimit (selectedForgottenTargetMappedCocone S cs) → α) : α :=
  consume (selectedForgottenTargetMappedCoconeIsColimitOfPreserves S cs hcs)

/-- W413 checked support state. -/
structure AddCommGrpMappedCoconeIsColimitSourceV370SupportState : Type where
  seed : String
  checkedConstructors : List String
  mappedCoconeIsColimitSourceResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpMappedCoconeIsColimitSourceV370SupportState :
    AddCommGrpMappedCoconeIsColimitSourceV370SupportState where
  seed := "f463a8e92b7fe3180cb4dad5"
  checkedConstructors :=
    ["selectedForgottenTargetMappedCoconeIsColimitOfPreserves",
      "consumeW410MappedCoconeInputOfOriginalColimit"]
  mappedCoconeIsColimitSourceResult := "proved"
  remainingInputs := []
  productSuccessClaimed := false

theorem currentAddCommGrpMappedCoconeIsColimitSourceV370SupportState_productSuccess :
    currentAddCommGrpMappedCoconeIsColimitSourceV370SupportState.productSuccessClaimed = false :=
  rfl

section Checks

#check selectedForgottenTargetMappedCocone
#check selectedForgottenTargetMappedCoconeIsColimitOfPreserves
#check consumeW410MappedCoconeInputOfOriginalColimit
#check currentAddCommGrpMappedCoconeIsColimitSourceV370SupportState_productSuccess

end Checks

end AddCommGrpMappedCoconeIsColimitSourceV370SupportW413

end LeanLCAExactChallenge
