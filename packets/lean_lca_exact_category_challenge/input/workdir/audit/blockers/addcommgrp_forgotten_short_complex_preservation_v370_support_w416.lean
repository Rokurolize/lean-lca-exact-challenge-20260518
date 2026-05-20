import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Homology.ShortComplex.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
W416: preservation-source support for the short-complex forgetful functor.

This standalone audit file isolates the source of W413's local assumption
`[PreservesColimit S forgottenShortComplexFunctor]`.  The useful checked bridge
is the standard mathlib instance from preservation of all colimits of the WPP-op
shape to preservation of the selected diagram.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpForgottenShortComplexPreservationV370SupportW416

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

This is W413's hand-expanded cocone: its legs are the original WPP-op cocone
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
W413's local source theorem: an original WPP-op colimit cocone becomes a colimit
of the ordinary forgotten mapped cocone under preservation of this one diagram
by `forgottenShortComplexFunctor`.
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

/--
Shape-level WPP-op colimit preservation supplies W413's one-diagram
preservation assumption by typeclass search.
-/
theorem forgottenShortComplexPreservesSelectedDiagramOfShape
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    [PreservesColimitsOfShape WalkingParallelPairᵒᵖ forgottenShortComplexFunctor] :
    PreservesColimit S forgottenShortComplexFunctor :=
  inferInstance

/--
The W413 mapped-cocone source theorem with only the WPP-op shape-level
preservation assumption exposed to downstream callers.
-/
def selectedForgottenTargetMappedCoconeIsColimitOfShapePreserves
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S)
    [PreservesColimitsOfShape WalkingParallelPairᵒᵖ forgottenShortComplexFunctor]
    (hcs : IsColimit cs) :
    IsColimit (selectedForgottenTargetMappedCocone S cs) :=
  selectedForgottenTargetMappedCoconeIsColimitOfPreserves S cs hcs

/--
A W410-shaped consumer that no longer needs to mention the one-diagram
preservation assumption directly.
-/
def consumeW410MappedCoconeInputOfShapePreserves
    {α : Sort _}
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S)
    [PreservesColimitsOfShape WalkingParallelPairᵒᵖ forgottenShortComplexFunctor]
    (hcs : IsColimit cs)
    (consume :
      IsColimit (selectedForgottenTargetMappedCocone S cs) → α) : α :=
  consume (selectedForgottenTargetMappedCoconeIsColimitOfShapePreserves S cs hcs)

/-- W416 checked support state. -/
structure AddCommGrpForgottenShortComplexPreservationV370SupportState : Type where
  seed : String
  checkedConstructors : List String
  preservationSourceResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpForgottenShortComplexPreservationV370SupportState :
    AddCommGrpForgottenShortComplexPreservationV370SupportState where
  seed := "stipple-cobalt-7391"
  checkedConstructors :=
    ["forgottenShortComplexPreservesSelectedDiagramOfShape",
      "selectedForgottenTargetMappedCoconeIsColimitOfShapePreserves",
      "consumeW410MappedCoconeInputOfShapePreserves"]
  preservationSourceResult := "proved"
  remainingInputs :=
    ["main thread must provide or prove `[PreservesColimitsOfShape WalkingParallelPairᵒᵖ forgottenShortComplexFunctor]`"]
  productSuccessClaimed := false

theorem currentAddCommGrpForgottenShortComplexPreservationV370SupportState_productSuccess :
    currentAddCommGrpForgottenShortComplexPreservationV370SupportState.productSuccessClaimed = false :=
  rfl

section Checks

#check forgottenShortComplexPreservesSelectedDiagramOfShape
#check selectedForgottenTargetMappedCoconeIsColimitOfShapePreserves
#check consumeW410MappedCoconeInputOfShapePreserves
#check currentAddCommGrpForgottenShortComplexPreservationV370SupportState_productSuccess

end Checks

end AddCommGrpForgottenShortComplexPreservationV370SupportW416

end LeanLCAExactChallenge
