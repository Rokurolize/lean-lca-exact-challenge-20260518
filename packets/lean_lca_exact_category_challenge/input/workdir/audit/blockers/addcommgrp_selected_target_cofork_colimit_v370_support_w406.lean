import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Homology.ShortComplex.Limits
import Mathlib.CategoryTheory.Preadditive.Basic

/-!
W406: selected forgotten-target cofork colimit support.

This standalone audit file reduces W403's remaining selected-target cokernel
cofork colimit to the colimit of the forgotten WPP-op cocone after precomposing
by `walkingParallelPairOpEquiv.functor`.  The last non-local input is the
preservation/transport theorem that supplies that mapped cocone colimit from the
original `IsColimit cs`.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpSelectedTargetCoforkColimitV370SupportW406

open AddCommGrpSnakeInputDifferenceCokernel
open WppOpExactAcyclicFrontierConsolidatedW318

/-- The functor forgetting a short complex of metrizable LCA groups to abelian groups. -/
abbrev forgottenShortComplexFunctor :
    ShortComplex MetrizableLCA.{0} ⥤ ShortComplex AddCommGrpCat.{0} :=
  (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).mapShortComplex

/-- The ordinary source object of a WPP diagram, transported into `WalkingParallelPairᵒᵖ`. -/
abbrev ordinarySourceIndex : WalkingParallelPairᵒᵖ :=
  walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.zero

/-- The ordinary target object of a WPP diagram, transported into `WalkingParallelPairᵒᵖ`. -/
abbrev ordinaryTargetIndex : WalkingParallelPairᵒᵖ :=
  walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.one

/-- The selected forgotten-target cocone leg: the WPP-op leg at the ordinary target object. -/
def selectedForgottenTargetCoconeLeg
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    (S.obj ordinaryTargetIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) ⟶
      cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) :=
  forgottenShortComplexFunctor.map (cs.ι.app ordinaryTargetIndex)

/-- The forgotten ordinary-left arrow of the WPP-op short-complex diagram. -/
def selectedForgottenLeft
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (S.obj ordinarySourceIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) ⟶
      (S.obj ordinaryTargetIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) :=
  forgottenShortComplexFunctor.map
    (S.map (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.left))

/-- The forgotten ordinary-right arrow of the WPP-op short-complex diagram. -/
def selectedForgottenRight
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (S.obj ordinarySourceIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) ⟶
      (S.obj ordinaryTargetIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) :=
  forgottenShortComplexFunctor.map
    (S.map (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.right))

/-- Cocone naturality says the selected target leg coequalizes the two WPP arrows. -/
theorem selectedForgottenTargetCoconeLeg_parallel_pair
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    selectedForgottenLeft S ≫ selectedForgottenTargetCoconeLeg S cs =
      selectedForgottenRight S ≫ selectedForgottenTargetCoconeLeg S cs := by
  change
    forgottenShortComplexFunctor.map
        (S.map (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.left)) ≫
        forgottenShortComplexFunctor.map (cs.ι.app ordinaryTargetIndex) =
      forgottenShortComplexFunctor.map
        (S.map (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.right)) ≫
        forgottenShortComplexFunctor.map (cs.ι.app ordinaryTargetIndex)
  rw [← forgottenShortComplexFunctor.map_comp, ← forgottenShortComplexFunctor.map_comp]
  congr 1
  exact (cs.w (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.left)).trans
    (cs.w (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.right)).symm

/-- The selected target leg is a `Cofork` for the parallel pair of selected maps. -/
def selectedForgottenTargetCofork
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    Cofork (selectedForgottenLeft S) (selectedForgottenRight S) :=
  Cofork.ofπ (selectedForgottenTargetCoconeLeg S cs)
    (selectedForgottenTargetCoconeLeg_parallel_pair S cs)

/-- The selected target leg is a cofork map for the same parallel pair `(left - right, 0)`. -/
theorem selectedForgottenTargetCoconeLeg_w
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    (selectedForgottenLeft S - selectedForgottenRight S) ≫
        selectedForgottenTargetCoconeLeg S cs = 0 := by
  rw [Preadditive.sub_comp, selectedForgottenTargetCoconeLeg_parallel_pair S cs, sub_self]

/-- The selected leg as an explicit cokernel cofork. -/
def selectedForgottenTargetCokernelCofork
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    CokernelCofork (selectedForgottenLeft S - selectedForgottenRight S) :=
  CokernelCofork.ofπ (selectedForgottenTargetCoconeLeg S cs)
    (selectedForgottenTargetCoconeLeg_w S cs)

/--
The forgotten cocone over the ordinary `WalkingParallelPair` obtained by
precomposing the WPP-op diagram by `walkingParallelPairOpEquiv.functor`.
-/
def selectedForgottenTargetMappedCocone
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    Cocone (walkingParallelPairOpEquiv.functor ⋙ S ⋙ forgottenShortComplexFunctor) where
  pt := cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})
  ι :=
    { app := fun j =>
        forgottenShortComplexFunctor.map (cs.ι.app (walkingParallelPairOpEquiv.functor.obj j))
      naturality := fun {j j'} f => by
        simpa only [Functor.comp_obj, Functor.comp_map, Functor.const_obj_obj,
          Functor.const_obj_map, Category.comp_id] using
          congrArg forgottenShortComplexFunctor.map
            (cs.w (walkingParallelPairOpEquiv.functor.map f)) }

@[simp]
theorem selectedForgottenTargetMappedCocone_ι_one
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    (selectedForgottenTargetMappedCocone S cs).ι.app WalkingParallelPair.one =
      selectedForgottenTargetCoconeLeg S cs :=
  rfl

@[simp]
theorem selectedForgottenTargetCofork_π
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    (selectedForgottenTargetCofork S cs).π = selectedForgottenTargetCoconeLeg S cs :=
  rfl

/-- Any colimit proof for the selected `Cofork` gives W403's remaining cokernel colimit. -/
def selectedForgottenTargetCokernelColimitOfCoforkColimit
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S)
    (hCofork : IsColimit (selectedForgottenTargetCofork S cs)) :
    IsColimit (selectedForgottenTargetCokernelCofork S cs) :=
  IsColimit.ofIsoColimit
    (Preadditive.isColimitCokernelCoforkOfCofork hCofork)
    (Cofork.ext (Iso.refl _) (by
      simp [selectedForgottenTargetCokernelCofork, selectedForgottenTargetCofork]))

/--
Checked adapter for W403's remaining proof.  Its only mathematical input is the
precise preservation/transport theorem: the selected forgotten-target cofork
obtained from `cs` is colimiting.
-/
def selectedForgottenTargetCokernelColimitOfSelectedCoforkColimit
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S)
    (hCofork : IsColimit (selectedForgottenTargetCofork S cs)) :
    IsColimit (selectedForgottenTargetCokernelCofork S cs) :=
  selectedForgottenTargetCokernelColimitOfCoforkColimit S cs hCofork

/-- W403-shaped exact selected-leg input, repeated locally for a checked consumer. -/
structure ExactSelectedForgottenTargetCoforkInputW403Shape
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 where
  hForgotten :
    IsColimit (selectedForgottenTargetCokernelCofork S cs)

/-- The selected-cofork colimit theorem feeds W403's selected exact input shape. -/
def exactSelectedForgottenTargetCoforkInputW403OfSelectedCoforkColimit
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S)
    (hCofork : IsColimit (selectedForgottenTargetCofork S cs)) :
    ExactSelectedForgottenTargetCoforkInputW403Shape S cs where
  hForgotten := selectedForgottenTargetCokernelColimitOfSelectedCoforkColimit S cs hCofork

/-- W400 concrete selected-target input shape, with source/target transport already selected. -/
structure SelectedTargetConcreteForgottenLegInputW400Shape
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} (u v : L₁ ⟶ L₂)
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 where
  sourceIso : L₁ ≅ (S.obj ordinarySourceIndex).map
    (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})
  targetIso : L₂ ≅ (S.obj ordinaryTargetIndex).map
    (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})
  u_eq_selected :
    u = sourceIso.hom ≫ selectedForgottenLeft S ≫ targetIso.inv
  v_eq_selected :
    v = sourceIso.hom ≫ selectedForgottenRight S ≫ targetIso.inv
  hForgotten :
    IsColimit (selectedForgottenTargetCokernelCofork S cs)

/-- W398-shaped exact selected target cofork-map input. -/
structure SelectedTargetCoforkMapInputW398Shape
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 where
  qForgotten :
    (S.obj ordinaryTargetIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) ⟶
      cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})
  wForgotten :
    (selectedForgottenLeft S - selectedForgottenRight S) ≫ qForgotten = 0 := by cat_disch
  hForgotten : IsColimit (CokernelCofork.ofπ qForgotten wForgotten)

/-- The selected-cofork colimit theorem feeds the W398 cofork-map shape. -/
def selectedTargetCoforkMapInputW398OfSelectedCoforkColimit
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S)
    (hCofork : IsColimit (selectedForgottenTargetCofork S cs)) :
    SelectedTargetCoforkMapInputW398Shape S cs where
  qForgotten := selectedForgottenTargetCoconeLeg S cs
  wForgotten := selectedForgottenTargetCoconeLeg_w S cs
  hForgotten := selectedForgottenTargetCokernelColimitOfSelectedCoforkColimit S cs hCofork

/-- W406 checked support state. -/
structure AddCommGrpSelectedTargetCoforkColimitV370SupportState : Type where
  seed : String
  checkedConstructors : List String
  selectedTargetCoforkColimitResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpSelectedTargetCoforkColimitV370SupportState :
    AddCommGrpSelectedTargetCoforkColimitV370SupportState where
  seed := "MrWu7hPzhWC5swW3Tm3hnHWE"
  checkedConstructors :=
    ["selectedForgottenTargetMappedCocone",
      "selectedForgottenTargetCofork",
      "selectedForgottenTargetCokernelCofork",
      "selectedForgottenTargetCokernelColimitOfCoforkColimit",
      "selectedForgottenTargetCokernelColimitOfSelectedCoforkColimit",
      "exactSelectedForgottenTargetCoforkInputW403OfSelectedCoforkColimit",
      "selectedTargetCoforkMapInputW398OfSelectedCoforkColimit"]
  selectedTargetCoforkColimitResult := "partial"
  remainingInputs :=
    ["prove IsColimit (selectedForgottenTargetCofork S cs), typically by preserving the WPP-op colimit cs along forgottenShortComplexFunctor and transporting across walkingParallelPairOpEquiv.functor to the selected cofork"]
  productSuccessClaimed := false

theorem currentAddCommGrpSelectedTargetCoforkColimitV370SupportState_productSuccess :
    currentAddCommGrpSelectedTargetCoforkColimitV370SupportState.productSuccessClaimed = false := rfl

section Checks

#check selectedForgottenTargetMappedCocone
#check selectedForgottenTargetCofork
#check selectedForgottenTargetCokernelCofork
#check selectedForgottenTargetCokernelColimitOfCoforkColimit
#check selectedForgottenTargetCokernelColimitOfSelectedCoforkColimit
#check ExactSelectedForgottenTargetCoforkInputW403Shape
#check exactSelectedForgottenTargetCoforkInputW403OfSelectedCoforkColimit
#check SelectedTargetConcreteForgottenLegInputW400Shape
#check SelectedTargetCoforkMapInputW398Shape
#check selectedTargetCoforkMapInputW398OfSelectedCoforkColimit
#check currentAddCommGrpSelectedTargetCoforkColimitV370SupportState_productSuccess

end Checks

end AddCommGrpSelectedTargetCoforkColimitV370SupportW406

end LeanLCAExactChallenge
