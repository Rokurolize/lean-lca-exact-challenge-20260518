import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Homology.ShortComplex.Limits

/-!
W403: selected forgotten-target WPP-op cocone leg support.

This standalone audit file identifies the concrete WPP-op leg left open by W400:
the leg at `walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.one`, i.e.
the ordinary codomain object of the parallel pair.  It also proves the reusable
same-parallel-pair cofork equation for that selected leg directly from cocone
naturality.  The cokernel-colimit proof remains an explicit input when the
consumer needs a full W400 `ConcreteForgottenTargetLegInputW400`.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpForgottenTargetCoconeLegV370SupportW403

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

/-- The selected target leg is the `j = one` instance of W400's concrete cocone leg. -/
theorem selectedForgottenTargetCoconeLeg_eq_concreteLeg
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    selectedForgottenTargetCoconeLeg S cs =
      forgottenShortComplexFunctor.map (cs.ι.app ordinaryTargetIndex) :=
  rfl

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
Checked adapter for W400's remaining frontier.  Once downstream code identifies
its `L₁`, `L₂`, `u`, and `v` with the selected WPP-op source, target, left, and
right data, the only remaining mathematical input is that the selected cofork is
a colimit.
-/
structure SelectedForgottenTargetLegInputW403
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

/-- The W400 concrete quotient map induced by the selected target leg. -/
def SelectedForgottenTargetLegInputW403.qForgotten
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S} (I : SelectedForgottenTargetLegInputW403 u v S cs) :
    L₂ ⟶ cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) :=
  I.targetIso.hom ≫ selectedForgottenTargetCoconeLeg S cs

/-- The W400 concrete leg formula for the selected ordinary-target index. -/
theorem SelectedForgottenTargetLegInputW403.qForgotten_eq_selected
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S} (I : SelectedForgottenTargetLegInputW403 u v S cs) :
    I.qForgotten = I.targetIso.hom ≫ selectedForgottenTargetCoconeLeg S cs :=
  rfl

/--
Exact selected-leg W398-shaped input.  This is the checked adapter before any
external source/target isomorphism transport: the map, equation, and remaining
colimit proof all refer to the concrete WPP-op target leg.
-/
structure ExactSelectedForgottenTargetCoforkInputW403
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 where
  hForgotten :
    IsColimit (selectedForgottenTargetCokernelCofork S cs)

/-- The exact selected-leg input carries the concrete target quotient map. -/
def ExactSelectedForgottenTargetCoforkInputW403.qForgotten
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S} (_I : ExactSelectedForgottenTargetCoforkInputW403 S cs) :
    (S.obj ordinaryTargetIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) ⟶
      cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) :=
  selectedForgottenTargetCoconeLeg S cs

/-- The exact selected-leg input's cofork equation is exactly cocone naturality. -/
theorem ExactSelectedForgottenTargetCoforkInputW403.wForgotten
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S} (_I : ExactSelectedForgottenTargetCoforkInputW403 S cs) :
    (selectedForgottenLeft S - selectedForgottenRight S) ≫
        selectedForgottenTargetCoconeLeg S cs = 0 :=
  selectedForgottenTargetCoconeLeg_w S cs

/-- W403 checked support state. -/
structure AddCommGrpForgottenTargetCoconeLegV370SupportState : Type where
  seed : String
  selectedIndex : String
  checkedConstructors : List String
  forgottenTargetCoconeLegResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpForgottenTargetCoconeLegV370SupportState :
    AddCommGrpForgottenTargetCoconeLegV370SupportState where
  seed := "seed-20260520T223932Z-8409399a2754e28d"
  selectedIndex := "walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.one"
  checkedConstructors :=
    ["ordinaryTargetIndex",
      "selectedForgottenTargetCoconeLeg",
      "selectedForgottenLeft",
      "selectedForgottenRight",
      "selectedForgottenTargetCoconeLeg_parallel_pair",
      "selectedForgottenTargetCoconeLeg_w",
      "selectedForgottenTargetCokernelCofork",
      "SelectedForgottenTargetLegInputW403",
      "SelectedForgottenTargetLegInputW403.qForgotten",
      "ExactSelectedForgottenTargetCoforkInputW403",
      "ExactSelectedForgottenTargetCoforkInputW403.qForgotten",
      "ExactSelectedForgottenTargetCoforkInputW403.wForgotten"]
  forgottenTargetCoconeLegResult := "partial"
  remainingInputs :=
    ["identify downstream L₁/L₂/u/v with ordinarySourceIndex/ordinaryTargetIndex and selectedForgottenLeft/selectedForgottenRight",
      "prove IsColimit (selectedForgottenTargetCokernelCofork S cs) for the selected concrete target leg"]
  productSuccessClaimed := false

theorem currentAddCommGrpForgottenTargetCoconeLegV370SupportState_productSuccess :
    currentAddCommGrpForgottenTargetCoconeLegV370SupportState.productSuccessClaimed = false := rfl

section Checks

#check ordinarySourceIndex
#check ordinaryTargetIndex
#check selectedForgottenTargetCoconeLeg
#check selectedForgottenLeft
#check selectedForgottenRight
#check selectedForgottenTargetCoconeLeg_parallel_pair
#check selectedForgottenTargetCoconeLeg_w
#check selectedForgottenTargetCokernelCofork
#check SelectedForgottenTargetLegInputW403
#check SelectedForgottenTargetLegInputW403.qForgotten
#check SelectedForgottenTargetLegInputW403.qForgotten_eq_selected
#check ExactSelectedForgottenTargetCoforkInputW403
#check ExactSelectedForgottenTargetCoforkInputW403.qForgotten
#check ExactSelectedForgottenTargetCoforkInputW403.wForgotten
#check currentAddCommGrpForgottenTargetCoconeLegV370SupportState_productSuccess

end Checks

end AddCommGrpForgottenTargetCoconeLegV370SupportW403

end LeanLCAExactChallenge
