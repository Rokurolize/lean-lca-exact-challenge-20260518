import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel
import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Homology.ShortComplex.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
W446: selected AddCommGrp target cokernel colimit from one selected cokernel
preservation input.

This isolates the dependency that W435 routed through finite/global cokernel
preservation.  The checked theorem below only assumes preservation of the
single cokernel cofork for the selected short-complex difference map
`selectedMetrizableLeft S - selectedMetrizableRight S` by
`forgottenShortComplexFunctor`.

The remaining closed-range boundary is explicit: W442/W443 prove single
underlying `MetrizableLCA ⥤ AddCommGrpCat` cokernel preservation from a
closed-range equality/range-closed hypothesis for one `MetrizableLCA` morphism.
This file does not prove the componentwise/short-complex lift from those
underlying closed-range inputs to preservation of the selected short-complex
difference map.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpSelectedCokernelColimitFromSingleClosedRangeV370SupportW446

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

/-- The selected left arrow before forgetting topology. -/
def selectedMetrizableLeft
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    S.obj ordinarySourceIndex ⟶ S.obj ordinaryTargetIndex :=
  S.map (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.left)

/-- The selected right arrow before forgetting topology. -/
def selectedMetrizableRight
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    S.obj ordinarySourceIndex ⟶ S.obj ordinaryTargetIndex :=
  S.map (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.right)

/-- The selected leg before forgetting topology. -/
def selectedMetrizableTargetCoconeLeg
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    S.obj ordinaryTargetIndex ⟶ cs.pt :=
  cs.ι.app ordinaryTargetIndex

/-- Cocone naturality says the selected target leg coequalizes the two WPP arrows. -/
theorem selectedMetrizableTargetCoconeLeg_parallel_pair
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    selectedMetrizableLeft S ≫ selectedMetrizableTargetCoconeLeg S cs =
      selectedMetrizableRight S ≫ selectedMetrizableTargetCoconeLeg S cs :=
  (cs.w (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.left)).trans
    (cs.w (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.right)).symm

/-- The selected target leg as a cofork in short complexes of metrizable LCA groups. -/
def selectedMetrizableTargetCofork
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    Cofork (selectedMetrizableLeft S) (selectedMetrizableRight S) :=
  Cofork.ofπ (selectedMetrizableTargetCoconeLeg S cs)
    (selectedMetrizableTargetCoconeLeg_parallel_pair S cs)

/-- The ordinary diagram associated to the WPP-op short-complex diagram. -/
abbrev selectedMetrizableTargetOrdinaryDiagram
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    WalkingParallelPair ⥤ ShortComplex MetrizableLCA.{0} :=
  walkingParallelPairOpEquiv.functor ⋙ S

/-- The cocone over the ordinary diagram obtained from the WPP-op cocone. -/
def selectedMetrizableTargetMappedCocone
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    Cocone (selectedMetrizableTargetOrdinaryDiagram S) where
  pt := cs.pt
  ι :=
    { app := fun j => cs.ι.app (walkingParallelPairOpEquiv.functor.obj j)
      naturality := fun {j j'} f => by
        simpa only [Functor.comp_obj, Functor.comp_map, Functor.const_obj_obj,
          Functor.const_obj_map, Category.comp_id] using
          cs.w (walkingParallelPairOpEquiv.functor.map f) }

/-- The ordinary mapped cocone is the selected cofork precomposed along `diagramIsoParallelPair`. -/
def selectedMetrizableTargetMappedCoconeIsoPrecomposeCofork
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    selectedMetrizableTargetMappedCocone S cs ≅
      (Cocone.precompose
        (diagramIsoParallelPair (selectedMetrizableTargetOrdinaryDiagram S)).hom).obj
        (selectedMetrizableTargetCofork S cs) :=
  Cocone.ext (Iso.refl _) (fun j => by
    cases j
    · simp only [Iso.refl_hom]
      change
        cs.ι.app (walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.zero) =
          S.map (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.left) ≫
            cs.ι.app (walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.one)
      exact (cs.w (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.left)).symm
    · rfl)

/-- An original WPP-op colimit gives a colimit proof for the selected metrizable cofork. -/
def selectedMetrizableTargetCoforkColimitOfOriginal
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S)
    (hcs : IsColimit cs) :
    IsColimit (selectedMetrizableTargetCofork S cs) := by
  let hMapped : IsColimit (selectedMetrizableTargetMappedCocone S cs) :=
    hcs.whiskerEquivalence walkingParallelPairOpEquiv
  let hPre :
      IsColimit
        ((Cocone.precompose
          (diagramIsoParallelPair (selectedMetrizableTargetOrdinaryDiagram S)).hom).obj
          (selectedMetrizableTargetCofork S cs)) :=
    IsColimit.ofIsoColimit hMapped
      (selectedMetrizableTargetMappedCoconeIsoPrecomposeCofork S cs)
  exact
    (IsColimit.precomposeHomEquiv
      (diagramIsoParallelPair (selectedMetrizableTargetOrdinaryDiagram S))
      (selectedMetrizableTargetCofork S cs)) hPre

/-- The selected metrizable target leg is a cokernel cofork for `(left - right)`. -/
def selectedMetrizableTargetCokernelCofork
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    CokernelCofork (selectedMetrizableLeft S - selectedMetrizableRight S) :=
  Preadditive.cokernelCoforkOfCofork (selectedMetrizableTargetCofork S cs)

/-- The original WPP-op colimit gives the selected single-difference cokernel colimit. -/
def selectedMetrizableTargetCokernelColimitOfOriginal
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S)
    (hcs : IsColimit cs) :
    IsColimit (selectedMetrizableTargetCokernelCofork S cs) :=
  Preadditive.isColimitCokernelCoforkOfCofork
    (selectedMetrizableTargetCoforkColimitOfOriginal S cs hcs)

/-- The forgotten ordinary-left arrow of the WPP-op short-complex diagram. -/
def selectedForgottenLeft
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (S.obj ordinarySourceIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) ⟶
      (S.obj ordinaryTargetIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) :=
  forgottenShortComplexFunctor.map (selectedMetrizableLeft S)

/-- The forgotten ordinary-right arrow of the WPP-op short-complex diagram. -/
def selectedForgottenRight
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (S.obj ordinarySourceIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) ⟶
      (S.obj ordinaryTargetIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) :=
  forgottenShortComplexFunctor.map (selectedMetrizableRight S)

/-- The selected forgotten-target cocone leg. -/
def selectedForgottenTargetCoconeLeg
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    (S.obj ordinaryTargetIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) ⟶
      cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) :=
  forgottenShortComplexFunctor.map (selectedMetrizableTargetCoconeLeg S cs)

/-- The selected forgotten leg is an explicit cokernel cofork. -/
def selectedForgottenTargetCokernelCofork
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    CokernelCofork (selectedForgottenLeft S - selectedForgottenRight S) :=
  CokernelCofork.ofπ (selectedForgottenTargetCoconeLeg S cs) (by
    rw [Preadditive.sub_comp, sub_eq_zero]
    change
      forgottenShortComplexFunctor.map (selectedMetrizableLeft S) ≫
          forgottenShortComplexFunctor.map (selectedMetrizableTargetCoconeLeg S cs) =
        forgottenShortComplexFunctor.map (selectedMetrizableRight S) ≫
          forgottenShortComplexFunctor.map (selectedMetrizableTargetCoconeLeg S cs)
    rw [← forgottenShortComplexFunctor.map_comp, ← forgottenShortComplexFunctor.map_comp,
      selectedMetrizableTargetCoconeLeg_parallel_pair S cs])

/--
After rewriting `F.map (left - right)` to `F.map left - F.map right`, the mapped
selected metrizable cokernel cofork is the selected forgotten cokernel cofork.
-/
def precomposeSelectedForgottenCokernelCoforkIsoMap
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    let p : parallelPair
        (forgottenShortComplexFunctor.map
          (selectedMetrizableLeft S - selectedMetrizableRight S)) 0 ≅
        parallelPair (selectedForgottenLeft S - selectedForgottenRight S) 0 :=
      parallelPair.eqOfHomEq forgottenShortComplexFunctor.map_sub rfl
    ((Cocone.precompose p.hom).obj (selectedForgottenTargetCokernelCofork S cs)) ≅
      (selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor := by
  dsimp
  refine Cofork.ext (Iso.refl _) ?_
  simp only [Iso.refl_hom]
  rfl

/--
Primary W446 theorem: an original WPP-op colimit cocone induces the selected
target cokernel colimit from preservation of only the selected short-complex
difference cokernel.
-/
def selectedForgottenTargetCokernelColimitOfOriginalSinglePreservation
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S)
    [PreservesColimit (parallelPair
      (selectedMetrizableLeft S - selectedMetrizableRight S) 0) forgottenShortComplexFunctor]
    (hcs : IsColimit cs) :
    IsColimit (selectedForgottenTargetCokernelCofork S cs) := by
  let p : parallelPair
      (forgottenShortComplexFunctor.map
        (selectedMetrizableLeft S - selectedMetrizableRight S)) 0 ≅
      parallelPair (selectedForgottenLeft S - selectedForgottenRight S) 0 :=
    parallelPair.eqOfHomEq forgottenShortComplexFunctor.map_sub rfl
  let hMap :
      IsColimit
        ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor) :=
    CokernelCofork.mapIsColimit (selectedMetrizableTargetCokernelCofork S cs)
      (selectedMetrizableTargetCokernelColimitOfOriginal S cs hcs) forgottenShortComplexFunctor
  let hPre :
      IsColimit
        ((Cocone.precompose p.hom).obj (selectedForgottenTargetCokernelCofork S cs)) :=
    IsColimit.ofIsoColimit hMap
      (precomposeSelectedForgottenCokernelCoforkIsoMap S cs).symm
  exact (IsColimit.precomposeHomEquiv p (selectedForgottenTargetCokernelCofork S cs)) hPre

/-- W446 checked support state. -/
structure AddCommGrpSelectedCokernelColimitFromSingleClosedRangeV370SupportState : Type where
  seed : String
  checkedDeclarations : List String
  singleClosedRangeResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpSelectedCokernelColimitFromSingleClosedRangeV370SupportState :
    AddCommGrpSelectedCokernelColimitFromSingleClosedRangeV370SupportState where
  seed := "6bee571576ba41444ee62da8"
  checkedDeclarations :=
    ["selectedMetrizableTargetCoforkColimitOfOriginal",
      "selectedMetrizableTargetCokernelColimitOfOriginal",
      "precomposeSelectedForgottenCokernelCoforkIsoMap",
      "selectedForgottenTargetCokernelColimitOfOriginalSinglePreservation"]
  singleClosedRangeResult := "partial"
  remainingInputs :=
    ["Provide `[PreservesColimit (parallelPair (selectedMetrizableLeft S - selectedMetrizableRight S) 0) forgottenShortComplexFunctor]` for the selected short-complex difference map.",
      "W442/W443 discharge one underlying `MetrizableLCA ⥤ AddCommGrpCat` cokernel preservation from a closed-range hypothesis, but an additional componentwise/short-complex preservation lift is still needed to turn those closed-range inputs into the displayed short-complex preservation instance."]
  productSuccessClaimed := false

theorem currentAddCommGrpSelectedCokernelColimitFromSingleClosedRangeV370SupportState_productSuccess :
    currentAddCommGrpSelectedCokernelColimitFromSingleClosedRangeV370SupportState.productSuccessClaimed =
      false :=
  rfl

section Checks

#check selectedMetrizableTargetCoforkColimitOfOriginal
#check selectedMetrizableTargetCokernelColimitOfOriginal
#check precomposeSelectedForgottenCokernelCoforkIsoMap
#check selectedForgottenTargetCokernelColimitOfOriginalSinglePreservation
#check currentAddCommGrpSelectedCokernelColimitFromSingleClosedRangeV370SupportState_productSuccess

end Checks

end AddCommGrpSelectedCokernelColimitFromSingleClosedRangeV370SupportW446

end LeanLCAExactChallenge
