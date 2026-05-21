import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel
import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Homology.ShortComplex.Limits
import Mathlib.Algebra.Homology.ShortComplex.Preadditive
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
W449: additive/zero boundary for the forgotten short-complex functor used by
W446.

Seed: `1b6bcea67fa6d9525200c16d`.

This file discharges W446's additive and zero-morphism typeclass inputs for the
selected forgotten short-complex functor.  It also records the checked
componentwise shape needed to assemble a short-complex cokernel cofork from
the three projection coforks; the selected preservation instance itself remains
an explicit input.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpForgottenShortComplexFunctorAdditiveZeroV370SupportW449

open AddCommGrpSnakeInputDifferenceCokernel
open WppOpExactAcyclicFrontierConsolidatedW318

/-- Local name for W446's short-complex forgetful functor. -/
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

/-- The W446 functor preserves zero morphisms, componentwise. -/
instance forgottenShortComplexFunctor_preservesZeroMorphisms :
    forgottenShortComplexFunctor.PreservesZeroMorphisms where
  map_zero S T := by
    ext x <;> rfl

/-- The W446 functor is additive, componentwise. -/
instance forgottenShortComplexFunctor_additive :
    forgottenShortComplexFunctor.Additive where
  map_add {S T} {f g} := by
    ext x <;> rfl

/-- Instance synthesis exposes the zero-morphism preservation input W446 needs. -/
theorem forgottenShortComplexFunctor_preservesZeroMorphisms_infer :
    forgottenShortComplexFunctor.PreservesZeroMorphisms :=
  inferInstance

/-- Instance synthesis exposes the additive input W446 needs. -/
theorem forgottenShortComplexFunctor_additive_infer :
    forgottenShortComplexFunctor.Additive :=
  inferInstance

/--
W446's selected theorem with the additive and zero-morphism inputs discharged
locally.  The selected single-preservation instance is intentionally still a
typeclass input.
-/
def selectedForgottenTargetCokernelColimitOfOriginalSinglePreservation_additiveZeroDischarged
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S)
    [PreservesColimit (parallelPair
      (selectedMetrizableLeft S - selectedMetrizableRight S) 0)
      forgottenShortComplexFunctor]
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
  let hIso :
      ((Cocone.precompose p.hom).obj (selectedForgottenTargetCokernelCofork S cs)) ≅
        (selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor := by
    dsimp [p]
    refine Cofork.ext (Iso.refl _) ?_
    simp only [Iso.refl_hom]
    rfl
  let hPre :
      IsColimit
        ((Cocone.precompose p.hom).obj (selectedForgottenTargetCokernelCofork S cs)) :=
    IsColimit.ofIsoColimit hMap hIso.symm
  exact (IsColimit.precomposeHomEquiv p (selectedForgottenTargetCokernelCofork S cs)) hPre

/--
Componentwise cokernel-colimit data for the selected mapped W446 cofork.

This is the exact data accepted by `ShortComplex.isColimitOfIsColimitπ` after
the selected metrizable cokernel cofork is mapped by the forgotten functor.
-/
structure SelectedMappedCokernelComponentwiseInputs
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 where
  hπ₁ :
    IsColimit
      ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor))
  hπ₂ :
    IsColimit
      ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor))
  hπ₃ :
    IsColimit
      ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor))

/--
The componentwise projection inputs assemble into the mapped selected
short-complex cokernel cofork.
-/
def selectedMappedCokernelColimitOfComponentwise
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (H : SelectedMappedCokernelComponentwiseInputs S cs) :
    IsColimit
      ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor) :=
  ShortComplex.isColimitOfIsColimitπ
    ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor)
    H.hπ₁ H.hπ₂ H.hπ₃

/--
Shape-level short-complex preservation follows from componentwise underlying
shape preservation by applying `ShortComplex.isColimitOfIsColimitπ` to the
three projection cocones.
-/
@[reducible]
def mapShortComplexPreservesColimitsOfShapeOfUnderlying
    {J C D : Type*} [Category J] [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [HasColimitsOfShape J C] [HasColimitsOfShape J D]
    [PreservesColimitsOfShape J F] :
    PreservesColimitsOfShape J F.mapShortComplex where
  preservesColimit {K} :=
    preservesColimit_of_preserves_colimit_cocone
      (ShortComplex.isColimitColimitCocone K)
      (by
        refine ShortComplex.isColimitOfIsColimitπ _ ?_ ?_ ?_
        · change IsColimit (F.mapCocone (ShortComplex.π₁.mapCocone (ShortComplex.colimitCocone K)))
          exact isColimitOfPreserves F
            (isColimitOfPreserves (ShortComplex.π₁ : ShortComplex C ⥤ C)
              (ShortComplex.isColimitColimitCocone K))
        · change IsColimit (F.mapCocone (ShortComplex.π₂.mapCocone (ShortComplex.colimitCocone K)))
          exact isColimitOfPreserves F
            (isColimitOfPreserves (ShortComplex.π₂ : ShortComplex C ⥤ C)
              (ShortComplex.isColimitColimitCocone K))
        · change IsColimit (F.mapCocone (ShortComplex.π₃.mapCocone (ShortComplex.colimitCocone K)))
          exact isColimitOfPreserves F
            (isColimitOfPreserves (ShortComplex.π₃ : ShortComplex C ⥤ C)
              (ShortComplex.isColimitColimitCocone K)))

/--
W435's shape-level bridge remains checked and importable here.  It gives
short-complex shape preservation from underlying shape preservation, not the
selected single cokernel-preservation instance needed by W446.
-/
@[reducible]
def forgottenShortComplexPreservesWppOpColimitsOfUnderlying_checked
    [HasColimitsOfShape WalkingParallelPairᵒᵖ MetrizableLCA.{0}]
    [PreservesColimitsOfShape WalkingParallelPairᵒᵖ
      (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})] :
    PreservesColimitsOfShape WalkingParallelPairᵒᵖ forgottenShortComplexFunctor :=
  mapShortComplexPreservesColimitsOfShapeOfUnderlying
    (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})

/-- W449 checked support state. -/
structure AddCommGrpForgottenShortComplexFunctorAdditiveZeroV370SupportState : Type where
  seed : String
  checkedDeclarations : List String
  additiveZeroResult : String
  selectedPreservationLiftResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpForgottenShortComplexFunctorAdditiveZeroV370SupportState :
    AddCommGrpForgottenShortComplexFunctorAdditiveZeroV370SupportState where
  seed := "1b6bcea67fa6d9525200c16d"
  checkedDeclarations :=
    ["forgottenShortComplexFunctor_preservesZeroMorphisms",
      "forgottenShortComplexFunctor_additive",
      "forgottenShortComplexFunctor_preservesZeroMorphisms_infer",
      "forgottenShortComplexFunctor_additive_infer",
      "selectedForgottenTargetCokernelColimitOfOriginalSinglePreservation_additiveZeroDischarged",
      "SelectedMappedCokernelComponentwiseInputs",
      "selectedMappedCokernelColimitOfComponentwise",
      "forgottenShortComplexPreservesWppOpColimitsOfUnderlying_checked"]
  additiveZeroResult := "proved"
  selectedPreservationLiftResult := "partial"
  remainingInputs :=
    ["Provide `[PreservesColimit (parallelPair (selectedMetrizableLeft S - selectedMetrizableRight S) 0) forgottenShortComplexFunctor]` for the selected short-complex difference map.",
      "Alternatively provide the three projection colimit fields of `SelectedMappedCokernelComponentwiseInputs S cs` for the mapped selected cokernel cofork, then bridge that mapped cofork to W446's selected forgotten cofork.",
      "W435's `forgottenShortComplexPreservesWppOpColimitsOfUnderlying_checked` proves WPP-op shape preservation from underlying WPP-op shape preservation; it does not by itself construct the selected single cokernel-preservation instance from closed-range component data."]
  productSuccessClaimed := false

theorem currentAddCommGrpForgottenShortComplexFunctorAdditiveZeroV370SupportState_productSuccess :
    currentAddCommGrpForgottenShortComplexFunctorAdditiveZeroV370SupportState.productSuccessClaimed =
      false :=
  rfl

section Checks

#check forgottenShortComplexFunctor_preservesZeroMorphisms
#check forgottenShortComplexFunctor_additive
#check forgottenShortComplexFunctor_preservesZeroMorphisms_infer
#check forgottenShortComplexFunctor_additive_infer
#check selectedForgottenTargetCokernelColimitOfOriginalSinglePreservation_additiveZeroDischarged
#check SelectedMappedCokernelComponentwiseInputs
#check selectedMappedCokernelColimitOfComponentwise
#check ShortComplex.isColimitOfIsColimitπ
#check mapShortComplexPreservesColimitsOfShapeOfUnderlying
#check forgottenShortComplexPreservesWppOpColimitsOfUnderlying_checked
#check currentAddCommGrpForgottenShortComplexFunctorAdditiveZeroV370SupportState_productSuccess

end Checks

end AddCommGrpForgottenShortComplexFunctorAdditiveZeroV370SupportW449

end LeanLCAExactChallenge
