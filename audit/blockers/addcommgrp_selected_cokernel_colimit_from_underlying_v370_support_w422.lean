import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Homology.ShortComplex.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Preadditive.Basic

/-!
W422: selected AddCommGrp cokernel colimit from an original WPP-op colimit.

This standalone audit file composes the checked W410/W413/W416/W419 path in one
namespace.  The copied support files intentionally use independent namespaces,
so this file repeats the small local definitions and exposes the composed
theorems with the final assumptions requested by the worker contract.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpSelectedCokernelColimitFromUnderlyingV370SupportW422

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

/-- The ordinary forgotten diagram associated to the WPP-op short-complex diagram. -/
abbrev selectedForgottenTargetOrdinaryDiagram
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    WalkingParallelPair ⥤ ShortComplex AddCommGrpCat.{0} :=
  walkingParallelPairOpEquiv.functor ⋙ S ⋙ forgottenShortComplexFunctor

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

/--
The forgotten cocone over the ordinary `WalkingParallelPair` obtained by
precomposing the WPP-op diagram by `walkingParallelPairOpEquiv.functor`.
-/
def selectedForgottenTargetMappedCocone
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    Cocone (selectedForgottenTargetOrdinaryDiagram S) where
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

/--
The mapped cocone is the selected cofork precomposed along
`diagramIsoParallelPair` for the ordinary forgotten diagram.
-/
def selectedForgottenTargetMappedCoconeIsoPrecomposeCofork
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    selectedForgottenTargetMappedCocone S cs ≅
      (Cocone.precompose
        (diagramIsoParallelPair (selectedForgottenTargetOrdinaryDiagram S)).hom).obj
        (selectedForgottenTargetCofork S cs) :=
  Cocone.ext (Iso.refl _) (fun j => by
    cases j
    · simp only [Iso.refl_hom]
      change
        forgottenShortComplexFunctor.map
            (cs.ι.app (walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.zero)) =
          forgottenShortComplexFunctor.map
              (S.map (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.left)) ≫
            forgottenShortComplexFunctor.map
              (cs.ι.app (walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.one))
      rw [← forgottenShortComplexFunctor.map_comp]
      exact congrArg forgottenShortComplexFunctor.map
        (cs.w (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.left)).symm
    · rfl)

/-- A colimit proof for the mapped ordinary cocone gives a colimit proof for the selected cofork. -/
def selectedForgottenTargetCoforkColimitOfMappedCocone
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S)
    (hMapped : IsColimit (selectedForgottenTargetMappedCocone S cs)) :
    IsColimit (selectedForgottenTargetCofork S cs) := by
  let hPre :
      IsColimit
        ((Cocone.precompose
          (diagramIsoParallelPair (selectedForgottenTargetOrdinaryDiagram S)).hom).obj
          (selectedForgottenTargetCofork S cs)) :=
    IsColimit.ofIsoColimit hMapped
      (selectedForgottenTargetMappedCoconeIsoPrecomposeCofork S cs)
  exact
    (IsColimit.precomposeHomEquiv
      (diagramIsoParallelPair (selectedForgottenTargetOrdinaryDiagram S))
      (selectedForgottenTargetCofork S cs)) hPre

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

/-- W410: mapped-cocone colimit input gives the selected target cokernel colimit. -/
def selectedForgottenTargetCokernelColimitOfMappedCocone
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S)
    (hMapped : IsColimit (selectedForgottenTargetMappedCocone S cs)) :
    IsColimit (selectedForgottenTargetCokernelCofork S cs) :=
  IsColimit.ofIsoColimit
    (Preadditive.isColimitCokernelCoforkOfCofork
      (selectedForgottenTargetCoforkColimitOfMappedCocone S cs hMapped))
    (Cofork.ext (Iso.refl _) (by
      simp [selectedForgottenTargetCokernelCofork, selectedForgottenTargetCofork]))

/-- W413: the mapped ordinary cocone is colimit if the short-complex forgetful functor preserves `S`. -/
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

/-- W416: shape-level short-complex preservation supplies the selected one-diagram preservation. -/
theorem forgottenShortComplexPreservesSelectedDiagramOfShape
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    [PreservesColimitsOfShape WalkingParallelPairᵒᵖ forgottenShortComplexFunctor] :
    PreservesColimit S forgottenShortComplexFunctor :=
  inferInstance

/-- W416: mapped-cocone colimit from original colimit and shape-level short-complex preservation. -/
def selectedForgottenTargetMappedCoconeIsColimitOfShapePreserves
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S)
    [PreservesColimitsOfShape WalkingParallelPairᵒᵖ forgottenShortComplexFunctor]
    (hcs : IsColimit cs) :
    IsColimit (selectedForgottenTargetMappedCocone S cs) :=
  selectedForgottenTargetMappedCoconeIsColimitOfPreserves S cs hcs

/--
W419: shape-level colimit preservation by an underlying functor implies
shape-level colimit preservation by the induced short-complex functor.
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

/-- W419: the requested short-complex preservation instance from the underlying forgetful preservation. -/
@[reducible]
def forgottenShortComplexPreservesWppOpColimitsOfUnderlying
    [HasColimitsOfShape WalkingParallelPairᵒᵖ MetrizableLCA.{0}]
    [PreservesColimitsOfShape WalkingParallelPairᵒᵖ
      (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})] :
    PreservesColimitsOfShape WalkingParallelPairᵒᵖ forgottenShortComplexFunctor :=
  mapShortComplexPreservesColimitsOfShapeOfUnderlying
    (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})

/-- W419: exact one-diagram preservation derived from the underlying forgetful preservation. -/
theorem forgottenShortComplexPreservesSelectedDiagramOfUnderlying
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    [HasColimitsOfShape WalkingParallelPairᵒᵖ MetrizableLCA.{0}]
    [PreservesColimitsOfShape WalkingParallelPairᵒᵖ
      (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})] :
    PreservesColimit S forgottenShortComplexFunctor := by
  letI : PreservesColimitsOfShape WalkingParallelPairᵒᵖ forgottenShortComplexFunctor :=
    forgottenShortComplexPreservesWppOpColimitsOfUnderlying
  infer_instance

/--
W422 source: an original WPP-op colimit cocone maps to the W410-shaped ordinary
forgotten cocone under only the requested underlying preservation assumptions.
-/
def selectedForgottenTargetMappedCoconeIsColimitOfUnderlying
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S)
    [HasColimitsOfShape WalkingParallelPairᵒᵖ MetrizableLCA.{0}]
    [PreservesColimitsOfShape WalkingParallelPairᵒᵖ
      (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})]
    (hcs : IsColimit cs) :
    IsColimit (selectedForgottenTargetMappedCocone S cs) := by
  letI : PreservesColimitsOfShape WalkingParallelPairᵒᵖ forgottenShortComplexFunctor :=
    forgottenShortComplexPreservesWppOpColimitsOfUnderlying
  exact selectedForgottenTargetMappedCoconeIsColimitOfShapePreserves S cs hcs

/--
Primary W422 theorem: the original WPP-op colimit cocone induces the selected
ordinary target cofork colimit in `AddCommGrpCat`.
-/
def selectedForgottenTargetCoforkColimitOfOriginalUnderlying
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S)
    [HasColimitsOfShape WalkingParallelPairᵒᵖ MetrizableLCA.{0}]
    [PreservesColimitsOfShape WalkingParallelPairᵒᵖ
      (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})]
    (hcs : IsColimit cs) :
    IsColimit (selectedForgottenTargetCofork S cs) :=
  selectedForgottenTargetCoforkColimitOfMappedCocone S cs
    (selectedForgottenTargetMappedCoconeIsColimitOfUnderlying S cs hcs)

/--
Primary W422 cokernel theorem: the same original WPP-op colimit cocone induces
the selected target cokernel cofork colimit in `AddCommGrpCat`.
-/
def selectedForgottenTargetCokernelColimitOfOriginalUnderlying
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S)
    [HasColimitsOfShape WalkingParallelPairᵒᵖ MetrizableLCA.{0}]
    [PreservesColimitsOfShape WalkingParallelPairᵒᵖ
      (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})]
    (hcs : IsColimit cs) :
    IsColimit (selectedForgottenTargetCokernelCofork S cs) :=
  selectedForgottenTargetCokernelColimitOfMappedCocone S cs
    (selectedForgottenTargetMappedCoconeIsColimitOfUnderlying S cs hcs)

/-- W422 checked support state. -/
structure AddCommGrpSelectedCokernelColimitFromUnderlyingV370SupportState : Type where
  seed : String
  checkedConstructors : List String
  selectedCokernelColimitFromUnderlyingResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpSelectedCokernelColimitFromUnderlyingV370SupportState :
    AddCommGrpSelectedCokernelColimitFromUnderlyingV370SupportState where
  seed := "20260520T232742Z-60685b35b84298c0160e913e"
  checkedConstructors :=
    ["selectedForgottenTargetMappedCoconeIsColimitOfUnderlying",
      "selectedForgottenTargetCoforkColimitOfOriginalUnderlying",
      "selectedForgottenTargetCokernelColimitOfOriginalUnderlying"]
  selectedCokernelColimitFromUnderlyingResult := "proved"
  remainingInputs :=
    ["main thread must provide an original `hcs : IsColimit cs`",
      "main thread must provide `[HasColimitsOfShape WalkingParallelPairᵒᵖ MetrizableLCA]`",
      "main thread must provide `[PreservesColimitsOfShape WalkingParallelPairᵒᵖ (forget₂ MetrizableLCA AddCommGrpCat)]`"]
  productSuccessClaimed := false

theorem currentAddCommGrpSelectedCokernelColimitFromUnderlyingV370SupportState_productSuccess :
    currentAddCommGrpSelectedCokernelColimitFromUnderlyingV370SupportState.productSuccessClaimed =
      false :=
  rfl

section Checks

#check selectedForgottenTargetMappedCoconeIsColimitOfUnderlying
#check selectedForgottenTargetCoforkColimitOfOriginalUnderlying
#check selectedForgottenTargetCokernelColimitOfOriginalUnderlying
#check currentAddCommGrpSelectedCokernelColimitFromUnderlyingV370SupportState_productSuccess

end Checks

end AddCommGrpSelectedCokernelColimitFromUnderlyingV370SupportW422

end LeanLCAExactChallenge
