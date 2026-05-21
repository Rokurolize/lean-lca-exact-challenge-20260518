import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel
import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Homology.ShortComplex.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
W435: selected AddCommGrp cokernel colimit from an original WPP-op colimit,
with the W429 finite-colimit input discharged by W430's pointwise
cokernel-preservation sufficient condition for the underlying forgetful
functor.

The copied support files intentionally use independent standalone namespaces, so
this file repeats the W429 local definitions before exposing the requested
cokernel-preservation selected cokernel theorem.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpSelectedCokernelColimitFromCokernelPreservationV370SupportW435

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

/-- W425: the local finite-colimit instance supplies WPP-op colimits in `MetrizableLCA`. -/
theorem metrizableLCA_hasColimitsOfShape_walkingParallelPair_op :
    HasColimitsOfShape WalkingParallelPairᵒᵖ MetrizableLCA.{0} :=
  inferInstance

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

/--
Primary W427 cokernel theorem: W425 installs the WPP-op colimit existence input
locally, so callers only provide the original colimit proof and preservation by
the underlying forgetful functor.
-/
def selectedForgottenTargetCokernelColimitOfOriginalPreservationOnly
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S)
    [PreservesColimitsOfShape WalkingParallelPairᵒᵖ
      (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})]
    (hcs : IsColimit cs) :
    IsColimit (selectedForgottenTargetCokernelCofork S cs) := by
  letI : HasColimitsOfShape WalkingParallelPairᵒᵖ MetrizableLCA.{0} :=
    metrizableLCA_hasColimitsOfShape_walkingParallelPair_op
  exact selectedForgottenTargetCokernelColimitOfOriginalUnderlying S cs hcs

/--
Selected ordinary cofork variant with the same preservation-only assumptions.
-/
def selectedForgottenTargetCoforkColimitOfOriginalPreservationOnly
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S)
    [PreservesColimitsOfShape WalkingParallelPairᵒᵖ
      (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})]
    (hcs : IsColimit cs) :
    IsColimit (selectedForgottenTargetCofork S cs) := by
  letI : HasColimitsOfShape WalkingParallelPairᵒᵖ MetrizableLCA.{0} :=
    metrizableLCA_hasColimitsOfShape_walkingParallelPair_op
  exact selectedForgottenTargetCoforkColimitOfOriginalUnderlying S cs hcs

/--
W428 bridge: finite-colimit preservation of the underlying forgetful functor
supplies the WPP-op shape-preservation input used by W427.
-/
theorem underlyingForgetfulPreservesWppOpColimitsOfShape_of_preservesFiniteColimits
    [PreservesFiniteColimits (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})] :
    PreservesColimitsOfShape WalkingParallelPairᵒᵖ
      (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) :=
  inferInstance

/--
Primary W429 cokernel theorem: the original WPP-op colimit cocone induces the
selected target cokernel cofork colimit from only `hcs` and finite-colimit
preservation of the underlying forgetful functor.
-/
def selectedForgottenTargetCokernelColimitOfOriginalFinitePreservation
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S)
    [PreservesFiniteColimits (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})]
    (hcs : IsColimit cs) :
    IsColimit (selectedForgottenTargetCokernelCofork S cs) := by
  letI : PreservesColimitsOfShape WalkingParallelPairᵒᵖ
      (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) :=
    underlyingForgetfulPreservesWppOpColimitsOfShape_of_preservesFiniteColimits
  exact selectedForgottenTargetCokernelColimitOfOriginalPreservationOnly S cs hcs

/--
Selected ordinary cofork variant with the same finite-preservation assumptions.
-/
def selectedForgottenTargetCoforkColimitOfOriginalFinitePreservation
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S)
    [PreservesFiniteColimits (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})]
    (hcs : IsColimit cs) :
    IsColimit (selectedForgottenTargetCofork S cs) := by
  letI : PreservesColimitsOfShape WalkingParallelPairᵒᵖ
      (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) :=
    underlyingForgetfulPreservesWppOpColimitsOfShape_of_preservesFiniteColimits
  exact selectedForgottenTargetCoforkColimitOfOriginalPreservationOnly S cs hcs

/--
W430 bridge: finite-colimit preservation follows from preservation of
coequalizers plus the already-synthesized finite-coproduct preservation for the
underlying forgetful functor.
-/
theorem underlyingForgetfulPreservesFiniteColimits_of_preservesCoequalizers
    [PreservesColimitsOfShape WalkingParallelPair
      (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})] :
    PreservesFiniteColimits (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) := by
  haveI : PreservesFiniteCoproducts (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) :=
    inferInstance
  exact
    preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts
      (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})

/--
W430 pointwise bridge: finite-colimit preservation follows from preservation of
every cokernel cofork by the underlying forgetful functor.
-/
theorem underlyingForgetfulPreservesFiniteColimits_of_preservesCokernels
    [∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
      PreservesColimit (parallelPair f 0) (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})] :
    PreservesFiniteColimits (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) :=
  CategoryTheory.Functor.preservesFiniteColimits_of_preservesCokernels
    (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})

/--
W432 coequalizer theorem retained as a comparison point: the original WPP-op colimit cocone induces the
selected target cokernel cofork colimit from only `hcs` and coequalizer
preservation of the underlying forgetful functor.
-/
def selectedForgottenTargetCokernelColimitOfOriginalCoequalizerPreservation
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S)
    [PreservesColimitsOfShape WalkingParallelPair
      (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})]
    (hcs : IsColimit cs) :
    IsColimit (selectedForgottenTargetCokernelCofork S cs) := by
  letI : PreservesFiniteColimits (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) :=
    underlyingForgetfulPreservesFiniteColimits_of_preservesCoequalizers
  exact selectedForgottenTargetCokernelColimitOfOriginalFinitePreservation S cs hcs

/--
Selected ordinary cofork variant with the same coequalizer-preservation
assumption.
-/
def selectedForgottenTargetCoforkColimitOfOriginalCoequalizerPreservation
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S)
    [PreservesColimitsOfShape WalkingParallelPair
      (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})]
    (hcs : IsColimit cs) :
    IsColimit (selectedForgottenTargetCofork S cs) := by
  letI : PreservesFiniteColimits (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) :=
    underlyingForgetfulPreservesFiniteColimits_of_preservesCoequalizers
  exact selectedForgottenTargetCoforkColimitOfOriginalFinitePreservation S cs hcs

/--
Primary W435 cokernel theorem: the original WPP-op colimit cocone induces the
selected target cokernel cofork colimit from only `hcs` and pointwise
cokernel-cofork preservation by the underlying forgetful functor.
-/
def selectedForgottenTargetCokernelColimitOfOriginalCokernelPreservation
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S)
    [∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
      PreservesColimit (parallelPair f 0) (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})]
    (hcs : IsColimit cs) :
    IsColimit (selectedForgottenTargetCokernelCofork S cs) := by
  letI : PreservesFiniteColimits (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) :=
    underlyingForgetfulPreservesFiniteColimits_of_preservesCokernels
  exact selectedForgottenTargetCokernelColimitOfOriginalFinitePreservation S cs hcs

/--
Selected ordinary cofork variant with the same pointwise cokernel-preservation
assumption.
-/
def selectedForgottenTargetCoforkColimitOfOriginalCokernelPreservation
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S)
    [∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
      PreservesColimit (parallelPair f 0) (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})]
    (hcs : IsColimit cs) :
    IsColimit (selectedForgottenTargetCofork S cs) := by
  letI : PreservesFiniteColimits (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) :=
    underlyingForgetfulPreservesFiniteColimits_of_preservesCokernels
  exact selectedForgottenTargetCoforkColimitOfOriginalFinitePreservation S cs hcs

/-- W435 checked support state. -/
structure AddCommGrpSelectedCokernelColimitFromCokernelPreservationV370SupportState : Type where
  seed : String
  checkedConstructors : List String
  selectedCokernelColimitFromCokernelPreservationResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpSelectedCokernelColimitFromCokernelPreservationV370SupportState :
    AddCommGrpSelectedCokernelColimitFromCokernelPreservationV370SupportState where
  seed := "w435-167c7ac1dc237233d32689b4"
  checkedConstructors :=
    ["metrizableLCA_hasColimitsOfShape_walkingParallelPair_op",
      "selectedForgottenTargetCokernelColimitOfOriginalPreservationOnly",
      "selectedForgottenTargetCoforkColimitOfOriginalPreservationOnly",
      "underlyingForgetfulPreservesWppOpColimitsOfShape_of_preservesFiniteColimits",
      "selectedForgottenTargetCokernelColimitOfOriginalFinitePreservation",
      "selectedForgottenTargetCoforkColimitOfOriginalFinitePreservation",
      "underlyingForgetfulPreservesFiniteColimits_of_preservesCoequalizers",
      "selectedForgottenTargetCokernelColimitOfOriginalCoequalizerPreservation",
      "selectedForgottenTargetCoforkColimitOfOriginalCoequalizerPreservation",
      "underlyingForgetfulPreservesFiniteColimits_of_preservesCokernels",
      "selectedForgottenTargetCokernelColimitOfOriginalCokernelPreservation",
      "selectedForgottenTargetCoforkColimitOfOriginalCokernelPreservation"]
  selectedCokernelColimitFromCokernelPreservationResult := "proved"
  remainingInputs :=
    ["main thread must provide an original `hcs : IsColimit cs`",
      "main thread must provide `[∀ {X Y : MetrizableLCA} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) (forget₂ MetrizableLCA AddCommGrpCat)]`"]
  productSuccessClaimed := false

theorem currentAddCommGrpSelectedCokernelColimitFromCokernelPreservationV370SupportState_productSuccess :
    currentAddCommGrpSelectedCokernelColimitFromCokernelPreservationV370SupportState.productSuccessClaimed =
      false :=
  rfl

section Checks

#check selectedForgottenTargetMappedCoconeIsColimitOfUnderlying
#check selectedForgottenTargetCoforkColimitOfOriginalUnderlying
#check selectedForgottenTargetCokernelColimitOfOriginalUnderlying
#check metrizableLCA_hasColimitsOfShape_walkingParallelPair_op
#check selectedForgottenTargetCokernelColimitOfOriginalPreservationOnly
#check selectedForgottenTargetCoforkColimitOfOriginalPreservationOnly
#check underlyingForgetfulPreservesWppOpColimitsOfShape_of_preservesFiniteColimits
#check selectedForgottenTargetCokernelColimitOfOriginalFinitePreservation
#check selectedForgottenTargetCoforkColimitOfOriginalFinitePreservation
#check underlyingForgetfulPreservesFiniteColimits_of_preservesCoequalizers
#check selectedForgottenTargetCokernelColimitOfOriginalCoequalizerPreservation
#check selectedForgottenTargetCoforkColimitOfOriginalCoequalizerPreservation
#check underlyingForgetfulPreservesFiniteColimits_of_preservesCokernels
#check selectedForgottenTargetCokernelColimitOfOriginalCokernelPreservation
#check selectedForgottenTargetCoforkColimitOfOriginalCokernelPreservation
#check currentAddCommGrpSelectedCokernelColimitFromCokernelPreservationV370SupportState_productSuccess

end Checks

end AddCommGrpSelectedCokernelColimitFromCokernelPreservationV370SupportW435

end LeanLCAExactChallenge
