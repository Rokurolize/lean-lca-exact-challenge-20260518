import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Homology.ShortComplex.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
W419: short-complex preservation from underlying forgetful preservation.

This standalone audit file isolates the bridge requested after W416: preservation
of WPP-op colimits by an underlying functor `F` gives preservation of WPP-op
colimits by `F.mapShortComplex`.  The proof uses mathlib's componentwise
colimit API for `ShortComplex`: `ShortComplex.π₁`, `π₂`, and `π₃` preserve
colimits whenever the underlying category has colimits of the relevant shape,
and a short-complex cocone is colimit when all three projected cocones are.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpShortComplexPreservationFromUnderlyingV370SupportW419

open AddCommGrpSnakeInputDifferenceCokernel
open WppOpExactAcyclicFrontierConsolidatedW318

/-- The functor forgetting a short complex of metrizable LCA groups to abelian groups. -/
abbrev forgottenShortComplexFunctor :
    ShortComplex MetrizableLCA.{0} ⥤ ShortComplex AddCommGrpCat.{0} :=
  (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).mapShortComplex

/--
Generic bridge: shape-level colimit preservation by an underlying functor
implies shape-level colimit preservation by the induced short-complex functor.
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
The W416 missing input follows from WPP-op preservation by the underlying
forgetful functor `forget₂ MetrizableLCA AddCommGrpCat`.
-/
@[reducible]
def forgottenShortComplexPreservesWppOpColimitsOfUnderlying
    [HasColimitsOfShape WalkingParallelPairᵒᵖ MetrizableLCA.{0}]
    [PreservesColimitsOfShape WalkingParallelPairᵒᵖ
      (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})] :
    PreservesColimitsOfShape WalkingParallelPairᵒᵖ forgottenShortComplexFunctor :=
  mapShortComplexPreservesColimitsOfShapeOfUnderlying
    (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})

/--
The exact one-diagram preservation assumption consumed by W413/W416, now
derived directly from the underlying forgetful functor's WPP-op preservation.
-/
theorem forgottenShortComplexPreservesSelectedDiagramOfUnderlying
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    [HasColimitsOfShape WalkingParallelPairᵒᵖ MetrizableLCA.{0}]
    [PreservesColimitsOfShape WalkingParallelPairᵒᵖ
      (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})] :
    PreservesColimit S forgottenShortComplexFunctor := by
  letI : PreservesColimitsOfShape WalkingParallelPairᵒᵖ forgottenShortComplexFunctor :=
    forgottenShortComplexPreservesWppOpColimitsOfUnderlying
  infer_instance

/-- W419 checked support state. -/
structure AddCommGrpShortComplexPreservationFromUnderlyingV370SupportState : Type where
  seed : String
  checkedConstructors : List String
  shortComplexPreservationBridgeResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpShortComplexPreservationFromUnderlyingV370SupportState :
    AddCommGrpShortComplexPreservationFromUnderlyingV370SupportState where
  seed := "w419-20260520T232000Z-c85101817c80630a"
  checkedConstructors :=
    ["mapShortComplexPreservesColimitsOfShapeOfUnderlying",
      "forgottenShortComplexPreservesWppOpColimitsOfUnderlying",
      "forgottenShortComplexPreservesSelectedDiagramOfUnderlying"]
  shortComplexPreservationBridgeResult := "proved"
  remainingInputs :=
    ["main thread must provide `[HasColimitsOfShape WalkingParallelPairᵒᵖ MetrizableLCA]`",
      "main thread must provide `[PreservesColimitsOfShape WalkingParallelPairᵒᵖ (forget₂ MetrizableLCA AddCommGrpCat)]`"]
  productSuccessClaimed := false

theorem currentAddCommGrpShortComplexPreservationFromUnderlyingV370SupportState_productSuccess :
    currentAddCommGrpShortComplexPreservationFromUnderlyingV370SupportState.productSuccessClaimed = false :=
  rfl

section Checks

#check mapShortComplexPreservesColimitsOfShapeOfUnderlying
#check forgottenShortComplexPreservesWppOpColimitsOfUnderlying
#check forgottenShortComplexPreservesSelectedDiagramOfUnderlying
#check currentAddCommGrpShortComplexPreservationFromUnderlyingV370SupportState_productSuccess

end Checks

end AddCommGrpShortComplexPreservationFromUnderlyingV370SupportW419

end LeanLCAExactChallenge
