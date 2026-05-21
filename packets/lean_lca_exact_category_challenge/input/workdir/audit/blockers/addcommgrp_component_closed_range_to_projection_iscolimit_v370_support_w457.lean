import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel
import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Homology.ShortComplex.Limits
import Mathlib.Algebra.Homology.ShortComplex.Preadditive
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.Topology.Defs.Induced

/-!
W457: bridge attempt from selected component closed-range preservation to the
projection `IsColimit` fields consumed by W455/W452.

Seed: `35e252a5cb8c9b4fd2eb54da`.

This file checks the strongest local bridge that does not assume the missing
identification: each projected cocone of the mapped selected short-complex
cokernel cofork is definitionally the corresponding AddCommGrp cofork of the
forgotten selected component difference, with projection equal to the forgotten
component of the selected target cocone leg.  It also records the exact extra
componentwise `IsColimit` input needed to construct W455's three fields.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace AddCommGrpComponentClosedRangeToProjectionIsColimitV370SupportW457

open AddCommGrpSnakeInputDifferenceCokernel
open WppOpExactAcyclicFrontierConsolidatedW318

/-- Local name for the short-complex functor forgetting topology. -/
abbrev forgottenShortComplexFunctor :
    ShortComplex MetrizableLCA.{0} ⥤ ShortComplex AddCommGrpCat.{0} :=
  (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).mapShortComplex

/-- The underlying functor used by the one-component closed-range wrappers. -/
abbrev underlyingForgetfulFunctor : MetrizableLCA.{0} ⥤ AddCommGrpCat.{0} :=
  forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}

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

/-- The selected short-complex difference map whose projections W452 needs. -/
def selectedMetrizableDifference
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    S.obj ordinarySourceIndex ⟶ S.obj ordinaryTargetIndex :=
  selectedMetrizableLeft S - selectedMetrizableRight S

/-- First component of the selected difference map. -/
abbrev selectedMetrizableDifferenceπ₁
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (S.obj ordinarySourceIndex).X₁ ⟶ (S.obj ordinaryTargetIndex).X₁ :=
  (selectedMetrizableDifference S).τ₁

/-- Second component of the selected difference map. -/
abbrev selectedMetrizableDifferenceπ₂
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (S.obj ordinarySourceIndex).X₂ ⟶ (S.obj ordinaryTargetIndex).X₂ :=
  (selectedMetrizableDifference S).τ₂

/-- Third component of the selected difference map. -/
abbrev selectedMetrizableDifferenceπ₃
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (S.obj ordinarySourceIndex).X₃ ⟶ (S.obj ordinaryTargetIndex).X₃ :=
  (selectedMetrizableDifference S).τ₃

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

/-- The selected metrizable target leg is a cokernel cofork for `(left - right)`. -/
def selectedMetrizableTargetCokernelCofork
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    CokernelCofork (selectedMetrizableDifference S) :=
  Preadditive.cokernelCoforkOfCofork (selectedMetrizableTargetCofork S cs)

/-- The short-complex forgetful functor preserves zero morphisms, componentwise. -/
instance forgottenShortComplexFunctor_preservesZeroMorphisms :
    forgottenShortComplexFunctor.PreservesZeroMorphisms where
  map_zero S T := by
    ext x <;> rfl

/-- The short-complex forgetful functor is additive, componentwise. -/
instance forgottenShortComplexFunctor_additive :
    forgottenShortComplexFunctor.Additive where
  map_add {S T} {f g} := by
    ext x <;> rfl

/-- The first projected cocone has the expected component cofork projection. -/
theorem selectedProjectionπ₁_ι_one
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    (((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor))).ι.app
          WalkingParallelPair.one =
      underlyingForgetfulFunctor.map (selectedMetrizableTargetCoconeLeg S cs).τ₁ := by
  rfl

/-- The second projected cocone has the expected component cofork projection. -/
theorem selectedProjectionπ₂_ι_one
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    (((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor))).ι.app
          WalkingParallelPair.one =
      underlyingForgetfulFunctor.map (selectedMetrizableTargetCoconeLeg S cs).τ₂ := by
  rfl

/-- The third projected cocone has the expected component cofork projection. -/
theorem selectedProjectionπ₃_ι_one
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    (((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor))).ι.app
          WalkingParallelPair.one =
      underlyingForgetfulFunctor.map (selectedMetrizableTargetCoconeLeg S cs).τ₃ := by
  rfl

/-- The selected component difference kills the first component target leg. -/
theorem selectedMetrizableDifferenceπ₁_comp_target
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    selectedMetrizableDifferenceπ₁ S ≫ (selectedMetrizableTargetCoconeLeg S cs).τ₁ = 0 := by
  have h :
      selectedMetrizableDifference S ≫ selectedMetrizableTargetCoconeLeg S cs = 0 := by
    rw [selectedMetrizableDifference, Preadditive.sub_comp, sub_eq_zero]
    exact selectedMetrizableTargetCoconeLeg_parallel_pair S cs
  exact congrArg ShortComplex.Hom.τ₁ h

/-- The selected component difference kills the second component target leg. -/
theorem selectedMetrizableDifferenceπ₂_comp_target
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    selectedMetrizableDifferenceπ₂ S ≫ (selectedMetrizableTargetCoconeLeg S cs).τ₂ = 0 := by
  have h :
      selectedMetrizableDifference S ≫ selectedMetrizableTargetCoconeLeg S cs = 0 := by
    rw [selectedMetrizableDifference, Preadditive.sub_comp, sub_eq_zero]
    exact selectedMetrizableTargetCoconeLeg_parallel_pair S cs
  exact congrArg ShortComplex.Hom.τ₂ h

/-- The selected component difference kills the third component target leg. -/
theorem selectedMetrizableDifferenceπ₃_comp_target
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    selectedMetrizableDifferenceπ₃ S ≫ (selectedMetrizableTargetCoconeLeg S cs).τ₃ = 0 := by
  have h :
      selectedMetrizableDifference S ≫ selectedMetrizableTargetCoconeLeg S cs = 0 := by
    rw [selectedMetrizableDifference, Preadditive.sub_comp, sub_eq_zero]
    exact selectedMetrizableTargetCoconeLeg_parallel_pair S cs
  exact congrArg ShortComplex.Hom.τ₃ h

/-- The first selected component cofork after forgetting topology. -/
def selectedForgottenComponentπ₁CokernelCofork
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    CokernelCofork (underlyingForgetfulFunctor.map (selectedMetrizableDifferenceπ₁ S)) :=
  CokernelCofork.ofπ
    (underlyingForgetfulFunctor.map (selectedMetrizableTargetCoconeLeg S cs).τ₁) (by
      rw [← underlyingForgetfulFunctor.map_comp,
        selectedMetrizableDifferenceπ₁_comp_target S cs]
      rfl)

/-- The second selected component cofork after forgetting topology. -/
def selectedForgottenComponentπ₂CokernelCofork
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    CokernelCofork (underlyingForgetfulFunctor.map (selectedMetrizableDifferenceπ₂ S)) :=
  CokernelCofork.ofπ
    (underlyingForgetfulFunctor.map (selectedMetrizableTargetCoconeLeg S cs).τ₂) (by
      rw [← underlyingForgetfulFunctor.map_comp,
        selectedMetrizableDifferenceπ₂_comp_target S cs]
      rfl)

/-- The third selected component cofork after forgetting topology. -/
def selectedForgottenComponentπ₃CokernelCofork
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    CokernelCofork (underlyingForgetfulFunctor.map (selectedMetrizableDifferenceπ₃ S)) :=
  CokernelCofork.ofπ
    (underlyingForgetfulFunctor.map (selectedMetrizableTargetCoconeLeg S cs).τ₃) (by
      rw [← underlyingForgetfulFunctor.map_comp,
        selectedMetrizableDifferenceπ₃_comp_target S cs]
      rfl)

/--
The exact remaining bridge shape: closed range can prove preservation for the
explicit quotient cokernel of `selectedMetrizableDifferenceπ₁ S`, but W455 needs
this component cofork, whose point is `cs.pt.X₁`.
-/
def SelectedProjectionComponentIsColimitInputs
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 :=
  IsColimit
    ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
      ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor)) ×
  IsColimit
    ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
      ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor)) ×
  IsColimit
    ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
      ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor))

/-- W455 componentwise cokernel-colimit data for the selected mapped cofork. -/
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

/-- The exact constructor W455 needs once the three projection fields are supplied. -/
def selectedMappedCokernelComponentwiseInputsOfProjectionFields
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (H : SelectedProjectionComponentIsColimitInputs S cs) :
    SelectedMappedCokernelComponentwiseInputs S cs where
  hπ₁ := H.1
  hπ₂ := H.2.1
  hπ₃ := H.2.2

/-- W457 checked support state. -/
structure AddCommGrpComponentClosedRangeToProjectionIsColimitV370SupportState : Type where
  seed : String
  checkedDeclarations : List String
  projectionIsColimitResult : String
  componentCountClosed : Nat
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpComponentClosedRangeToProjectionIsColimitV370SupportState :
    AddCommGrpComponentClosedRangeToProjectionIsColimitV370SupportState where
  seed := "35e252a5cb8c9b4fd2eb54da"
  checkedDeclarations :=
    ["selectedProjectionπ₁_ι_one",
      "selectedProjectionπ₂_ι_one",
      "selectedProjectionπ₃_ι_one",
      "selectedMetrizableDifferenceπ₁_comp_target",
      "selectedMetrizableDifferenceπ₂_comp_target",
      "selectedMetrizableDifferenceπ₃_comp_target",
      "selectedForgottenComponentπ₁CokernelCofork",
      "selectedForgottenComponentπ₂CokernelCofork",
      "selectedForgottenComponentπ₃CokernelCofork",
      "SelectedProjectionComponentIsColimitInputs",
      "SelectedMappedCokernelComponentwiseInputs",
      "selectedMappedCokernelComponentwiseInputsOfProjectionFields"]
  projectionIsColimitResult := "partial"
  componentCountClosed := 0
  remainingInputs :=
    ["For each component i, identify the selected component leg `(selectedMetrizableTargetCoconeLeg S cs).τᵢ` with the explicit LCA cokernel projection `MetrizableLCA.cokernelπ (selectedMetrizableDifferenceπᵢ S)`, or provide an `IsColimit` proof for that selected component cofork directly.",
      "A diagram iso/precompose normalization is still needed between `parallelPair (forgottenShortComplexFunctor.map (selectedMetrizableDifference S)) 0 ⋙ ShortComplex.πᵢ` and `parallelPair (underlyingForgetfulFunctor.map (selectedMetrizableDifferenceπᵢ S)) 0` if downstream code wants to transport the component cofork proof by iso.",
      "Closed-range preservation from W442/W443 applies to the explicit quotient cokernel object; it does not by itself prove that the arbitrary selected cocone point `cs.pt.Xᵢ` is that quotient."]
  productSuccessClaimed := false

theorem currentAddCommGrpComponentClosedRangeToProjectionIsColimitV370SupportState_productSuccess :
    currentAddCommGrpComponentClosedRangeToProjectionIsColimitV370SupportState.productSuccessClaimed =
      false :=
  rfl

section Checks

#check selectedProjectionπ₁_ι_one
#check selectedProjectionπ₂_ι_one
#check selectedProjectionπ₃_ι_one
#check selectedMetrizableDifferenceπ₁_comp_target
#check selectedMetrizableDifferenceπ₂_comp_target
#check selectedMetrizableDifferenceπ₃_comp_target
#check selectedForgottenComponentπ₁CokernelCofork
#check selectedForgottenComponentπ₂CokernelCofork
#check selectedForgottenComponentπ₃CokernelCofork
#check SelectedProjectionComponentIsColimitInputs
#check SelectedMappedCokernelComponentwiseInputs
#check selectedMappedCokernelComponentwiseInputsOfProjectionFields
#check currentAddCommGrpComponentClosedRangeToProjectionIsColimitV370SupportState_productSuccess

end Checks

end AddCommGrpComponentClosedRangeToProjectionIsColimitV370SupportW457

end LeanLCAExactChallenge
