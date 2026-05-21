import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel
import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.LCA.StrictExact
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Homology.ShortComplex.Limits
import Mathlib.Algebra.Homology.ShortComplex.Preadditive
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.Topology.Defs.Induced


/-!
W463: selected component quotient-identification bridge.

Seed: `c33f238ef7fc4cbb2ff6d34e`.

This standalone support file reduces W460's remaining selected component
cofork `IsColimit` inputs to explicit quotient-identification data: an
AddCommGrp point isomorphism from the selected component target to the forgotten
explicit LCA cokernel quotient, a proof that the selected component leg becomes
the explicit quotient projection under that isomorphism, and the explicit
quotient cofork `IsColimit` proof.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463

open AddCommGrpSnakeInputDifferenceCokernel
open WppOpExactAcyclicFrontierConsolidatedW318
open MetrizableLCA

/-- Worker seed recorded before edits, used only to diversify proof search. -/
def supportSeed : String := "c33f238ef7fc4cbb2ff6d34e"

/-- Local name for the short-complex functor forgetting topology. -/
abbrev forgottenShortComplexFunctor :
    ShortComplex MetrizableLCA.{0} ⥤ ShortComplex AddCommGrpCat.{0} :=
  (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).mapShortComplex

/-- The underlying functor used by the one-component wrappers. -/
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

/-- The selected short-complex difference map whose components are normalized below. -/
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

/-- The mapped selected short-complex cofork after forgetting topology. -/
abbrev selectedForgottenShortComplexCokernelCofork
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    Cocone (parallelPair (forgottenShortComplexFunctor.map (selectedMetrizableDifference S)) 0) :=
  (selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor

/-- W433's explicit local cokernel cofork before forgetting topology. -/
def explicitMetrizableCokernelCofork {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    CokernelCofork f :=
  CokernelCofork.ofπ (cokernelπ f) (comp_cokernelπ f)

/-- W433's mapped concrete cokernel cocone. -/
def mappedExplicitCokernelCocone {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    Cocone (parallelPair f 0 ⋙ underlyingForgetfulFunctor) :=
  underlyingForgetfulFunctor.mapCocone (explicitMetrizableCokernelCofork f)

/-- The forgotten explicit cokernel projection, as in W440. -/
abbrev forgottenCokernelπ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    underlyingForgetfulFunctor.obj Y ⟶ underlyingForgetfulFunctor.obj (cokernelObj f) :=
  AddCommGrpCat.ofHom (QuotientAddGroup.mk' (cokernelSubgroup f))

/-- W440's projection is the forgotten image of the LCA cokernel projection. -/
theorem forgottenCokernelπ_eq_map_cokernelπ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    forgottenCokernelπ f = underlyingForgetfulFunctor.map (cokernelπ f) := by
  ext y
  rfl

/-- The forgotten explicit cokernel projection kills the forgotten source map. -/
theorem forgottenCokernelπ_condition {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    underlyingForgetfulFunctor.map f ≫ forgottenCokernelπ f = 0 := by
  ext x
  change ((f x : Y) : Y ⧸ cokernelSubgroup f) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact map_mem_cokernelSubgroup f x

/-- W440's explicit AddCommGrp cokernel cofork. -/
def forgottenExplicitCokernelCofork {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    CokernelCofork (underlyingForgetfulFunctor.map f) :=
  CokernelCofork.ofπ (forgottenCokernelπ f) (forgottenCokernelπ_condition f)

/-- Transport data identifying the selected component cofork with the explicit quotient cofork. -/
structure SelectedComponentQuotientIdentificationInputsW463
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 where
  pointIsoπ₁ :
    underlyingForgetfulFunctor.obj (cs.pt.X₁) ≅
      underlyingForgetfulFunctor.obj (cokernelObj (selectedMetrizableDifferenceπ₁ S))
  pointIsoπ₂ :
    underlyingForgetfulFunctor.obj (cs.pt.X₂) ≅
      underlyingForgetfulFunctor.obj (cokernelObj (selectedMetrizableDifferenceπ₂ S))
  pointIsoπ₃ :
    underlyingForgetfulFunctor.obj (cs.pt.X₃) ≅
      underlyingForgetfulFunctor.obj (cokernelObj (selectedMetrizableDifferenceπ₃ S))
  legπ₁ :
    underlyingForgetfulFunctor.map (selectedMetrizableTargetCoconeLeg S cs).τ₁ ≫
      pointIsoπ₁.hom =
        forgottenCokernelπ (selectedMetrizableDifferenceπ₁ S)
  legπ₂ :
    underlyingForgetfulFunctor.map (selectedMetrizableTargetCoconeLeg S cs).τ₂ ≫
      pointIsoπ₂.hom =
        forgottenCokernelπ (selectedMetrizableDifferenceπ₂ S)
  legπ₃ :
    underlyingForgetfulFunctor.map (selectedMetrizableTargetCoconeLeg S cs).τ₃ ≫
      pointIsoπ₃.hom =
        forgottenCokernelπ (selectedMetrizableDifferenceπ₃ S)
  explicitπ₁CokernelIsColimit :
    IsColimit (forgottenExplicitCokernelCofork (selectedMetrizableDifferenceπ₁ S))
  explicitπ₂CokernelIsColimit :
    IsColimit (forgottenExplicitCokernelCofork (selectedMetrizableDifferenceπ₂ S))
  explicitπ₃CokernelIsColimit :
    IsColimit (forgottenExplicitCokernelCofork (selectedMetrizableDifferenceπ₃ S))

/-- The selected first-component cofork is isomorphic to the explicit quotient cofork. -/
def selectedComponentπ₁CoforkIso_of_quotientIdentification
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentQuotientIdentificationInputsW463 S cs) :
    selectedForgottenComponentπ₁CokernelCofork S cs ≅
      forgottenExplicitCokernelCofork (selectedMetrizableDifferenceπ₁ S) :=
  Cocone.ext h.pointIsoπ₁ (by
    rintro (_ | _)
    · have hzero := congrArg
        (fun q => underlyingForgetfulFunctor.map (selectedMetrizableDifferenceπ₁ S) ≫ q) h.legπ₁
      simpa [Category.assoc, selectedForgottenComponentπ₁CokernelCofork,
        forgottenExplicitCokernelCofork] using hzero
    · simpa [selectedForgottenComponentπ₁CokernelCofork, forgottenExplicitCokernelCofork] using h.legπ₁)

/-- The selected second-component cofork is isomorphic to the explicit quotient cofork. -/
def selectedComponentπ₂CoforkIso_of_quotientIdentification
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentQuotientIdentificationInputsW463 S cs) :
    selectedForgottenComponentπ₂CokernelCofork S cs ≅
      forgottenExplicitCokernelCofork (selectedMetrizableDifferenceπ₂ S) :=
  Cocone.ext h.pointIsoπ₂ (by
    rintro (_ | _)
    · have hzero := congrArg
        (fun q => underlyingForgetfulFunctor.map (selectedMetrizableDifferenceπ₂ S) ≫ q) h.legπ₂
      simpa [Category.assoc, selectedForgottenComponentπ₂CokernelCofork,
        forgottenExplicitCokernelCofork] using hzero
    · simpa [selectedForgottenComponentπ₂CokernelCofork, forgottenExplicitCokernelCofork] using h.legπ₂)

/-- The selected third-component cofork is isomorphic to the explicit quotient cofork. -/
def selectedComponentπ₃CoforkIso_of_quotientIdentification
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentQuotientIdentificationInputsW463 S cs) :
    selectedForgottenComponentπ₃CokernelCofork S cs ≅
      forgottenExplicitCokernelCofork (selectedMetrizableDifferenceπ₃ S) :=
  Cocone.ext h.pointIsoπ₃ (by
    rintro (_ | _)
    · have hzero := congrArg
        (fun q => underlyingForgetfulFunctor.map (selectedMetrizableDifferenceπ₃ S) ≫ q) h.legπ₃
      simpa [Category.assoc, selectedForgottenComponentπ₃CokernelCofork,
        forgottenExplicitCokernelCofork] using hzero
    · simpa [selectedForgottenComponentπ₃CokernelCofork, forgottenExplicitCokernelCofork] using h.legπ₃)

/-- Quotient-identification data transports the explicit first-component cokernel proof. -/
def selectedComponentπ₁_isColimit_of_quotientIdentification_w463
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentQuotientIdentificationInputsW463 S cs) :
    IsColimit (selectedForgottenComponentπ₁CokernelCofork S cs) :=
  IsColimit.ofIsoColimit h.explicitπ₁CokernelIsColimit
    (selectedComponentπ₁CoforkIso_of_quotientIdentification h).symm

/-- Quotient-identification data transports the explicit second-component cokernel proof. -/
def selectedComponentπ₂_isColimit_of_quotientIdentification_w463
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentQuotientIdentificationInputsW463 S cs) :
    IsColimit (selectedForgottenComponentπ₂CokernelCofork S cs) :=
  IsColimit.ofIsoColimit h.explicitπ₂CokernelIsColimit
    (selectedComponentπ₂CoforkIso_of_quotientIdentification h).symm

/-- Quotient-identification data transports the explicit third-component cokernel proof. -/
def selectedComponentπ₃_isColimit_of_quotientIdentification_w463
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentQuotientIdentificationInputsW463 S cs) :
    IsColimit (selectedForgottenComponentπ₃CokernelCofork S cs) :=
  IsColimit.ofIsoColimit h.explicitπ₃CokernelIsColimit
    (selectedComponentπ₃CoforkIso_of_quotientIdentification h).symm

/-- The projected `π₁` parallel-pair diagram is the selected component diagram. -/
def selectedProjectionπ₁DiagramIso
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    parallelPair (underlyingForgetfulFunctor.map (selectedMetrizableDifferenceπ₁ S)) 0 ≅
      (parallelPair (forgottenShortComplexFunctor.map (selectedMetrizableDifference S)) 0) ⋙
        (ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}) :=
  parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp [selectedMetrizableDifferenceπ₁]) (by rfl)

/-- The projected `π₂` parallel-pair diagram is the selected component diagram. -/
def selectedProjectionπ₂DiagramIso
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    parallelPair (underlyingForgetfulFunctor.map (selectedMetrizableDifferenceπ₂ S)) 0 ≅
      (parallelPair (forgottenShortComplexFunctor.map (selectedMetrizableDifference S)) 0) ⋙
        (ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}) :=
  parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp [selectedMetrizableDifferenceπ₂]) (by rfl)

/-- The projected `π₃` parallel-pair diagram is the selected component diagram. -/
def selectedProjectionπ₃DiagramIso
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    parallelPair (underlyingForgetfulFunctor.map (selectedMetrizableDifferenceπ₃ S)) 0 ≅
      (parallelPair (forgottenShortComplexFunctor.map (selectedMetrizableDifference S)) 0) ⋙
        (ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}) :=
  parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp [selectedMetrizableDifferenceπ₃]) (by rfl)

/-- The first selected component cofork is the precomposed projected cofork. -/
def selectedProjectionπ₁CoforkIso
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    (Cocone.precompose (selectedProjectionπ₁DiagramIso S).inv).obj
        (selectedForgottenComponentπ₁CokernelCofork S cs) ≅
      ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (selectedForgottenShortComplexCokernelCofork S cs)) :=
  Cocone.ext (Iso.refl _) (by
    rintro (_ | _) <;> rfl)

/-- The second selected component cofork is the precomposed projected cofork. -/
def selectedProjectionπ₂CoforkIso
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    (Cocone.precompose (selectedProjectionπ₂DiagramIso S).inv).obj
        (selectedForgottenComponentπ₂CokernelCofork S cs) ≅
      ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (selectedForgottenShortComplexCokernelCofork S cs)) :=
  Cocone.ext (Iso.refl _) (by
    rintro (_ | _) <;> rfl)

/-- The third selected component cofork is the precomposed projected cofork. -/
def selectedProjectionπ₃CoforkIso
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    (Cocone.precompose (selectedProjectionπ₃DiagramIso S).inv).obj
        (selectedForgottenComponentπ₃CokernelCofork S cs) ≅
      ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (selectedForgottenShortComplexCokernelCofork S cs)) :=
  Cocone.ext (Iso.refl _) (by
    rintro (_ | _) <;> rfl)

/-- Transport a selected first-component `IsColimit` proof to the projected cofork. -/
def projectionπ₁_isColimit_of_selectedComponentπ₁
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : IsColimit (selectedForgottenComponentπ₁CokernelCofork S cs)) :
    IsColimit
      ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (selectedForgottenShortComplexCokernelCofork S cs)) :=
  (IsColimit.equivOfNatIsoOfIso (selectedProjectionπ₁DiagramIso S)
    (selectedForgottenComponentπ₁CokernelCofork S cs)
    _
    (selectedProjectionπ₁CoforkIso S cs)) h

/-- Transport a selected second-component `IsColimit` proof to the projected cofork. -/
def projectionπ₂_isColimit_of_selectedComponentπ₂
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : IsColimit (selectedForgottenComponentπ₂CokernelCofork S cs)) :
    IsColimit
      ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (selectedForgottenShortComplexCokernelCofork S cs)) :=
  (IsColimit.equivOfNatIsoOfIso (selectedProjectionπ₂DiagramIso S)
    (selectedForgottenComponentπ₂CokernelCofork S cs)
    _
    (selectedProjectionπ₂CoforkIso S cs)) h

/-- Transport a selected third-component `IsColimit` proof to the projected cofork. -/
def projectionπ₃_isColimit_of_selectedComponentπ₃
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : IsColimit (selectedForgottenComponentπ₃CokernelCofork S cs)) :
    IsColimit
      ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (selectedForgottenShortComplexCokernelCofork S cs)) :=
  (IsColimit.equivOfNatIsoOfIso (selectedProjectionπ₃DiagramIso S)
    (selectedForgottenComponentπ₃CokernelCofork S cs)
    _
    (selectedProjectionπ₃CoforkIso S cs)) h

/-- W457's selected projection colimit input shape. -/
def SelectedProjectionComponentIsColimitInputs
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 :=
  IsColimit
    ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
      (selectedForgottenShortComplexCokernelCofork S cs)) ×
  IsColimit
    ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
      (selectedForgottenShortComplexCokernelCofork S cs)) ×
  IsColimit
    ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
      (selectedForgottenShortComplexCokernelCofork S cs))

/-- Component `IsColimit` proofs for the selected coforks supply W457's projected fields. -/
def selectedProjectionComponentIsColimitInputs_of_selectedComponentCoforks
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (hπ₁ : IsColimit (selectedForgottenComponentπ₁CokernelCofork S cs))
    (hπ₂ : IsColimit (selectedForgottenComponentπ₂CokernelCofork S cs))
    (hπ₃ : IsColimit (selectedForgottenComponentπ₃CokernelCofork S cs)) :
    SelectedProjectionComponentIsColimitInputs S cs :=
  ⟨projectionπ₁_isColimit_of_selectedComponentπ₁ hπ₁,
    projectionπ₂_isColimit_of_selectedComponentπ₂ hπ₂,
    projectionπ₃_isColimit_of_selectedComponentπ₃ hπ₃⟩

/-- Quotient-identification inputs provide all projected component `IsColimit` fields. -/
def selectedProjectionComponentIsColimitInputs_of_quotientIdentifications_w463
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentQuotientIdentificationInputsW463 S cs) :
    SelectedProjectionComponentIsColimitInputs S cs :=
  selectedProjectionComponentIsColimitInputs_of_selectedComponentCoforks
    (selectedComponentπ₁_isColimit_of_quotientIdentification_w463 h)
    (selectedComponentπ₂_isColimit_of_quotientIdentification_w463 h)
    (selectedComponentπ₃_isColimit_of_quotientIdentification_w463 h)

/-- Machine-readable W463 support state. -/
structure AddCommGrpSelectedComponentQuotientIdentificationV370SupportState : Type where
  seed : String
  checkedDeclarations : List String
  quotientIdentificationResult : String
  selectedComponentIsColimitResult : String
  projectionFieldsResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpSelectedComponentQuotientIdentificationV370SupportState :
    AddCommGrpSelectedComponentQuotientIdentificationV370SupportState where
  seed := supportSeed
  checkedDeclarations :=
    ["supportSeed",
      "SelectedComponentQuotientIdentificationInputsW463",
      "selectedComponentπ₁_isColimit_of_quotientIdentification_w463",
      "selectedComponentπ₂_isColimit_of_quotientIdentification_w463",
      "selectedComponentπ₃_isColimit_of_quotientIdentification_w463",
      "selectedProjectionComponentIsColimitInputs_of_quotientIdentifications_w463"]
  quotientIdentificationResult := "proved"
  selectedComponentIsColimitResult := "proved"
  projectionFieldsResult := "proved"
  remainingInputs :=
    ["At the call site, supply the three AddCommGrp point isomorphisms from `cs.pt.Xᵢ` to the forgotten explicit cokernel quotients.",
      "At the call site, prove the three selected component legs compose with those isomorphisms to the forgotten explicit quotient projections.",
      "At the call site, supply the three explicit quotient `IsColimit` proofs, for example from the closed-range quotient support."]
  productSuccessClaimed := false

theorem currentAddCommGrpSelectedComponentQuotientIdentificationV370SupportState_productSuccess :
    currentAddCommGrpSelectedComponentQuotientIdentificationV370SupportState.productSuccessClaimed =
      false :=
  rfl

section Checks

#check supportSeed
#check SelectedComponentQuotientIdentificationInputsW463
#check selectedComponentπ₁_isColimit_of_quotientIdentification_w463
#check selectedComponentπ₂_isColimit_of_quotientIdentification_w463
#check selectedComponentπ₃_isColimit_of_quotientIdentification_w463
#check selectedProjectionComponentIsColimitInputs_of_quotientIdentifications_w463
#check currentAddCommGrpSelectedComponentQuotientIdentificationV370SupportState_productSuccess

end Checks

end AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463

end LeanLCAExactChallenge


/-!
W464: projection fields plus AddCommGrp row fields boundary.

Seed: `ee3109d3f37256d88905bcbb`.

This file composes W457's projection-field input surface with W459's canonical
selected-difference kernel row, giving a small wrapper from projection component
fields plus AddCommGrp row fields to strict SnakeInput cokernel data.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464

open AddCommGrpSnakeInputDifferenceCokernel
open WppOpExactAcyclicFrontierConsolidatedW318

/-- Reproducible support seed recorded for the worker result contract. -/
def supportSeed : String :=
  "ee3109d3f37256d88905bcbb"

/-- Local name for the short-complex functor forgetting topology. -/
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

/-- The selected metrizable target leg is a cokernel cofork for `(left - right)`. -/
def selectedMetrizableTargetCokernelCofork
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    CokernelCofork (selectedMetrizableLeft S - selectedMetrizableRight S) :=
  Preadditive.cokernelCoforkOfCofork (selectedMetrizableTargetCofork S cs)

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

/-- The mapped selected cofork and selected forgotten cofork differ only by precomposition. -/
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

/-- Projection-field input surface for the selected mapped short-complex cofork. -/
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

/-- Componentwise cokernel-colimit data for the selected mapped cofork. -/
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

/-- Projection fields are exactly the three fields of the componentwise input package. -/
def selectedMappedCokernelComponentwiseInputsOfProjectionFields
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (H : SelectedProjectionComponentIsColimitInputs S cs) :
    SelectedMappedCokernelComponentwiseInputs S cs where
  hπ₁ := H.1
  hπ₂ := H.2.1
  hπ₃ := H.2.2

/-- Componentwise projection inputs assemble into the mapped short-complex cofork. -/
def selectedMappedCokernelColimitOfComponentwise
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (H : SelectedMappedCokernelComponentwiseInputs S cs) :
    IsColimit
      ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor) :=
  ShortComplex.isColimitOfIsColimitπ
    ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor)
    H.hπ₁ H.hπ₂ H.hπ₃

/-- W452 bridge: componentwise selected mapped cokernel inputs imply the forgotten cofork. -/
def selectedForgottenTargetCokernelColimitOfComponentwise
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (H : SelectedMappedCokernelComponentwiseInputs S cs) :
    IsColimit (selectedForgottenTargetCokernelCofork S cs) := by
  let p : parallelPair
      (forgottenShortComplexFunctor.map
        (selectedMetrizableLeft S - selectedMetrizableRight S)) 0 ≅
      parallelPair (selectedForgottenLeft S - selectedForgottenRight S) 0 :=
    parallelPair.eqOfHomEq forgottenShortComplexFunctor.map_sub rfl
  let hMap :
      IsColimit
        ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor) :=
    selectedMappedCokernelColimitOfComponentwise H
  let hPre :
      IsColimit
        ((Cocone.precompose p.hom).obj (selectedForgottenTargetCokernelCofork S cs)) :=
    IsColimit.ofIsoColimit hMap
      (precomposeSelectedForgottenCokernelCoforkIsoMap S cs).symm
  exact (IsColimit.precomposeHomEquiv p (selectedForgottenTargetCokernelCofork S cs)) hPre

/-- A strict short exact row supplies W318's three AddCommGrp row inputs. -/
def addCommGrpStrictInputsOfStrictShortExact
    {S : ShortComplex MetrizableLCA.{0}}
    (hS : MetrizableLCA.strictShortExact S) :
    AddCommGrpLeftInjective (S.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
      AddCommGrpKernelExact (S.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
        AddCommGrpRightSurjective (S.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) :=
  ⟨hS.closed_inclusion.injective, hS.algebraic_exact, hS.surjective⟩

/-- A strict WPP-op family supplies W318's row-input family. -/
def addCommGrpStrictInputsFamilyOfStrictShortExact
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    (hS : ∀ j, MetrizableLCA.strictShortExact (S.obj j)) :
    ∀ j,
      AddCommGrpLeftInjective
          ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
        AddCommGrpKernelExact ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
          AddCommGrpRightSurjective
            ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) :=
  fun j => addCommGrpStrictInputsOfStrictShortExact (hS j)

/-- Selected WPP-op source/target adapter for the difference-cokernel route. -/
def selectedWppOpParallelPairDifferenceStrictCokernelData_of_addCommGrpRows
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    (hRows : ∀ j : WalkingParallelPairᵒᵖ,
      AddCommGrpLeftInjective
          ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
        AddCommGrpKernelExact ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
          AddCommGrpRightSurjective
            ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})))
    {L₃ : ShortComplex AddCommGrpCat.{0}}
    (q :
      (S.obj ordinaryTargetIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) ⟶
        L₃)
    (w : (selectedForgottenLeft S - selectedForgottenRight S) ≫ q = 0 := by cat_disch)
    (L₀ : ShortComplex AddCommGrpCat.{0})
    (i :
      L₀ ⟶
        (S.obj ordinarySourceIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}))
    (wi : i ≫ (selectedForgottenLeft S - selectedForgottenRight S) = 0 := by cat_disch)
    (h₀ : IsLimit (KernelFork.ofι i wi))
    (h₃ : IsColimit (CokernelCofork.ofπ q w)) :
    ParallelPairDifferenceStrictCokernelData
      ((S.obj ordinarySourceIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}))
      ((S.obj ordinaryTargetIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}))
      L₃ where
  u := selectedForgottenLeft S
  v := selectedForgottenRight S
  q := q
  w := w
  L₀ := L₀
  i := i
  wi := wi
  h₀ := h₀
  h₃ := h₃
  L₁_kernelExact := (hRows ordinarySourceIndex).2.1
  L₁_rightSurjective := (hRows ordinarySourceIndex).2.2
  L₂_kernelExact := (hRows ordinaryTargetIndex).2.1
  L₂_leftInjective := (hRows ordinaryTargetIndex).1

/-- The selected target cofork supplies the strict SnakeInput cokernel data. -/
def strictSnakeCokernelData_of_componentwiseSelectedCokernel
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (hRows : ∀ j : WalkingParallelPairᵒᵖ,
      AddCommGrpLeftInjective
          ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
        AddCommGrpKernelExact ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
          AddCommGrpRightSurjective
            ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})))
    (H : SelectedMappedCokernelComponentwiseInputs S cs)
    (L₀ : ShortComplex AddCommGrpCat.{0})
    (i : L₀ ⟶ (S.obj ordinarySourceIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}))
    (wi : i ≫ (selectedForgottenLeft S - selectedForgottenRight S) = 0 := by cat_disch)
    (h₀ : IsLimit (KernelFork.ofι i wi)) :
  AddCommGrpStrictSnakeCokernelData
      (cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) :=
  strictSnakeCokernelData_of_parallelPairDifferenceStrictCokernelData
    (selectedWppOpParallelPairDifferenceStrictCokernelData_of_addCommGrpRows
      hRows (selectedForgottenTargetCoconeLeg S cs)
      (selectedForgottenTargetCokernelCofork S cs).condition L₀ i wi h₀
      (selectedForgottenTargetCokernelColimitOfComponentwise H))
    (Iso.refl _)

/-- The canonical kernel row for the selected forgotten difference map. -/
abbrev selectedDifferenceKernelRow
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    ShortComplex AddCommGrpCat.{0} :=
  kernel (selectedForgottenLeft S - selectedForgottenRight S)

/-- The kernel inclusion for the selected forgotten difference map. -/
abbrev selectedDifferenceKernelι
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    selectedDifferenceKernelRow S ⟶
      (S.obj ordinarySourceIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) :=
  kernel.ι (selectedForgottenLeft S - selectedForgottenRight S)

/-- The canonical kernel inclusion kills the selected forgotten difference map. -/
theorem selectedDifferenceKernelι_condition
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    selectedDifferenceKernelι S ≫
        (selectedForgottenLeft S - selectedForgottenRight S) =
      0 :=
  kernel.condition (selectedForgottenLeft S - selectedForgottenRight S)

/-- The canonical selected difference kernel fork is limiting. -/
def selectedDifferenceKernelIsLimit
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    IsLimit
      (KernelFork.ofι (selectedDifferenceKernelι S)
        (selectedDifferenceKernelι_condition S)) :=
  kernelIsKernel (selectedForgottenLeft S - selectedForgottenRight S)

/--
The W456 strict SnakeInput cokernel data with the remaining kernel-row input
filled by the categorical kernel of the selected forgotten difference map.
-/
def strictSnakeCokernelData_of_componentwiseSelectedCokernel_kernelRow
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (hRows : ∀ j : WalkingParallelPairᵒᵖ,
      AddCommGrpLeftInjective
          ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
        AddCommGrpKernelExact ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
          AddCommGrpRightSurjective
            ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})))
    (H : SelectedMappedCokernelComponentwiseInputs S cs) :
    AddCommGrpStrictSnakeCokernelData
      (cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) :=
  strictSnakeCokernelData_of_componentwiseSelectedCokernel hRows H
    (selectedDifferenceKernelRow S) (selectedDifferenceKernelι S)
    (selectedDifferenceKernelι_condition S) (selectedDifferenceKernelIsLimit S)

/--
Projection component fields plus strict source rows give strict SnakeInput
cokernel data for the forgotten selected target short complex.
-/
def strictSnakeCokernelData_of_projectionComponentFields_addCommGrpRows
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (hRows : ∀ j : WalkingParallelPairᵒᵖ,
      AddCommGrpLeftInjective
          ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
        AddCommGrpKernelExact ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
          AddCommGrpRightSurjective
            ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})))
    (H : SelectedProjectionComponentIsColimitInputs S cs) :
    AddCommGrpStrictSnakeCokernelData
      (cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) :=
  strictSnakeCokernelData_of_componentwiseSelectedCokernel_kernelRow hRows
    (selectedMappedCokernelComponentwiseInputsOfProjectionFields H)

/-- W318 consumer: the projection-field wrapper also supplies AddCommGrp kernel exactness. -/
theorem addCommGrpKernelExact_of_projectionComponentFields_addCommGrpRows
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (hRows : ∀ j : WalkingParallelPairᵒᵖ,
      AddCommGrpLeftInjective
          ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
        AddCommGrpKernelExact ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
          AddCommGrpRightSurjective
            ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})))
    (H : SelectedProjectionComponentIsColimitInputs S cs) :
    AddCommGrpKernelExact
      (cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) :=
  addCommGrpKernelExact_of_strictSnakeCokernelData _
    (strictSnakeCokernelData_of_projectionComponentFields_addCommGrpRows hRows H)

/-- Projection component fields supply W318's AddCommGrp row-field boundary. -/
theorem addCommGrpStrictKernelExactBoundary_of_projectionComponentFields
    (hproj : ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
      (cs : Cocone S), IsColimit cs → SelectedProjectionComponentIsColimitInputs S cs) :
    addCommGrpStrictKernelExact_wppOp_colimit_boundary_for_metrizable := by
  intro S cs hcs hRows
  exact addCommGrpKernelExact_of_projectionComponentFields_addCommGrpRows hRows
    (hproj S cs hcs)

/-- Projection component fields plus the left strictness boundary imply exact acyclicity. -/
theorem exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_projectionComponentFields
    (hclosed : wppOp_lca_colimitMap_injective_inducing_closedImage)
    (hproj : ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
      (cs : Cocone S), IsColimit cs → SelectedProjectionComponentIsColimitInputs S cs) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_addCommGrpStrict
    hclosed (addCommGrpStrictKernelExactBoundary_of_projectionComponentFields hproj)

/-- W464 checked support state. -/
structure AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportState : Type where
  seed : String
  checkedDeclarations : List String
  projectionToComponentwiseResult : String
  strictSnakeResult : String
  kernelRowResult : String
  kernelExactResult : String
  boundaryResult : String
  exactAcyclicWrapperResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked support state for W464. -/
def currentAddCommGrpRowFieldsProjectionKernelBoundaryV370SupportState :
    AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportState where
  seed := supportSeed
  checkedDeclarations :=
    ["supportSeed",
      "SelectedProjectionComponentIsColimitInputs",
      "SelectedMappedCokernelComponentwiseInputs",
      "selectedMappedCokernelComponentwiseInputsOfProjectionFields",
      "selectedMappedCokernelColimitOfComponentwise",
      "selectedForgottenTargetCokernelColimitOfComponentwise",
      "addCommGrpStrictInputsOfStrictShortExact",
      "addCommGrpStrictInputsFamilyOfStrictShortExact",
      "selectedWppOpParallelPairDifferenceStrictCokernelData_of_addCommGrpRows",
      "strictSnakeCokernelData_of_componentwiseSelectedCokernel",
      "selectedDifferenceKernelRow",
      "selectedDifferenceKernelι",
      "selectedDifferenceKernelι_condition",
      "selectedDifferenceKernelIsLimit",
      "strictSnakeCokernelData_of_componentwiseSelectedCokernel_kernelRow",
      "strictSnakeCokernelData_of_projectionComponentFields_addCommGrpRows",
      "addCommGrpKernelExact_of_projectionComponentFields_addCommGrpRows",
      "addCommGrpStrictKernelExactBoundary_of_projectionComponentFields",
      "exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_projectionComponentFields"]
  projectionToComponentwiseResult := "proved"
  strictSnakeResult := "proved"
  kernelRowResult := "proved"
  kernelExactResult := "proved"
  boundaryResult := "proved"
  exactAcyclicWrapperResult := "proved"
  remainingInputs := []
  productSuccessClaimed := false

theorem currentAddCommGrpRowFieldsProjectionKernelBoundaryV370SupportState_productSuccess :
    currentAddCommGrpRowFieldsProjectionKernelBoundaryV370SupportState.productSuccessClaimed =
      false :=
  rfl

section Checks

#check supportSeed
#check SelectedProjectionComponentIsColimitInputs
#check SelectedMappedCokernelComponentwiseInputs
#check selectedMappedCokernelComponentwiseInputsOfProjectionFields
#check selectedMappedCokernelColimitOfComponentwise
#check selectedForgottenTargetCokernelColimitOfComponentwise
#check addCommGrpStrictInputsOfStrictShortExact
#check addCommGrpStrictInputsFamilyOfStrictShortExact
#check selectedWppOpParallelPairDifferenceStrictCokernelData_of_addCommGrpRows
#check strictSnakeCokernelData_of_componentwiseSelectedCokernel
#check selectedDifferenceKernelRow
#check selectedDifferenceKernelι
#check selectedDifferenceKernelι_condition
#check selectedDifferenceKernelIsLimit
#check strictSnakeCokernelData_of_componentwiseSelectedCokernel_kernelRow
#check strictSnakeCokernelData_of_projectionComponentFields_addCommGrpRows
#check addCommGrpKernelExact_of_projectionComponentFields_addCommGrpRows
#check addCommGrpStrictKernelExactBoundary_of_projectionComponentFields
#check exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_projectionComponentFields
#check currentAddCommGrpRowFieldsProjectionKernelBoundaryV370SupportState_productSuccess

end Checks

end AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464

end LeanLCAExactChallenge

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpQuotientIdentificationExactAcyclicBoundaryV370SupportW467

open AddCommGrpSnakeInputDifferenceCokernel
open WppOpExactAcyclicFrontierConsolidatedW318

/-!
W467: quotient-identification to exact-acyclic boundary.

Seed: `fba669c7dd85612f026c92ca`.

This final support layer composes W463 quotient-identification data with the
W464 projection-field consumer. The seed is recorded only for worker diversity;
it is not mathematical evidence.
-/

/-- Worker seed recorded before W467 edits. -/
def supportSeed : String :=
  "fba669c7dd85612f026c92ca"

/--
W463 quotient-identification inputs produce W464's selected projection
component `IsColimit` fields.
-/
def selectedProjectionComponentIsColimitInputs_of_quotientIdentifications_w467
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463.SelectedComponentQuotientIdentificationInputsW463 S cs) :
    AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464.SelectedProjectionComponentIsColimitInputs S cs := by
  simpa [AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464.SelectedProjectionComponentIsColimitInputs,
    AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464.selectedMetrizableTargetCokernelCofork,
    AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464.selectedMetrizableTargetCofork,
    AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464.selectedMetrizableTargetCoconeLeg,
    AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464.selectedMetrizableLeft,
    AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464.selectedMetrizableRight,
    AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464.forgottenShortComplexFunctor,
    AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463.SelectedProjectionComponentIsColimitInputs,
    AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463.selectedForgottenShortComplexCokernelCofork,
    AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463.selectedMetrizableTargetCokernelCofork,
    AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463.selectedMetrizableTargetCofork,
    AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463.selectedMetrizableTargetCoconeLeg,
    AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463.selectedMetrizableDifference,
    AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463.selectedMetrizableLeft,
    AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463.selectedMetrizableRight,
    AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463.forgottenShortComplexFunctor] using
    (AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463.selectedProjectionComponentIsColimitInputs_of_quotientIdentifications_w463 h)

/--
Quotient-identification inputs supply the AddCommGrp strict kernel exactness
boundary by way of W464's projection-field wrapper.
-/
theorem addCommGrpStrictKernelExactBoundary_of_quotientIdentifications_w467
    (hquot :
      ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
        (cs : Cocone S), IsColimit cs →
          AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463.SelectedComponentQuotientIdentificationInputsW463 S cs) :
    addCommGrpStrictKernelExact_wppOp_colimit_boundary_for_metrizable :=
  AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464.addCommGrpStrictKernelExactBoundary_of_projectionComponentFields
    (fun S cs hcs =>
      selectedProjectionComponentIsColimitInputs_of_quotientIdentifications_w467
        (hquot S cs hcs))

/--
Left closed-embedding input plus quotient-identification inputs imply the
walking-parallel-pair-op exact-acyclic colimit closure.
-/
theorem exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_quotientIdentifications_w467
    (hclosed : wppOp_lca_colimitMap_injective_inducing_closedImage)
    (hquot :
      ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
        (cs : Cocone S), IsColimit cs →
          AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463.SelectedComponentQuotientIdentificationInputsW463 S cs) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464.exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_projectionComponentFields
    hclosed
    (fun S cs hcs =>
      selectedProjectionComponentIsColimitInputs_of_quotientIdentifications_w467
        (hquot S cs hcs))

/-- Machine-readable W467 support state. -/
structure AddCommGrpQuotientIdentificationExactAcyclicBoundaryV370SupportState : Type where
  seed : String
  checkedDeclarations : List String
  projectionFieldsResult : String
  kernelExactBoundaryResult : String
  exactAcyclicWrapperResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked support state for W467. -/
def currentAddCommGrpQuotientIdentificationExactAcyclicBoundaryV370SupportState :
    AddCommGrpQuotientIdentificationExactAcyclicBoundaryV370SupportState where
  seed := supportSeed
  checkedDeclarations :=
    ["supportSeed",
      "selectedProjectionComponentIsColimitInputs_of_quotientIdentifications_w467",
      "addCommGrpStrictKernelExactBoundary_of_quotientIdentifications_w467",
      "exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_quotientIdentifications_w467"]
  projectionFieldsResult := "proved"
  kernelExactBoundaryResult := "proved"
  exactAcyclicWrapperResult := "proved"
  remainingInputs :=
    ["At each colimit call site, provide W463 quotient-identification inputs: three point isomorphisms, three leg/projection identifications, and three explicit quotient `IsColimit` proofs.",
      "Provide the W318/W464 left closed-embedding input `wppOp_lca_colimitMap_injective_inducing_closedImage` for the exact-acyclic closure theorem."]
  productSuccessClaimed := false

theorem currentAddCommGrpQuotientIdentificationExactAcyclicBoundaryV370SupportState_productSuccess :
    currentAddCommGrpQuotientIdentificationExactAcyclicBoundaryV370SupportState.productSuccessClaimed =
      false :=
  rfl

section Checks

#check supportSeed
#check selectedProjectionComponentIsColimitInputs_of_quotientIdentifications_w467
#check addCommGrpStrictKernelExactBoundary_of_quotientIdentifications_w467
#check exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_quotientIdentifications_w467
#check currentAddCommGrpQuotientIdentificationExactAcyclicBoundaryV370SupportState_productSuccess

end Checks

end AddCommGrpQuotientIdentificationExactAcyclicBoundaryV370SupportW467

end LeanLCAExactChallenge

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace AddCommGrpClosedRangePointIdentificationExactAcyclicV370SupportW470

open AddCommGrpSnakeInputDifferenceCokernel
open WppOpExactAcyclicFrontierConsolidatedW318
open MetrizableLCA
open AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463

/-!
W470: closed-range point-identification to exact-acyclic boundary.

Seed: `bd8d298ff9b97d190ead8bfdef25cbc9`.

This standalone support layer weakens W467's quotient-identification inputs to
closed-range point-identification data. The seed is recorded only for worker
diversity; it is not mathematical evidence.
-/

/-- Worker seed recorded before W470 edits. -/
def supportSeed : String :=
  "bd8d298ff9b97d190ead8bfdef25cbc9"

/-- The algebraic range subgroup of the forgotten source map. -/
abbrev forgottenAlgebraicRangeSubgroup {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    AddSubgroup (underlyingForgetfulFunctor.obj Y) :=
  AddSubgroup.map (underlyingForgetfulFunctor.map f).hom
    (⊤ : AddSubgroup (underlyingForgetfulFunctor.obj X))

/-- The same algebraic range subgroup, kept in the topological target object. -/
abbrev algebraicRangeSubgroup {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    AddSubgroup Y :=
  AddSubgroup.map f.hom.toAddMonoidHom (⊤ : AddSubgroup X)

/-- The local algebraic range subgroup has carrier `Set.range f`. -/
theorem mem_algebraicRangeSubgroup_iff {X Y : MetrizableLCA.{0}}
    (f : X ⟶ Y) (y : Y) :
    y ∈ algebraicRangeSubgroup f ↔ y ∈ Set.range (f : X → Y) := by
  constructor
  · intro hy
    rcases hy with ⟨x, _hx, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, trivial, rfl⟩

/-- The forgotten algebraic range subgroup has the same carrier as the topological one. -/
theorem mem_forgottenAlgebraicRangeSubgroup_iff {X Y : MetrizableLCA.{0}}
    (f : X ⟶ Y) (y : Y) :
    y ∈ forgottenAlgebraicRangeSubgroup f ↔ y ∈ algebraicRangeSubgroup f := by
  rw [mem_algebraicRangeSubgroup_iff]
  constructor
  · intro hy
    rcases hy with ⟨x, _hx, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, trivial, rfl⟩

/-- Closedness of the underlying set range gives closedness of the algebraic range subgroup. -/
theorem isClosed_algebraicRangeSubgroup_of_isClosed_range
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosed : IsClosed (Set.range (f : X → Y))) :
    IsClosed (algebraicRangeSubgroup f : Set Y) := by
  rwa [Set.ext_iff.mpr (mem_algebraicRangeSubgroup_iff f)]

/-- In `Y`, a closed algebraic range is equal to the closed cokernel subgroup. -/
theorem algebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosed : IsClosed (Set.range (f : X → Y))) :
    algebraicRangeSubgroup f = cokernelSubgroup f := by
  apply le_antisymm
  · exact range_le_cokernelSubgroup f
  · unfold cokernelSubgroup
    apply AddSubgroup.topologicalClosure_minimal
    · intro y hy
      exact hy
    · exact isClosed_algebraicRangeSubgroup_of_isClosed_range f hclosed

/-- Closed-range equality needed by the explicit AddCommGrp cokernel proof. -/
theorem forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosed : IsClosed (Set.range (f : X → Y))) :
    forgottenAlgebraicRangeSubgroup f =
      (cokernelSubgroup f : AddSubgroup (underlyingForgetfulFunctor.obj Y)) := by
  ext y
  constructor
  · intro hy
    have hyalg : y ∈ algebraicRangeSubgroup f :=
      (mem_forgottenAlgebraicRangeSubgroup_iff f y).mp hy
    rw [algebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range f hclosed] at hyalg
    exact hyalg
  · intro hy
    have hyalg : y ∈ algebraicRangeSubgroup f := by
      rw [algebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range f hclosed]
      exact hy
    exact (mem_forgottenAlgebraicRangeSubgroup_iff f y).mpr hyalg

/-- The closed-range quotient projection is surjective after forgetting to `AddCommGrpCat`. -/
theorem forgottenCokernelπ_surjective {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    Function.Surjective (forgottenCokernelπ f) :=
  QuotientAddGroup.mk'_surjective (cokernelSubgroup f)

/-- The algebraic range lies in the kernel of every cofork morphism. -/
theorem algebraicRange_le_ker_of_forgotten_condition {X Y : MetrizableLCA.{0}}
    (f : X ⟶ Y) {Z : AddCommGrpCat.{0}} (k : underlyingForgetfulFunctor.obj Y ⟶ Z)
    (hk : underlyingForgetfulFunctor.map f ≫ k = 0) :
    forgottenAlgebraicRangeSubgroup f ≤ k.hom.ker := by
  intro y hy
  rcases hy with ⟨x, _hx, rfl⟩
  change k (f x) = 0
  have h := congrArg (fun q : underlyingForgetfulFunctor.obj X ⟶ Z => q x) hk
  simpa using h

/-- Closed-range comparison upgrades the cofork equation to closed-subgroup kernel containment. -/
theorem closureKernel_of_forgottenAlgebraicRange_eq_cokernelSubgroup
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hRange :
      forgottenAlgebraicRangeSubgroup f =
        (cokernelSubgroup f : AddSubgroup (underlyingForgetfulFunctor.obj Y)))
    {Z : AddCommGrpCat.{0}} (k : underlyingForgetfulFunctor.obj Y ⟶ Z)
    (hk : underlyingForgetfulFunctor.map f ≫ k = 0) :
    cokernelSubgroup f ≤ k.hom.ker := by
  rw [← hRange]
  exact algebraicRange_le_ker_of_forgotten_condition f k hk

/-- Descend an AddCommGrp target map through the forgotten closed-range quotient. -/
def forgottenCokernelDesc {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    {Z : AddCommGrpCat.{0}} (k : underlyingForgetfulFunctor.obj Y ⟶ Z)
    (hkClosure : cokernelSubgroup f ≤ k.hom.ker) :
    underlyingForgetfulFunctor.obj (cokernelObj f) ⟶ Z :=
  AddCommGrpCat.ofHom
    (QuotientAddGroup.lift (cokernelSubgroup f) k.hom hkClosure)

/-- The descended AddCommGrp map composes with the quotient projection to the original map. -/
theorem forgottenCokernelπ_desc {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    {Z : AddCommGrpCat.{0}} (k : underlyingForgetfulFunctor.obj Y ⟶ Z)
    (hkClosure : cokernelSubgroup f ≤ k.hom.ker) :
    forgottenCokernelπ f ≫ forgottenCokernelDesc f k hkClosure = k := by
  ext y
  rfl

/-- Uniqueness of the descended AddCommGrp map from the surjective quotient projection. -/
theorem forgottenCokernelDesc_unique {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    {Z : AddCommGrpCat.{0}} (k : underlyingForgetfulFunctor.obj Y ⟶ Z)
    (hkClosure : cokernelSubgroup f ≤ k.hom.ker)
    (m : underlyingForgetfulFunctor.obj (cokernelObj f) ⟶ Z)
    (hm : forgottenCokernelπ f ≫ m = k) :
    m = forgottenCokernelDesc f k hkClosure := by
  haveI : Epi (forgottenCokernelπ f) :=
    (AddCommGrpCat.epi_iff_surjective (forgottenCokernelπ f)).mpr
      (forgottenCokernelπ_surjective f)
  apply (cancel_epi (forgottenCokernelπ f)).mp
  rw [hm, forgottenCokernelπ_desc]

/-- Equality between algebraic range and closed cokernel subgroup proves the explicit cofork. -/
def forgottenExplicitCokernelCoforkIsColimit_of_forgottenAlgebraicRange_eq
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hRange :
      forgottenAlgebraicRangeSubgroup f =
        (cokernelSubgroup f : AddSubgroup (underlyingForgetfulFunctor.obj Y))) :
    IsColimit (forgottenExplicitCokernelCofork f) :=
  CokernelCofork.IsColimit.ofπ (forgottenCokernelπ f) (forgottenCokernelπ_condition f)
    (fun k hk =>
      forgottenCokernelDesc f k
        (closureKernel_of_forgottenAlgebraicRange_eq_cokernelSubgroup f hRange k hk))
    (fun k hk =>
      forgottenCokernelπ_desc f k
        (closureKernel_of_forgottenAlgebraicRange_eq_cokernelSubgroup f hRange k hk))
    (fun k hk m hm =>
      forgottenCokernelDesc_unique f k
        (closureKernel_of_forgottenAlgebraicRange_eq_cokernelSubgroup f hRange k hk) m hm)

/-- Closed range proves the explicit AddCommGrp cokernel cofork is colimiting. -/
def forgottenExplicitCokernelCoforkIsColimit_of_isClosed_range
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosed : IsClosed (Set.range (f : X → Y))) :
    IsColimit (forgottenExplicitCokernelCofork f) :=
  forgottenExplicitCokernelCoforkIsColimit_of_forgottenAlgebraicRange_eq f
    (forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range f hclosed)

/-- Closed-range point-identification inputs for the selected three components. -/
structure SelectedComponentPointIdentificationClosedRangeInputsW470
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 where
  pointIsoπ₁ :
    underlyingForgetfulFunctor.obj (cs.pt.X₁) ≅
      underlyingForgetfulFunctor.obj (cokernelObj (selectedMetrizableDifferenceπ₁ S))
  pointIsoπ₂ :
    underlyingForgetfulFunctor.obj (cs.pt.X₂) ≅
      underlyingForgetfulFunctor.obj (cokernelObj (selectedMetrizableDifferenceπ₂ S))
  pointIsoπ₃ :
    underlyingForgetfulFunctor.obj (cs.pt.X₃) ≅
      underlyingForgetfulFunctor.obj (cokernelObj (selectedMetrizableDifferenceπ₃ S))
  legπ₁ :
    underlyingForgetfulFunctor.map (selectedMetrizableTargetCoconeLeg S cs).τ₁ ≫
      pointIsoπ₁.hom =
        forgottenCokernelπ (selectedMetrizableDifferenceπ₁ S)
  legπ₂ :
    underlyingForgetfulFunctor.map (selectedMetrizableTargetCoconeLeg S cs).τ₂ ≫
      pointIsoπ₂.hom =
        forgottenCokernelπ (selectedMetrizableDifferenceπ₂ S)
  legπ₃ :
    underlyingForgetfulFunctor.map (selectedMetrizableTargetCoconeLeg S cs).τ₃ ≫
      pointIsoπ₃.hom =
        forgottenCokernelπ (selectedMetrizableDifferenceπ₃ S)
  closedRangeπ₁ :
    IsClosed (Set.range
      (selectedMetrizableDifferenceπ₁ S :
        (S.obj ordinarySourceIndex).X₁ → (S.obj ordinaryTargetIndex).X₁))
  closedRangeπ₂ :
    IsClosed (Set.range
      (selectedMetrizableDifferenceπ₂ S :
        (S.obj ordinarySourceIndex).X₂ → (S.obj ordinaryTargetIndex).X₂))
  closedRangeπ₃ :
    IsClosed (Set.range
      (selectedMetrizableDifferenceπ₃ S :
        (S.obj ordinarySourceIndex).X₃ → (S.obj ordinaryTargetIndex).X₃))

/-- Closed-range point identifications supply W463's quotient-identification inputs. -/
def selectedComponentQuotientIdentificationInputs_of_closedRange_w470
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentPointIdentificationClosedRangeInputsW470 S cs) :
    SelectedComponentQuotientIdentificationInputsW463 S cs where
  pointIsoπ₁ := h.pointIsoπ₁
  pointIsoπ₂ := h.pointIsoπ₂
  pointIsoπ₃ := h.pointIsoπ₃
  legπ₁ := h.legπ₁
  legπ₂ := h.legπ₂
  legπ₃ := h.legπ₃
  explicitπ₁CokernelIsColimit :=
    forgottenExplicitCokernelCoforkIsColimit_of_isClosed_range
      (selectedMetrizableDifferenceπ₁ S) h.closedRangeπ₁
  explicitπ₂CokernelIsColimit :=
    forgottenExplicitCokernelCoforkIsColimit_of_isClosed_range
      (selectedMetrizableDifferenceπ₂ S) h.closedRangeπ₂
  explicitπ₃CokernelIsColimit :=
    forgottenExplicitCokernelCoforkIsColimit_of_isClosed_range
      (selectedMetrizableDifferenceπ₃ S) h.closedRangeπ₃

/-- Closed-range point identifications provide all W464 projected component fields. -/
def selectedProjectionComponentIsColimitInputs_of_closedRangePointIdentifications_w470
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentPointIdentificationClosedRangeInputsW470 S cs) :
    AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464.SelectedProjectionComponentIsColimitInputs S cs :=
  AddCommGrpQuotientIdentificationExactAcyclicBoundaryV370SupportW467.selectedProjectionComponentIsColimitInputs_of_quotientIdentifications_w467
    (selectedComponentQuotientIdentificationInputs_of_closedRange_w470 h)

/--
Closed-range point-identification inputs supply the AddCommGrp strict kernel
exactness boundary by way of W467 and W464.
-/
theorem addCommGrpStrictKernelExactBoundary_of_closedRangePointIdentifications_w470
    (hclosedRange :
      ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
        (cs : Cocone S), IsColimit cs →
          SelectedComponentPointIdentificationClosedRangeInputsW470 S cs) :
    addCommGrpStrictKernelExact_wppOp_colimit_boundary_for_metrizable :=
  AddCommGrpQuotientIdentificationExactAcyclicBoundaryV370SupportW467.addCommGrpStrictKernelExactBoundary_of_quotientIdentifications_w467
    (fun S cs hcs =>
      selectedComponentQuotientIdentificationInputs_of_closedRange_w470
        (hclosedRange S cs hcs))

/--
Left closed-embedding input plus closed-range point-identification inputs imply
the walking-parallel-pair-op exact-acyclic colimit closure.
-/
theorem exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_closedRangePointIdentifications_w470
    (hclosed : wppOp_lca_colimitMap_injective_inducing_closedImage)
    (hclosedRange :
      ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
        (cs : Cocone S), IsColimit cs →
          SelectedComponentPointIdentificationClosedRangeInputsW470 S cs) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  AddCommGrpQuotientIdentificationExactAcyclicBoundaryV370SupportW467.exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_quotientIdentifications_w467
    hclosed
    (fun S cs hcs =>
      selectedComponentQuotientIdentificationInputs_of_closedRange_w470
        (hclosedRange S cs hcs))

/-- Machine-readable W470 support state. -/
structure AddCommGrpClosedRangePointIdentificationExactAcyclicV370SupportState : Type where
  seed : String
  checkedDeclarations : List String
  projectionFieldsResult : String
  kernelExactBoundaryResult : String
  exactAcyclicWrapperResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked support state for W470. -/
def currentAddCommGrpClosedRangePointIdentificationExactAcyclicV370SupportState :
    AddCommGrpClosedRangePointIdentificationExactAcyclicV370SupportState where
  seed := supportSeed
  checkedDeclarations :=
    ["supportSeed",
      "SelectedComponentPointIdentificationClosedRangeInputsW470",
      "selectedProjectionComponentIsColimitInputs_of_closedRangePointIdentifications_w470",
      "addCommGrpStrictKernelExactBoundary_of_closedRangePointIdentifications_w470",
      "exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_closedRangePointIdentifications_w470"]
  projectionFieldsResult := "proved"
  kernelExactBoundaryResult := "proved"
  exactAcyclicWrapperResult := "proved"
  remainingInputs :=
    ["At each colimit call site, provide three AddCommGrp point isomorphisms from `cs.pt.Xᵢ` to the forgotten explicit cokernel quotients.",
      "At each colimit call site, prove the three selected component legs compose with those isomorphisms to the forgotten explicit quotient projections.",
      "At each colimit call site, provide the three closed-range hypotheses for the selected component difference maps.",
      "Provide the W464/W318 AddCommGrp row fields and the left closed-embedding input `wppOp_lca_colimitMap_injective_inducing_closedImage` required by the exact-acyclic closure theorem."]
  productSuccessClaimed := false

theorem currentAddCommGrpClosedRangePointIdentificationExactAcyclicV370SupportState_productSuccess :
    currentAddCommGrpClosedRangePointIdentificationExactAcyclicV370SupportState.productSuccessClaimed =
      false :=
  rfl

section Checks

#check supportSeed
#check SelectedComponentPointIdentificationClosedRangeInputsW470
#check selectedProjectionComponentIsColimitInputs_of_closedRangePointIdentifications_w470
#check addCommGrpStrictKernelExactBoundary_of_closedRangePointIdentifications_w470
#check exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_closedRangePointIdentifications_w470
#check currentAddCommGrpClosedRangePointIdentificationExactAcyclicV370SupportState_productSuccess

end Checks

end AddCommGrpClosedRangePointIdentificationExactAcyclicV370SupportW470

namespace AddCommGrpW426LeftClosedClosedRangeExactAcyclicV370SupportW473

open WppOpExactAcyclicFrontierConsolidatedW318

/-!
W473: compose W441's W426 ordinary-map-promotion left-closedness bridge with
W470's closed-range point-identification exact-acyclic wrapper.

Seed: `1c7c01337603ac2316cf85bfd77ef3a5`.

The seed is recorded only for worker diversity; it is not mathematical evidence.
-/

/-- Worker seed recorded before W473 edits. -/
def supportSeed : String :=
  "1c7c01337603ac2316cf85bfd77ef3a5"

/-- Ordinary diagram associated to a `WalkingParallelPairᵒᵖ` diagram. -/
abbrev wppOpOrdinaryDiagramW473 (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    WalkingParallelPair ⥤ MetrizableLCA.{0} :=
  walkingParallelPairOpEquiv.functor ⋙ X

/-- Domain object of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpDomainW473 (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : MetrizableLCA.{0} :=
  (wppOpOrdinaryDiagramW473 X).obj WalkingParallelPair.zero

/-- Codomain object of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpCodomainW473 (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : MetrizableLCA.{0} :=
  (wppOpOrdinaryDiagramW473 X).obj WalkingParallelPair.one

/-- Left arrow of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpLeftW473 (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    wppOpDomainW473 X ⟶ wppOpCodomainW473 X :=
  (wppOpOrdinaryDiagramW473 X).map WalkingParallelPairHom.left

/-- Right arrow of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpRightW473 (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    wppOpDomainW473 X ⟶ wppOpCodomainW473 X :=
  (wppOpOrdinaryDiagramW473 X).map WalkingParallelPairHom.right

/-- Ordinary quotient point used by the W426 descended quotient map. -/
abbrev wppOpOrdinaryQuotientPointW473
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : MetrizableLCA.{0} :=
  MetrizableLCA.quotientObj (wppOpCodomainW473 X)
    (MetrizableLCA.cokernelSubgroup (wppOpLeftW473 X - wppOpRightW473 X))
    (AddSubgroup.isClosed_topologicalClosure _)

/-- W318's per-object colimit-map compatibility equation. -/
abbrev W318ColimitMapLegCompatibilityW473
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt) : Prop :=
  ∀ j : WalkingParallelPairᵒᵖ, cx.ι.app j ≫ φ = α.app j ≫ cy.ι.app j

/--
Concrete W426 ordinary descended quotient-map package. It carries the ordinary
descended morphism, its quotient compatibility equation, and the topology facts
that must be transported across the ordinary/canonical colimit-map equality.
-/
structure W426OrdinaryDescendedMapPackageW473
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagramW473 X ⟶ wppOpOrdinaryDiagramW473 Y) : Type 1 where
  ordinaryDescended :
    wppOpOrdinaryQuotientPointW473 X ⟶ wppOpOrdinaryQuotientPointW473 Y
  quotient_compat :
    MetrizableLCA.quotientMap (wppOpCodomainW473 X)
        (MetrizableLCA.cokernelSubgroup (wppOpLeftW473 X - wppOpRightW473 X))
        (AddSubgroup.isClosed_topologicalClosure _) ≫ ordinaryDescended =
      ordinaryMap.app WalkingParallelPair.one ≫
        MetrizableLCA.quotientMap (wppOpCodomainW473 Y)
          (MetrizableLCA.cokernelSubgroup (wppOpLeftW473 Y - wppOpRightW473 Y))
          (AddSubgroup.isClosed_topologicalClosure _)
  descended_injective :
    Function.Injective (ordinaryDescended :
      wppOpOrdinaryQuotientPointW473 X → wppOpOrdinaryQuotientPointW473 Y)
  descended_inducing :
    IsInducing (ordinaryDescended :
      wppOpOrdinaryQuotientPointW473 X → wppOpOrdinaryQuotientPointW473 Y)
  descended_range_closed :
    IsClosed (Set.range (ordinaryDescended :
      wppOpOrdinaryQuotientPointW473 X → wppOpOrdinaryQuotientPointW473 Y))

/--
Typed promotion from the W426 ordinary map package to one W318 colimit-map
instance. The ordinary/canonical equality remains an explicit frontier input.
-/
structure W426OrdinaryMapPromotionToW318FieldsW473
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagramW473 X ⟶ wppOpOrdinaryDiagramW473 Y)
    (α : X ⟶ Y) (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt) : Type 1 where
  ordinaryPackage : W426OrdinaryDescendedMapPackageW473 ordinaryMap
  ordinaryDescendedMapName : String
  quotientCompatibilityName : String
  sourcePointIdentificationName : String
  targetPointIdentificationName : String
  canonicalWppOpColimitMapName : String
  ordinaryEqualsCanonicalColimitMap : Prop
  ordinaryEqualsCanonicalColimitMapName : String
  ordinaryEqualsCanonicalImpliesLegCompatibility :
    ordinaryEqualsCanonicalColimitMap →
      W318ColimitMapLegCompatibilityW473 X Y α cx cy φ
  ordinaryTopologyTransportsToColimitMap :
    ordinaryEqualsCanonicalColimitMap →
      Function.Injective (φ : cx.pt → cy.pt) ∧
        IsInducing (φ : cx.pt → cy.pt) ∧
        IsClosed (Set.range (φ : cx.pt → cy.pt))

/--
W473 alias for the W441 ordinary-map promotion: W426 promotion fields derive
W318's left closed-range colimit-map hypothesis.
-/
theorem wppOp_lca_colimitMap_injective_inducing_closedImage_of_w426Promotion_w473
    (hfields :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0})
        (ordinaryMap : (wppOpOrdinaryDiagramW473 X) ⟶ (wppOpOrdinaryDiagramW473 Y))
        (α : X ⟶ Y) (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
          IsColimit cx →
            IsColimit cy →
              (∀ j : WalkingParallelPairᵒᵖ,
                IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
                W318ColimitMapLegCompatibilityW473 X Y α cx cy φ →
                  W426OrdinaryMapPromotionToW318FieldsW473 ordinaryMap α cx cy φ)
    (hordinaryMap :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
        (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
          IsColimit cx →
            IsColimit cy →
              (∀ j : WalkingParallelPairᵒᵖ,
                IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
                W318ColimitMapLegCompatibilityW473 X Y α cx cy φ →
                  ((wppOpOrdinaryDiagramW473 X) ⟶ (wppOpOrdinaryDiagramW473 Y)))
    (heq :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
        (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt)
        (hcx : IsColimit cx) (hcy : IsColimit cy)
        (hclosed : ∀ j : WalkingParallelPairᵒᵖ,
          IsClosedEmbedding (α.app j : X.obj j → Y.obj j))
        (hcompat : W318ColimitMapLegCompatibilityW473 X Y α cx cy φ),
          (hfields X Y (hordinaryMap X Y α cx cy φ hcx hcy hclosed hcompat)
            α cx cy φ hcx hcy hclosed hcompat).ordinaryEqualsCanonicalColimitMap) :
    wppOp_lca_colimitMap_injective_inducing_closedImage := by
  intro X Y α cx cy φ hcx hcy hclosed hcompat
  let ordinaryMap := hordinaryMap X Y α cx cy φ hcx hcy hclosed hcompat
  let fields := hfields X Y ordinaryMap α cx cy φ hcx hcy hclosed hcompat
  exact fields.ordinaryTopologyTransportsToColimitMap
    (heq X Y α cx cy φ hcx hcy hclosed hcompat)

/--
W473 composition theorem: derive W318 left closedness from W426 promotion fields,
then feed W470 closed-range point-identification data to the exact-acyclic
closure theorem.
-/
theorem exactAcyclic_walkingParallelPairOp_colimit_closure_of_w426Promotion_and_closedRangePointIdentifications_w473
    (hfields :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0})
        (ordinaryMap : (wppOpOrdinaryDiagramW473 X) ⟶ (wppOpOrdinaryDiagramW473 Y))
        (α : X ⟶ Y) (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
          IsColimit cx →
            IsColimit cy →
              (∀ j : WalkingParallelPairᵒᵖ,
                IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
                W318ColimitMapLegCompatibilityW473 X Y α cx cy φ →
                  W426OrdinaryMapPromotionToW318FieldsW473 ordinaryMap α cx cy φ)
    (hordinaryMap :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
        (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
          IsColimit cx →
            IsColimit cy →
              (∀ j : WalkingParallelPairᵒᵖ,
                IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
                W318ColimitMapLegCompatibilityW473 X Y α cx cy φ →
                  ((wppOpOrdinaryDiagramW473 X) ⟶ (wppOpOrdinaryDiagramW473 Y)))
    (heq :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
        (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt)
        (hcx : IsColimit cx) (hcy : IsColimit cy)
        (hclosed : ∀ j : WalkingParallelPairᵒᵖ,
          IsClosedEmbedding (α.app j : X.obj j → Y.obj j))
        (hcompat : W318ColimitMapLegCompatibilityW473 X Y α cx cy φ),
          (hfields X Y (hordinaryMap X Y α cx cy φ hcx hcy hclosed hcompat)
            α cx cy φ hcx hcy hclosed hcompat).ordinaryEqualsCanonicalColimitMap)
    (hclosedRange :
      ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
        (cs : Cocone S), IsColimit cs →
          _root_.LeanLCAExactChallenge.AddCommGrpClosedRangePointIdentificationExactAcyclicV370SupportW470.SelectedComponentPointIdentificationClosedRangeInputsW470 S cs) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  _root_.LeanLCAExactChallenge.AddCommGrpClosedRangePointIdentificationExactAcyclicV370SupportW470.exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_closedRangePointIdentifications_w470
      (wppOp_lca_colimitMap_injective_inducing_closedImage_of_w426Promotion_w473
        hfields hordinaryMap heq)
      hclosedRange

def checkedDeclarationsW473 : List String :=
  ["supportSeed",
    "W426OrdinaryDescendedMapPackageW473",
    "W426OrdinaryMapPromotionToW318FieldsW473",
    "wppOp_lca_colimitMap_injective_inducing_closedImage_of_w426Promotion_w473",
    "exactAcyclic_walkingParallelPairOp_colimit_closure_of_w426Promotion_and_closedRangePointIdentifications_w473"]

def remainingInputsW473 : List String :=
  ["For each compatible WPP-op colimit map, provide the W426 ordinary descended map package.",
    "For each compatible WPP-op colimit map, provide the ordinary map and ordinary/canonical colimit-map equality witness.",
    "For each ShortComplex WPP-op colimit call site, provide W470 closed-range point-identification data."]

structure AddCommGrpW426LeftClosedClosedRangeExactAcyclicV370SupportStateW473 : Type where
  seed : String
  checkedDeclarations : List String
  remainingInputs : List String
  leftClosedResult : String
  exactAcyclicWrapperResult : String
  productSuccessClaimed : Bool

def currentAddCommGrpW426LeftClosedClosedRangeExactAcyclicV370SupportStateW473 :
    AddCommGrpW426LeftClosedClosedRangeExactAcyclicV370SupportStateW473 where
  seed := supportSeed
  checkedDeclarations := checkedDeclarationsW473
  remainingInputs := remainingInputsW473
  leftClosedResult := "proved from W426 ordinary-map promotion inputs"
  exactAcyclicWrapperResult := "proved by composing W426 promotion with W470 closed-range point-identification wrapper"
  productSuccessClaimed := false

theorem currentAddCommGrpW426LeftClosedClosedRangeExactAcyclicV370SupportStateW473_productSuccess :
    currentAddCommGrpW426LeftClosedClosedRangeExactAcyclicV370SupportStateW473.productSuccessClaimed =
      false :=
  rfl

section Checks

#check supportSeed
#check W426OrdinaryDescendedMapPackageW473
#check W426OrdinaryMapPromotionToW318FieldsW473
#check wppOp_lca_colimitMap_injective_inducing_closedImage_of_w426Promotion_w473
#check exactAcyclic_walkingParallelPairOp_colimit_closure_of_w426Promotion_and_closedRangePointIdentifications_w473
#check currentAddCommGrpW426LeftClosedClosedRangeExactAcyclicV370SupportStateW473_productSuccess

end Checks

end AddCommGrpW426LeftClosedClosedRangeExactAcyclicV370SupportW473

namespace AddCommGrpW426LeftClosedQuotientIdentificationExactAcyclicV370SupportW478

open WppOpExactAcyclicFrontierConsolidatedW318

/-!
W478: compose W441/W426 ordinary-map-promotion left closedness with W467's
quotient-identification exact-acyclic wrapper.

Seed: `478c0de185`.

The seed is recorded only for worker diversity; it is not mathematical evidence.
-/

/-- Worker seed recorded before W478 edits. -/
def supportSeed : String :=
  "478c0de185"

/-- Ordinary diagram associated to a `WalkingParallelPairᵒᵖ` diagram. -/
abbrev wppOpOrdinaryDiagramW478 (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    WalkingParallelPair ⥤ MetrizableLCA.{0} :=
  AddCommGrpW426LeftClosedClosedRangeExactAcyclicV370SupportW473.wppOpOrdinaryDiagramW473 X

/-- W318's per-object colimit-map compatibility equation. -/
abbrev W318ColimitMapLegCompatibilityW478
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt) : Prop :=
  AddCommGrpW426LeftClosedClosedRangeExactAcyclicV370SupportW473.W318ColimitMapLegCompatibilityW473
    X Y α cx cy φ

/-- W478 alias for the W473/W426 ordinary descended quotient-map package. -/
abbrev W426OrdinaryDescendedMapPackageW478
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagramW478 X ⟶ wppOpOrdinaryDiagramW478 Y) : Type 1 :=
  AddCommGrpW426LeftClosedClosedRangeExactAcyclicV370SupportW473.W426OrdinaryDescendedMapPackageW473
    ordinaryMap

/-- W478 alias for the W426 ordinary-map promotion fields used by W473. -/
abbrev W426OrdinaryMapPromotionToW318FieldsW478
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagramW478 X ⟶ wppOpOrdinaryDiagramW478 Y)
    (α : X ⟶ Y) (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt) : Type 1 :=
  AddCommGrpW426LeftClosedClosedRangeExactAcyclicV370SupportW473.W426OrdinaryMapPromotionToW318FieldsW473
    ordinaryMap α cx cy φ

/--
W426 promotion fields derive W318's left closed-range colimit-map hypothesis.
-/
theorem wppOp_lca_colimitMap_injective_inducing_closedImage_of_w426Promotion_w478
    (hfields :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0})
        (ordinaryMap : (wppOpOrdinaryDiagramW478 X) ⟶ (wppOpOrdinaryDiagramW478 Y))
        (α : X ⟶ Y) (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
          IsColimit cx →
            IsColimit cy →
              (∀ j : WalkingParallelPairᵒᵖ,
                IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
                W318ColimitMapLegCompatibilityW478 X Y α cx cy φ →
                  W426OrdinaryMapPromotionToW318FieldsW478 ordinaryMap α cx cy φ)
    (hordinaryMap :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
        (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
          IsColimit cx →
            IsColimit cy →
              (∀ j : WalkingParallelPairᵒᵖ,
                IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
                W318ColimitMapLegCompatibilityW478 X Y α cx cy φ →
                  ((wppOpOrdinaryDiagramW478 X) ⟶ (wppOpOrdinaryDiagramW478 Y)))
    (heq :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
        (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt)
        (hcx : IsColimit cx) (hcy : IsColimit cy)
        (hclosed : ∀ j : WalkingParallelPairᵒᵖ,
          IsClosedEmbedding (α.app j : X.obj j → Y.obj j))
        (hcompat : W318ColimitMapLegCompatibilityW478 X Y α cx cy φ),
          (hfields X Y (hordinaryMap X Y α cx cy φ hcx hcy hclosed hcompat)
            α cx cy φ hcx hcy hclosed hcompat).ordinaryEqualsCanonicalColimitMap) :
    wppOp_lca_colimitMap_injective_inducing_closedImage :=
  _root_.LeanLCAExactChallenge.AddCommGrpW426LeftClosedClosedRangeExactAcyclicV370SupportW473.wppOp_lca_colimitMap_injective_inducing_closedImage_of_w426Promotion_w473
    hfields hordinaryMap heq

/--
W478 composition theorem: derive W318 left closedness from W426 promotion fields,
then feed W467 quotient-identification data to the exact-acyclic closure theorem.
-/
theorem exactAcyclic_walkingParallelPairOp_colimit_closure_of_w426Promotion_and_quotientIdentifications_w478
    (hfields :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0})
        (ordinaryMap : (wppOpOrdinaryDiagramW478 X) ⟶ (wppOpOrdinaryDiagramW478 Y))
        (α : X ⟶ Y) (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
          IsColimit cx →
            IsColimit cy →
              (∀ j : WalkingParallelPairᵒᵖ,
                IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
                W318ColimitMapLegCompatibilityW478 X Y α cx cy φ →
                  W426OrdinaryMapPromotionToW318FieldsW478 ordinaryMap α cx cy φ)
    (hordinaryMap :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
        (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
          IsColimit cx →
            IsColimit cy →
              (∀ j : WalkingParallelPairᵒᵖ,
                IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
                W318ColimitMapLegCompatibilityW478 X Y α cx cy φ →
                  ((wppOpOrdinaryDiagramW478 X) ⟶ (wppOpOrdinaryDiagramW478 Y)))
    (heq :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
        (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt)
        (hcx : IsColimit cx) (hcy : IsColimit cy)
        (hclosed : ∀ j : WalkingParallelPairᵒᵖ,
          IsClosedEmbedding (α.app j : X.obj j → Y.obj j))
        (hcompat : W318ColimitMapLegCompatibilityW478 X Y α cx cy φ),
          (hfields X Y (hordinaryMap X Y α cx cy φ hcx hcy hclosed hcompat)
            α cx cy φ hcx hcy hclosed hcompat).ordinaryEqualsCanonicalColimitMap)
    (hquotientIdentifications :
      ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
        (cs : Cocone S), IsColimit cs →
          _root_.LeanLCAExactChallenge.AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463.SelectedComponentQuotientIdentificationInputsW463
            S cs) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  _root_.LeanLCAExactChallenge.AddCommGrpQuotientIdentificationExactAcyclicBoundaryV370SupportW467.exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_quotientIdentifications_w467
    (wppOp_lca_colimitMap_injective_inducing_closedImage_of_w426Promotion_w478
      hfields hordinaryMap heq)
    hquotientIdentifications

def checkedDeclarationsW478 : List String :=
  ["supportSeed",
    "W426OrdinaryDescendedMapPackageW478",
    "W426OrdinaryMapPromotionToW318FieldsW478",
    "wppOp_lca_colimitMap_injective_inducing_closedImage_of_w426Promotion_w478",
    "exactAcyclic_walkingParallelPairOp_colimit_closure_of_w426Promotion_and_quotientIdentifications_w478"]

def remainingInputsW478 : List String :=
  ["For each compatible WPP-op colimit map, provide the W426 ordinary descended map package.",
    "For each compatible WPP-op colimit map, provide the ordinary map and ordinary/canonical colimit-map equality witness.",
    "For each ShortComplex WPP-op colimit call site, provide W463 selected component quotient-identification data."]

structure AddCommGrpW426LeftClosedQuotientIdentificationExactAcyclicV370SupportStateW478 :
    Type where
  seed : String
  checkedDeclarations : List String
  remainingInputs : List String
  leftClosedResult : String
  exactAcyclicWrapperResult : String
  productSuccessClaimed : Bool

def currentAddCommGrpW426LeftClosedQuotientIdentificationExactAcyclicV370SupportStateW478 :
    AddCommGrpW426LeftClosedQuotientIdentificationExactAcyclicV370SupportStateW478 where
  seed := supportSeed
  checkedDeclarations := checkedDeclarationsW478
  remainingInputs := remainingInputsW478
  leftClosedResult := "proved from W426 ordinary-map promotion inputs"
  exactAcyclicWrapperResult := "proved by composing W426 promotion with W467 quotient-identification wrapper"
  productSuccessClaimed := false

theorem currentAddCommGrpW426LeftClosedQuotientIdentificationExactAcyclicV370SupportStateW478_productSuccess :
    currentAddCommGrpW426LeftClosedQuotientIdentificationExactAcyclicV370SupportStateW478.productSuccessClaimed =
      false :=
  rfl

section Checks

#check supportSeed
#check W426OrdinaryDescendedMapPackageW478
#check W426OrdinaryMapPromotionToW318FieldsW478
#check wppOp_lca_colimitMap_injective_inducing_closedImage_of_w426Promotion_w478
#check exactAcyclic_walkingParallelPairOp_colimit_closure_of_w426Promotion_and_quotientIdentifications_w478
#check currentAddCommGrpW426LeftClosedQuotientIdentificationExactAcyclicV370SupportStateW478_productSuccess

end Checks

end AddCommGrpW426LeftClosedQuotientIdentificationExactAcyclicV370SupportW478

end LeanLCAExactChallenge
