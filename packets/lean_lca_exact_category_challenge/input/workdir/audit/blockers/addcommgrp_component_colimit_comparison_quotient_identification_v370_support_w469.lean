import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel
import LeanLCAExactChallenge.LCA.Cokernel
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

namespace AddCommGrpComponentColimitComparisonQuotientIdentificationV370SupportW469

open AddCommGrpSnakeInputDifferenceCokernel
open WppOpExactAcyclicFrontierConsolidatedW318
open MetrizableLCA
open AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463

/-- Worker seed recorded before edits, used only to diversify proof search. -/
def supportSeedW469 : String := "609fc474ca14ac1abbf4d0a557af4907"

/--
Inputs for deriving W463's selected component quotient-identification package
from colimit comparison: selected component cofork colimits plus explicit
quotient cofork colimits, but no pre-supplied point isomorphisms or leg
equations.
-/
structure SelectedComponentColimitComparisonInputsW469
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 where
  selectedπ₁CokernelIsColimit :
    IsColimit (selectedForgottenComponentπ₁CokernelCofork S cs)
  selectedπ₂CokernelIsColimit :
    IsColimit (selectedForgottenComponentπ₂CokernelCofork S cs)
  selectedπ₃CokernelIsColimit :
    IsColimit (selectedForgottenComponentπ₃CokernelCofork S cs)
  explicitπ₁CokernelIsColimit :
    IsColimit (forgottenExplicitCokernelCofork (selectedMetrizableDifferenceπ₁ S))
  explicitπ₂CokernelIsColimit :
    IsColimit (forgottenExplicitCokernelCofork (selectedMetrizableDifferenceπ₂ S))
  explicitπ₃CokernelIsColimit :
    IsColimit (forgottenExplicitCokernelCofork (selectedMetrizableDifferenceπ₃ S))

/-- The first selected component point isomorphism from colimit uniqueness. -/
def selectedComponentπ₁PointIso_of_colimitComparison_w469
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentColimitComparisonInputsW469 S cs) :
    underlyingForgetfulFunctor.obj (cs.pt.X₁) ≅
      underlyingForgetfulFunctor.obj (cokernelObj (selectedMetrizableDifferenceπ₁ S)) :=
  h.selectedπ₁CokernelIsColimit.coconePointUniqueUpToIso h.explicitπ₁CokernelIsColimit

/-- The second selected component point isomorphism from colimit uniqueness. -/
def selectedComponentπ₂PointIso_of_colimitComparison_w469
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentColimitComparisonInputsW469 S cs) :
    underlyingForgetfulFunctor.obj (cs.pt.X₂) ≅
      underlyingForgetfulFunctor.obj (cokernelObj (selectedMetrizableDifferenceπ₂ S)) :=
  h.selectedπ₂CokernelIsColimit.coconePointUniqueUpToIso h.explicitπ₂CokernelIsColimit

/-- The third selected component point isomorphism from colimit uniqueness. -/
def selectedComponentπ₃PointIso_of_colimitComparison_w469
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentColimitComparisonInputsW469 S cs) :
    underlyingForgetfulFunctor.obj (cs.pt.X₃) ≅
      underlyingForgetfulFunctor.obj (cokernelObj (selectedMetrizableDifferenceπ₃ S)) :=
  h.selectedπ₃CokernelIsColimit.coconePointUniqueUpToIso h.explicitπ₃CokernelIsColimit

/-- The first selected component leg equation follows from colimit-point uniqueness. -/
theorem selectedComponentπ₁Leg_eq_of_colimitComparison_w469
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentColimitComparisonInputsW469 S cs) :
    underlyingForgetfulFunctor.map (selectedMetrizableTargetCoconeLeg S cs).τ₁ ≫
      (selectedComponentπ₁PointIso_of_colimitComparison_w469 h).hom =
        forgottenCokernelπ (selectedMetrizableDifferenceπ₁ S) := by
  simpa [selectedComponentπ₁PointIso_of_colimitComparison_w469,
    selectedForgottenComponentπ₁CokernelCofork, forgottenExplicitCokernelCofork] using
      (IsColimit.comp_coconePointUniqueUpToIso_hom h.selectedπ₁CokernelIsColimit
        h.explicitπ₁CokernelIsColimit WalkingParallelPair.one)

/-- The second selected component leg equation follows from colimit-point uniqueness. -/
theorem selectedComponentπ₂Leg_eq_of_colimitComparison_w469
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentColimitComparisonInputsW469 S cs) :
    underlyingForgetfulFunctor.map (selectedMetrizableTargetCoconeLeg S cs).τ₂ ≫
      (selectedComponentπ₂PointIso_of_colimitComparison_w469 h).hom =
        forgottenCokernelπ (selectedMetrizableDifferenceπ₂ S) := by
  simpa [selectedComponentπ₂PointIso_of_colimitComparison_w469,
    selectedForgottenComponentπ₂CokernelCofork, forgottenExplicitCokernelCofork] using
      (IsColimit.comp_coconePointUniqueUpToIso_hom h.selectedπ₂CokernelIsColimit
        h.explicitπ₂CokernelIsColimit WalkingParallelPair.one)

/-- The third selected component leg equation follows from colimit-point uniqueness. -/
theorem selectedComponentπ₃Leg_eq_of_colimitComparison_w469
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentColimitComparisonInputsW469 S cs) :
    underlyingForgetfulFunctor.map (selectedMetrizableTargetCoconeLeg S cs).τ₃ ≫
      (selectedComponentπ₃PointIso_of_colimitComparison_w469 h).hom =
        forgottenCokernelπ (selectedMetrizableDifferenceπ₃ S) := by
  simpa [selectedComponentπ₃PointIso_of_colimitComparison_w469,
    selectedForgottenComponentπ₃CokernelCofork, forgottenExplicitCokernelCofork] using
      (IsColimit.comp_coconePointUniqueUpToIso_hom h.selectedπ₃CokernelIsColimit
        h.explicitπ₃CokernelIsColimit WalkingParallelPair.one)

/--
Component cofork colimit comparison supplies W463's point isomorphisms, leg
equations, and explicit quotient cofork colimit proofs.
-/
def selectedComponentQuotientIdentificationInputs_of_colimitComparison_w469
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentColimitComparisonInputsW469 S cs) :
    SelectedComponentQuotientIdentificationInputsW463 S cs where
  pointIsoπ₁ := selectedComponentπ₁PointIso_of_colimitComparison_w469 h
  pointIsoπ₂ := selectedComponentπ₂PointIso_of_colimitComparison_w469 h
  pointIsoπ₃ := selectedComponentπ₃PointIso_of_colimitComparison_w469 h
  legπ₁ := selectedComponentπ₁Leg_eq_of_colimitComparison_w469 h
  legπ₂ := selectedComponentπ₂Leg_eq_of_colimitComparison_w469 h
  legπ₃ := selectedComponentπ₃Leg_eq_of_colimitComparison_w469 h
  explicitπ₁CokernelIsColimit := h.explicitπ₁CokernelIsColimit
  explicitπ₂CokernelIsColimit := h.explicitπ₂CokernelIsColimit
  explicitπ₃CokernelIsColimit := h.explicitπ₃CokernelIsColimit

/-- Machine-readable W469 support state. -/
structure AddCommGrpComponentColimitComparisonQuotientIdentificationV370SupportState : Type where
  seed : String
  checkedDeclarations : List String
  quotientIdentificationResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpComponentColimitComparisonQuotientIdentificationV370SupportState :
    AddCommGrpComponentColimitComparisonQuotientIdentificationV370SupportState where
  seed := supportSeedW469
  checkedDeclarations :=
    ["supportSeedW469",
      "SelectedComponentColimitComparisonInputsW469",
      "selectedComponentπ₁PointIso_of_colimitComparison_w469",
      "selectedComponentπ₂PointIso_of_colimitComparison_w469",
      "selectedComponentπ₃PointIso_of_colimitComparison_w469",
      "selectedComponentπ₁Leg_eq_of_colimitComparison_w469",
      "selectedComponentπ₂Leg_eq_of_colimitComparison_w469",
      "selectedComponentπ₃Leg_eq_of_colimitComparison_w469",
      "selectedComponentQuotientIdentificationInputs_of_colimitComparison_w469"]
  quotientIdentificationResult := "proved"
  remainingInputs :=
    ["At the call site, supply selected component cofork `IsColimit` proofs.",
      "At the call site, supply explicit quotient cofork `IsColimit` proofs."]
  productSuccessClaimed := false

theorem currentAddCommGrpComponentColimitComparisonQuotientIdentificationV370SupportState_productSuccess :
    currentAddCommGrpComponentColimitComparisonQuotientIdentificationV370SupportState.productSuccessClaimed =
      false :=
  rfl

section Checks

#check supportSeedW469
#check SelectedComponentColimitComparisonInputsW469
#check selectedComponentπ₁PointIso_of_colimitComparison_w469
#check selectedComponentπ₂PointIso_of_colimitComparison_w469
#check selectedComponentπ₃PointIso_of_colimitComparison_w469
#check selectedComponentπ₁Leg_eq_of_colimitComparison_w469
#check selectedComponentπ₂Leg_eq_of_colimitComparison_w469
#check selectedComponentπ₃Leg_eq_of_colimitComparison_w469
#check selectedComponentQuotientIdentificationInputs_of_colimitComparison_w469
#check currentAddCommGrpComponentColimitComparisonQuotientIdentificationV370SupportState_productSuccess

end Checks

end AddCommGrpComponentColimitComparisonQuotientIdentificationV370SupportW469

end LeanLCAExactChallenge
