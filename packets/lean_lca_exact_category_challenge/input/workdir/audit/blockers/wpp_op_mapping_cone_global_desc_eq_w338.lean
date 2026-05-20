import LeanLCAExactChallenge.Derived.MappingConeFiniteProduct

/-!
W338: global descEq for the W308 mapping-cone assembly.

W333-W337 reduced the W308 `descEq` field to standard colimit and mapping-cone
algebra.  This file packages the reduction into one import-safe theorem:
if the test mapping-cone legs are natural and the global right mediator has the
expected `mappingCone.inr` leg equations, then the descended left cochain
satisfies the global `mappingCone.desc` differential equation.

The remaining W308 work after this file is mostly instantiating the theorem with
the included bounded `c₁/c₂` cocones and packaging it into the ambient desc
assembly.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WppOpMappingConeGlobalDescEqW338

open CochainComplex

/-- Naturality of test legs over the objectwise mapping-cone diagram. -/
abbrev MappingConeTestLegNaturality {J : Type} [Category J]
    {X₁ X₂ : J ⥤ CochainComplex MetrizableLCA.{0} ℤ}
    (f : X₁ ⟶ X₂)
    {T : CochainComplex MetrizableLCA.{0} ℤ}
    (leg : ∀ j : J, mappingCone (f.app j) ⟶ T) : Prop :=
  ∀ {j j' : J} (α : j ⟶ j'),
    mappingCone.map (f.app j) (f.app j') (X₁.map α) (X₂.map α) (f.naturality α).symm ≫
      leg j' = leg j

/-- Objectwise left cochain from a mapping-cone test leg. -/
noncomputable def objectwiseLeftFromLeg
    {K L T : CochainComplex MetrizableLCA.{0} ℤ}
    (φ : K ⟶ L) (leg : mappingCone φ ⟶ T) :
    HomComplex.Cochain K T (-1) :=
  (mappingCone.inl φ).comp (HomComplex.Cochain.ofHom leg) (add_zero (-1))

/-- Compatibility of the objectwise left cochains induced by natural test legs. -/
theorem objectwiseLeftFromLeg_compatible {J : Type} [Category J]
    {X₁ X₂ : J ⥤ CochainComplex MetrizableLCA.{0} ℤ}
    (f : X₁ ⟶ X₂)
    {T : CochainComplex MetrizableLCA.{0} ℤ}
    (leg : ∀ j : J, mappingCone (f.app j) ⟶ T)
    (hleg : MappingConeTestLegNaturality f leg)
    {j j' : J} (α : j ⟶ j') (p q : ℤ) (hpq : p + (-1 : ℤ) = q) :
    (X₁.map α).f p ≫ (objectwiseLeftFromLeg (f.app j') (leg j')).v p q hpq =
      (objectwiseLeftFromLeg (f.app j) (leg j)).v p q hpq := by
  calc
    (X₁.map α).f p ≫ (objectwiseLeftFromLeg (f.app j') (leg j')).v p q hpq =
        (mappingCone.inl (f.app j)).v p q hpq ≫
          (mappingCone.map (f.app j) (f.app j') (X₁.map α) (X₂.map α)
            (f.naturality α).symm ≫ leg j').f q := by
        simp [objectwiseLeftFromLeg, mappingCone.map, Category.assoc]
    _ = (mappingCone.inl (f.app j)).v p q hpq ≫ (leg j).f q := by
        rw [hleg α]
    _ = (objectwiseLeftFromLeg (f.app j) (leg j)).v p q hpq := by
        simp [objectwiseLeftFromLeg]

/-- Degreewise cocone used in the assembled left-cochain construction. -/
noncomputable def assembledLeftEvalCocone {J : Type} [Category J]
    {X₁ X₂ : J ⥤ CochainComplex MetrizableLCA.{0} ℤ}
    (f : X₁ ⟶ X₂)
    {T : CochainComplex MetrizableLCA.{0} ℤ}
    (leg : ∀ j : J, mappingCone (f.app j) ⟶ T)
    (hleg : MappingConeTestLegNaturality f leg)
    (p q : ℤ) (hpq : p + (-1 : ℤ) = q) :
    Cocone (X₁ ⋙ HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p) where
  pt := T.X q
  ι :=
    { app := fun j => (objectwiseLeftFromLeg (f.app j) (leg j)).v p q hpq
      naturality := by
        intro j j' α
        exact objectwiseLeftFromLeg_compatible f leg hleg α p q hpq }

/-- The descended left cochain assembled directly from mapping-cone test legs. -/
noncomputable def leftCochainOfMappingConeLegs {J : Type} [Category J]
    {X₁ X₂ : J ⥤ CochainComplex MetrizableLCA.{0} ℤ}
    {c₁ : Cocone X₁} (hc₁ : IsColimit c₁)
    [∀ p : ℤ, PreservesColimit X₁
      (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p)]
    (f : X₁ ⟶ X₂)
    {T : CochainComplex MetrizableLCA.{0} ℤ}
    (leg : ∀ j : J, mappingCone (f.app j) ⟶ T)
    (hleg : MappingConeTestLegNaturality f leg) :
    HomComplex.Cochain c₁.pt T (-1) :=
  HomComplex.Cochain.mk (fun p q hpq =>
    (isColimitOfPreserves
      (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p) hc₁).desc
      (assembledLeftEvalCocone f leg hleg p q hpq))

/-- The assembled left cochain has the expected `mappingCone.inl` leg equation. -/
theorem leftCochainOfMappingConeLegs_comp_fac {J : Type} [Category J]
    {X₁ X₂ : J ⥤ CochainComplex MetrizableLCA.{0} ℤ}
    {c₁ : Cocone X₁} (hc₁ : IsColimit c₁)
    [∀ p : ℤ, PreservesColimit X₁
      (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p)]
    (f : X₁ ⟶ X₂)
    {T : CochainComplex MetrizableLCA.{0} ℤ}
    (leg : ∀ j : J, mappingCone (f.app j) ⟶ T)
    (hleg : MappingConeTestLegNaturality f leg)
    (j : J) :
    (HomComplex.Cochain.ofHom (c₁.ι.app j)).comp
        (leftCochainOfMappingConeLegs hc₁ f leg hleg) (zero_add (-1)) =
      objectwiseLeftFromLeg (f.app j) (leg j) := by
  apply HomComplex.Cochain.ext
  intro p q hpq
  simpa [leftCochainOfMappingConeLegs, HomComplex.Cochain.ofHom_comp] using
    (isColimitOfPreserves
      (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p) hc₁).fac
      (assembledLeftEvalCocone f leg hleg p q hpq) j

/-- Objectwise descEq for the left cochain candidate. -/
theorem objectwiseLeftFromLeg_descEq
    {K L T : CochainComplex MetrizableLCA.{0} ℤ}
    (φ : K ⟶ L) (leg : mappingCone φ ⟶ T) :
    HomComplex.δ (-1) 0 (objectwiseLeftFromLeg φ leg) =
      HomComplex.Cochain.ofHom (φ ≫ mappingCone.inr φ ≫ leg) := by
  simp [objectwiseLeftFromLeg, HomComplex.Cochain.ofHom_comp]

/-- Objectwise right terms form a cocone whenever the test legs are natural. -/
theorem objectwiseRightFromLeg_natural {J : Type} [Category J]
    {X₁ X₂ : J ⥤ CochainComplex MetrizableLCA.{0} ℤ}
    (f : X₁ ⟶ X₂)
    {T : CochainComplex MetrizableLCA.{0} ℤ}
    (leg : ∀ j : J, mappingCone (f.app j) ⟶ T)
    (hleg : MappingConeTestLegNaturality f leg)
    {j j' : J} (α : j ⟶ j') :
    X₂.map α ≫ (mappingCone.inr (f.app j') ≫ leg j') =
      mappingCone.inr (f.app j) ≫ leg j := by
  calc
    X₂.map α ≫ (mappingCone.inr (f.app j') ≫ leg j') =
        (mappingCone.inr (f.app j) ≫
          mappingCone.map (f.app j) (f.app j') (X₁.map α) (X₂.map α)
            (f.naturality α).symm) ≫ leg j' := by
        simp [mappingCone.map, Category.assoc]
    _ = mappingCone.inr (f.app j) ≫
          (mappingCone.map (f.app j) (f.app j') (X₁.map α) (X₂.map α)
            (f.naturality α).symm ≫ leg j') := by
        simp [Category.assoc]
    _ = mappingCone.inr (f.app j) ≫ leg j := by
        rw [hleg α]

/-- The cocone on `X₁` whose legs are `f.app j ≫ mappingCone.inr (f.app j) ≫ leg j`. -/
noncomputable def rightSideObjectwiseCocone {J : Type} [Category J]
    {X₁ X₂ : J ⥤ CochainComplex MetrizableLCA.{0} ℤ}
    (f : X₁ ⟶ X₂)
    {T : CochainComplex MetrizableLCA.{0} ℤ}
    (leg : ∀ j : J, mappingCone (f.app j) ⟶ T)
    (hleg : MappingConeTestLegNaturality f leg) :
    Cocone X₁ where
  pt := T
  ι :=
    { app := fun j => f.app j ≫ mappingCone.inr (f.app j) ≫ leg j
      naturality := by
        intro j j' α
        calc
          X₁.map α ≫ (f.app j' ≫ mappingCone.inr (f.app j') ≫ leg j') =
              (X₁.map α ≫ f.app j') ≫ mappingCone.inr (f.app j') ≫ leg j' := by
              simp [Category.assoc]
          _ = (f.app j ≫ X₂.map α) ≫ mappingCone.inr (f.app j') ≫ leg j' := by
              rw [f.naturality α]
          _ = f.app j ≫ (X₂.map α ≫ (mappingCone.inr (f.app j') ≫ leg j')) := by
              simp [Category.assoc]
          _ = f.app j ≫ (mappingCone.inr (f.app j) ≫ leg j) := by
              rw [objectwiseRightFromLeg_natural f leg hleg α]
          _ = f.app j ≫ mappingCone.inr (f.app j) ≫ leg j := by
              simp }

/-- `δ` commutes with precomposition by a colimit leg, in the W308 form. -/
theorem delta_of_colimit_leg_comp {A B T : CochainComplex MetrizableLCA.{0} ℤ}
    (ι : A ⟶ B) (z : HomComplex.Cochain B T (-1)) :
    HomComplex.δ (-1) 0
        ((HomComplex.Cochain.ofHom ι).comp z (zero_add (-1))) =
      (HomComplex.Cochain.ofHom ι).comp
        (HomComplex.δ (-1) 0 z) (zero_add 0) := by
  simp

/-- Rewrite the global `δ` after a leg using a precomposition equality. -/
theorem colimit_leg_delta_eq_of_precomp_eq
    {A B T : CochainComplex MetrizableLCA.{0} ℤ}
    (ι : A ⟶ B) (z : HomComplex.Cochain B T (-1))
    (zObj : HomComplex.Cochain A T (-1))
    (h : (HomComplex.Cochain.ofHom ι).comp z (zero_add (-1)) = zObj) :
    (HomComplex.Cochain.ofHom ι).comp
        (HomComplex.δ (-1) 0 z) (zero_add 0) =
      HomComplex.δ (-1) 0 zObj := by
  rw [← h, delta_of_colimit_leg_comp]

/-- `φ ≫ β` is the descent of the objectwise right side. -/
theorem phi_comp_rightMediator_eq_desc_objectwise {J : Type} [Category J]
    {X₁ X₂ : J ⥤ CochainComplex MetrizableLCA.{0} ℤ}
    {c₁ : Cocone X₁} (hc₁ : IsColimit c₁)
    {c₂ : Cocone X₂}
    (f : X₁ ⟶ X₂)
    (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j : J, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j)
    {T : CochainComplex MetrizableLCA.{0} ℤ}
    (β : c₂.pt ⟶ T)
    (leg : ∀ j : J, mappingCone (f.app j) ⟶ T)
    (hleg : MappingConeTestLegNaturality f leg)
    (hβ : ∀ j : J, c₂.ι.app j ≫ β = mappingCone.inr (f.app j) ≫ leg j) :
    φ ≫ β = hc₁.desc (rightSideObjectwiseCocone f leg hleg) := by
  apply hc₁.hom_ext
  intro j
  calc
    c₁.ι.app j ≫ (φ ≫ β) =
        (c₁.ι.app j ≫ φ) ≫ β := by simp [Category.assoc]
    _ = (f.app j ≫ c₂.ι.app j) ≫ β := by
        exact congrArg (fun g => g ≫ β) (hφ j)
    _ = f.app j ≫ (c₂.ι.app j ≫ β) := by simp [Category.assoc]
    _ = f.app j ≫ (mappingCone.inr (f.app j) ≫ leg j) := by rw [hβ j]
    _ = c₁.ι.app j ≫ hc₁.desc (rightSideObjectwiseCocone f leg hleg) := by
        exact (hc₁.fac (rightSideObjectwiseCocone f leg hleg) j).symm

/-- Extensionality for cochains out of a colimit complex, checked after legs. -/
theorem cochain_ext_of_colimit_legs_w338 {J : Type} [Category J]
    {X : J ⥤ CochainComplex MetrizableLCA.{0} ℤ}
    {cX : Cocone X} (hcX : IsColimit cX)
    [∀ p : ℤ, PreservesColimit X
      (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p)]
    {T : CochainComplex MetrizableLCA.{0} ℤ} {n : ℤ}
    {z₁ z₂ : HomComplex.Cochain cX.pt T n}
    (hlegs : ∀ j : J,
      (HomComplex.Cochain.ofHom (cX.ι.app j)).comp z₁ (zero_add n) =
        (HomComplex.Cochain.ofHom (cX.ι.app j)).comp z₂ (zero_add n)) :
    z₁ = z₂ := by
  apply HomComplex.Cochain.ext
  intro p q hpq
  apply (isColimitOfPreserves
    (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p) hcX).hom_ext
  intro j
  have h := HomComplex.Cochain.congr_v (hlegs j) p q hpq
  simpa [HomComplex.Cochain.ofHom_comp] using h

/-- The global W308-style descEq for the assembled left cochain. -/
theorem global_descEq_of_mappingConeLegs {J : Type} [Category J]
    {X₁ X₂ : J ⥤ CochainComplex MetrizableLCA.{0} ℤ}
    {c₁ : Cocone X₁} (hc₁ : IsColimit c₁)
    [∀ p : ℤ, PreservesColimit X₁
      (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p)]
    {c₂ : Cocone X₂}
    (f : X₁ ⟶ X₂)
    (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j : J, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j)
    {T : CochainComplex MetrizableLCA.{0} ℤ}
    (β : c₂.pt ⟶ T)
    (leg : ∀ j : J, mappingCone (f.app j) ⟶ T)
    (hleg : MappingConeTestLegNaturality f leg)
    (hβ : ∀ j : J, c₂.ι.app j ≫ β = mappingCone.inr (f.app j) ≫ leg j) :
    HomComplex.δ (-1) 0 (leftCochainOfMappingConeLegs hc₁ f leg hleg) =
      HomComplex.Cochain.ofHom (φ ≫ β) := by
  apply cochain_ext_of_colimit_legs_w338 hc₁
  intro j
  have hleft := colimit_leg_delta_eq_of_precomp_eq
    (c₁.ι.app j)
    (leftCochainOfMappingConeLegs hc₁ f leg hleg)
    (objectwiseLeftFromLeg (f.app j) (leg j))
    (leftCochainOfMappingConeLegs_comp_fac hc₁ f leg hleg j)
  have hobj := objectwiseLeftFromLeg_descEq (f.app j) (leg j)
  calc
    (HomComplex.Cochain.ofHom (c₁.ι.app j)).comp
        (HomComplex.δ (-1) 0 (leftCochainOfMappingConeLegs hc₁ f leg hleg)) (zero_add 0) =
        HomComplex.δ (-1) 0 (objectwiseLeftFromLeg (f.app j) (leg j)) := hleft
    _ = HomComplex.Cochain.ofHom (f.app j ≫ mappingCone.inr (f.app j) ≫ leg j) := hobj
    _ = (HomComplex.Cochain.ofHom (c₁.ι.app j)).comp
        (HomComplex.Cochain.ofHom (φ ≫ β)) (zero_add 0) := by
        have hmorph :
            f.app j ≫ mappingCone.inr (f.app j) ≫ leg j =
              c₁.ι.app j ≫ (φ ≫ β) := by
          symm
          calc
            c₁.ι.app j ≫ (φ ≫ β) =
                (c₁.ι.app j ≫ φ) ≫ β := by simp [Category.assoc]
            _ = (f.app j ≫ c₂.ι.app j) ≫ β := by
                rw [hφ j]
                rfl
            _ = f.app j ≫ (c₂.ι.app j ≫ β) := by simp [Category.assoc]
            _ = f.app j ≫ (mappingCone.inr (f.app j) ≫ leg j) := by
                rw [hβ j]
            _ = f.app j ≫ mappingCone.inr (f.app j) ≫ leg j := by simp
        rw [hmorph]
        simp [HomComplex.Cochain.ofHom_comp]

/-- Machine-readable W338 state. -/
structure WppOpMappingConeGlobalDescEqState : Type where
  checkedLemma : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W338 state. -/
def currentWppOpMappingConeGlobalDescEqState :
    WppOpMappingConeGlobalDescEqState where
  checkedLemma := "global_descEq_of_mappingConeLegs"
  remainingInputs :=
    ["instantiate this theorem with W308's included bounded c₁/c₂ cocones",
      "package it into W308's AmbientFixedMappingConeCoconeDescAssemblyData",
      "prove or package the remaining uniqueness/fac assembly fields using W327-W330"]
  productSuccessClaimed := false

theorem currentWppOpMappingConeGlobalDescEqState_productSuccess :
    currentWppOpMappingConeGlobalDescEqState.productSuccessClaimed = false := rfl

section Checks

#check global_descEq_of_mappingConeLegs
#check currentWppOpMappingConeGlobalDescEqState
#check currentWppOpMappingConeGlobalDescEqState_productSuccess

end Checks

end WppOpMappingConeGlobalDescEqW338

end LeanLCAExactChallenge
