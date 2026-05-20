import LeanLCAExactChallenge.Derived.MappingConeFiniteProduct

/-!
W333: assemble the W308 left cochain from mapping-cone test legs.

W331 constructs a left cochain from compatible objectwise cochains, and W332
shows that `mappingCone.inl` composed with natural test legs gives such a
compatible family.  This file combines the two ideas in one import-safe theorem.

Given a natural transformation `f : X₁ ⟶ X₂`, a colimit cocone `c₁` for `X₁`,
and a family of mapping-cone test legs natural with respect to `mappingCone.map`,
we construct the descended degree `-1` cochain out of `c₁.pt` and prove its
expected leg equation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WppOpMappingConeLeftCochainAssemblyW333

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

/-- Objectwise left cochain from a test leg. -/
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

/-- Machine-readable W333 state. -/
structure WppOpMappingConeLeftCochainAssemblyState : Type where
  checkedConstructor : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W333 state. -/
def currentWppOpMappingConeLeftCochainAssemblyState :
    WppOpMappingConeLeftCochainAssemblyState where
  checkedConstructor := "leftCochainOfMappingConeLegs"
  remainingInputs :=
    ["instantiate the theorem with W308's included bounded c₁ cocone",
      "supply evaluation-colimit preservation for that included c₁ diagram",
      "prove mappingCone.desc differential compatibility for the assembled left/right data"]
  productSuccessClaimed := false

theorem currentWppOpMappingConeLeftCochainAssemblyState_productSuccess :
    currentWppOpMappingConeLeftCochainAssemblyState.productSuccessClaimed = false := rfl

section Checks

#check MappingConeTestLegNaturality
#check objectwiseLeftFromLeg
#check objectwiseLeftFromLeg_compatible
#check assembledLeftEvalCocone
#check leftCochainOfMappingConeLegs
#check leftCochainOfMappingConeLegs_comp_fac
#check currentWppOpMappingConeLeftCochainAssemblyState
#check currentWppOpMappingConeLeftCochainAssemblyState_productSuccess

end Checks

end WppOpMappingConeLeftCochainAssemblyW333

end LeanLCAExactChallenge
