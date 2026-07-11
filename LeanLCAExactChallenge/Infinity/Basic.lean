import Mathlib.AlgebraicTopology.Quasicategory.StrictBicategory
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic

/-!
# Basic infinity-categorical semantics

This file records notions that are genuinely expressed in mathlib's strict bicategory of
quasicategories. In particular, equivalence here is adjoint equivalence in that bicategory,
not an isomorphism of ordinary homotopy categories.
-/

set_option autoImplicit false

universe u

namespace LeanLCAExactChallenge
namespace Infinity

open CategoryTheory
open scoped Bicategory

/-- A map of quasicategories is a bicategorical equivalence when it is the forward map of an
adjoint equivalence in mathlib's strict bicategory of quasicategories. -/
def IsBicategoricalEquivalence {X Y : SSet.QCat.{u}} (f : X ⟶ Y) : Prop :=
  ∃ e : Bicategory.Equivalence X Y, e.hom = f

/-- Identity maps of quasicategories are bicategorical equivalences. -/
theorem isBicategoricalEquivalence_id (X : SSet.QCat.{u}) :
    IsBicategoricalEquivalence (𝟙 X) :=
  ⟨Bicategory.Equivalence.id X, rfl⟩

/-- Adjoint equivalences compose in the strict bicategory of quasicategories. -/
noncomputable def bicategoricalEquivalenceComp
    {X Y Z : SSet.QCat.{u}}
    (e₁ : Bicategory.Equivalence X Y)
    (e₂ : Bicategory.Equivalence Y Z) :
    Bicategory.Equivalence X Z := by
  let unit : 𝟙 X ≅ (e₁.hom ≫ e₂.hom) ≫ e₂.inv ≫ e₁.inv :=
    e₁.unit ≪⊗≫
      Bicategory.whiskerLeftIso e₁.hom
        (Bicategory.whiskerRightIso e₂.unit e₁.inv) ≪⊗≫
          Iso.refl _
  let counit : (e₂.inv ≫ e₁.inv) ≫ e₁.hom ≫ e₂.hom ≅ 𝟙 Z :=
    Iso.refl _ ≪⊗≫
      Bicategory.whiskerLeftIso e₂.inv
        (Bicategory.whiskerRightIso e₁.counit e₂.hom) ≪⊗≫
          e₂.counit
  exact Bicategory.Equivalence.mkOfAdjointifyCounit unit counit

/-- Bicategorical equivalences are closed under composition. -/
theorem IsBicategoricalEquivalence.comp
    {X Y Z : SSet.QCat.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsBicategoricalEquivalence f)
    (hg : IsBicategoricalEquivalence g) :
    IsBicategoricalEquivalence (f ≫ g) := by
  obtain ⟨e₁, rfl⟩ := hf
  obtain ⟨e₂, rfl⟩ := hg
  exact ⟨bicategoricalEquivalenceComp e₁ e₂, rfl⟩

end Infinity
end LeanLCAExactChallenge
