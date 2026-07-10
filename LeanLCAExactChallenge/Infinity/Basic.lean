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

/-- A map of quasicategories is a bicategorical equivalence when it is the forward map of an
adjoint equivalence in mathlib's strict bicategory of quasicategories. -/
def IsBicategoricalEquivalence {X Y : SSet.QCat.{u}} (f : X ⟶ Y) : Prop :=
  ∃ e : Bicategory.Equivalence X Y, e.hom = f

/-- Identity maps of quasicategories are bicategorical equivalences. -/
theorem isBicategoricalEquivalence_id (X : SSet.QCat.{u}) :
    IsBicategoricalEquivalence (𝟙 X) :=
  ⟨Bicategory.Equivalence.id X, rfl⟩

end Infinity
end LeanLCAExactChallenge
