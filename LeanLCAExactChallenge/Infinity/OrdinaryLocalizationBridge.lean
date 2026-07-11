import LeanLCAExactChallenge.Infinity.EquivalenceIntervalExtension
import LeanLCAExactChallenge.Infinity.MetrizableEquivalenceForcingHomotopy
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction

/-!
# Ordinary localization bridge

This module is reserved for the comparison between the mapping-quasicategory localization
property and its ordinary homotopy-category truncation.  The comparison is not asserted here:
it requires a verified compatibility theorem between the two homotopy-category presentations.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity

open CategoryTheory

universe u

open scoped Bicategory

/-- Postcomposition with the forward map of a bicategorical adjoint equivalence is an
equivalence of ordinary hom-categories. -/
theorem bicategoricalEquivalence_postcomp_isEquivalence
    {X Y : SSet.QCat.{u}} (e : Bicategory.Equivalence X Y) (A : SSet.QCat.{u}) :
    (Bicategory.postcomp A e.hom).IsEquivalence := by
  let G := Bicategory.postcomp A e.inv
  let η :=
    (Bicategory.rightUnitorNatIso A X).symm ≪≫
      (Bicategory.postcomposing A X X).mapIso e.unit ≪≫
        (Bicategory.associatorNatIsoLeft A e.hom e.inv).symm
  let ε :=
    Bicategory.associatorNatIsoLeft A e.inv e.hom ≪≫
      (Bicategory.postcomposing A Y Y).mapIso e.counit ≪≫
        Bicategory.rightUnitorNatIso A Y
  exact Functor.IsEquivalence.mk' G η ε

/-- Maps between nerves are exactly ordinary functors.  This is the fully-faithful
starting point for comparing the mapping localization with its ordinary truncation. -/
noncomputable def nerveFunctorCategoryEquiv (C D : Type u)
    [Category.{u} C] [Category.{u} D] :
    (C ⥤ D) ≃
      (nerveFunctor.obj (Cat.of C) ⟶ nerveFunctor.obj (Cat.of D)) :=
  (Functor.equivCatHom C D).trans nerveFunctor.fullyfaithful.homEquiv

@[simp]
theorem nerveFunctorCategoryEquiv_apply (C D : Type u)
    [Category.{u} C] [Category.{u} D] (F : C ⥤ D) :
    nerveFunctorCategoryEquiv C D F =
      nerveFunctor.map F.toCatHom :=
  rfl

end Infinity
end LeanLCAExactChallenge
