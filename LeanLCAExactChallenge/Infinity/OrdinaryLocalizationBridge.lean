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
open CategoryTheory.MonoidalCategory

universe u

universe v w

/-- In a Cat-enriched ordinary category, the transported horizontal composite has the
expected enriched-composition normal form after applying `Hom.base`. -/
theorem catEnrichedOrdinary_base_hComp
    {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory Cat.{w, u} C]
    {a b c : CategoryTheory.CatEnrichedOrdinary C}
    {f f' : a ⟶ b} {g g' : b ⟶ c} (eta : f ⟶ f') (theta : g ⟶ g') :
    CategoryTheory.CatEnrichedOrdinary.Hom.base
        (CategoryTheory.CatEnrichedOrdinary.hComp eta theta) =
      eqToHom (CategoryTheory.CatEnrichedOrdinary.homEquiv_comp f g) ≫
        CategoryTheory.CatEnriched.hComp
          (CategoryTheory.CatEnrichedOrdinary.Hom.base eta)
          (CategoryTheory.CatEnrichedOrdinary.Hom.base theta) ≫
        eqToHom (CategoryTheory.CatEnrichedOrdinary.homEquiv_comp f' g').symm := by
  rfl

/-- Horizontal composition in the underlying Cat-enriched category is literally the map of
the enriched composition functor. -/
theorem catEnriched_hComp_eq_eComp_map
    {C : Type u} [Category.{v} C] [EnrichedCategory Cat.{w, u} C]
    {a b c : CategoryTheory.CatEnriched C}
    {f f' : a ⟶ b} {g g' : b ⟶ c} (eta : f ⟶ f') (theta : g ⟶ g') :
    CategoryTheory.CatEnriched.hComp eta theta =
      (eComp Cat a b c).toFunctor.map (eta, theta) := by
  rfl

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

local instance qcatHomCategory (X Y : SSet.QCat.{u}) : Category (X ⟶ Y) :=
  SSet.QCat.bicategory.homCategory X Y

/-- The category of strict-bicategory `1`-morphisms is obtained from the enriched
hom-category by transport along the ordinary/enriched Hom equivalence. -/
def qcatHomToEnrichedHom (X Y : SSet.QCat.{u}) :
    (X ⟶ Y) ⥤
      ((CategoryTheory.CatEnrichedOrdinary.toBase X) ⟶
        (CategoryTheory.CatEnrichedOrdinary.toBase Y)) where
  obj := CategoryTheory.CatEnrichedOrdinary.homEquiv
  map := CategoryTheory.CatEnrichedOrdinary.Hom.base

instance qcatHomToEnrichedHom_faithful (X Y : SSet.QCat.{u}) :
    (qcatHomToEnrichedHom X Y).Faithful where
  map_injective h := CategoryTheory.CatEnrichedOrdinary.Hom.ext _ _ h

instance qcatHomToEnrichedHom_full (X Y : SSet.QCat.{u}) :
    (qcatHomToEnrichedHom X Y).Full where
  map_surjective f := ⟨CategoryTheory.CatEnrichedOrdinary.Hom.mk f, rfl⟩

instance qcatHomToEnrichedHom_essSurj (X Y : SSet.QCat.{u}) :
    (qcatHomToEnrichedHom X Y).EssSurj where
  mem_essImage Z := by
    refine ⟨CategoryTheory.CatEnrichedOrdinary.homEquiv.symm Z, ?_⟩
    exact ⟨eqToIso (Equiv.apply_symm_apply
      CategoryTheory.CatEnrichedOrdinary.homEquiv Z)⟩

instance qcatHomToEnrichedHom_isEquivalence (X Y : SSet.QCat.{u}) :
    (qcatHomToEnrichedHom X Y).IsEquivalence where

private instance qcatTensorUnit_quasicategory :
    SSet.Quasicategory (𝟙_ SSet.{u}) := by
  apply SSet.quasicategory_of_hasLiftingProperty _
    (SemiCartesianMonoidalCategory.isTerminalTensorUnit (C := SSet.{u}))
  intro n i h₀ hₙ
  have heq : (SemiCartesianMonoidalCategory.isTerminalTensorUnit
      (C := SSet.{u})).from (𝟙_ SSet) = 𝟙 (𝟙_ SSet) :=
    (SemiCartesianMonoidalCategory.isTerminalTensorUnit (C := SSet.{u})).hom_ext _ _
  rw [heq]
  infer_instance

private def qcatTensorUnit : SSet.QCat.{u} :=
  ⟨𝟙_ SSet, qcatTensorUnit_quasicategory⟩

/-- The strict-bicategory Hom from the tensor unit is explicitly equivalent to the
homotopy category of a quasicategory. -/
noncomputable def qcatUnitHomEquivalence (X : SSet.QCat.{u}) :
    (qcatTensorUnit ⟶ X) ≌ SSet.hoFunctor.obj X.obj :=
  (qcatHomToEnrichedHom qcatTensorUnit X).asEquivalence |>.trans
    (Cat.equivOfIso (SSet.hoFunctor.mapIso
      (MonoidalClosed.unitIsoSelf (C := SSet.{u}) (X := X.obj))))

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
