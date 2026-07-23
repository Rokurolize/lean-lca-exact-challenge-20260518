/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.QuotientAlexanderWhitneyNaturality

/-! # Normalized Alexander--Whitney construction -/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord
namespace QuotientDoldKanMonoidal

open AlgebraicTopology
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Opposite

variable (X Y : SimplicialObject (QuotientModule))

/-- The degreewise normalized Alexander--Whitney candidate. It includes normalized chains
into alternating chains, applies the Alexander--Whitney formula, and then applies the two
normalized Moore projectors. -/
def normalizedAlexanderWhitneyDegree (n : ℕ) :
    ((normalizedMooreComplex (QuotientModule)).obj (X ⊗ Y)).X n ⟶
      (HomologicalComplex.tensorObj
        ((normalizedMooreComplex (QuotientModule)).obj X)
        ((normalizedMooreComplex (QuotientModule)).obj Y)).X n :=
  (inclusionOfMooreComplexMap (X ⊗ Y)).f n ≫
    alternatingAlexanderWhitneyDegree X Y n ≫
    (HomologicalComplex.tensorHom
      (DoldKan.PInftyToNormalizedMooreComplex X)
      (DoldKan.PInftyToNormalizedMooreComplex Y)).f n

/-- The normalized Alexander--Whitney chain map. -/
def normalizedAlexanderWhitney :
    (normalizedMooreComplex (QuotientModule)).obj (X ⊗ Y) ⟶
      HomologicalComplex.tensorObj
        ((normalizedMooreComplex (QuotientModule)).obj X)
        ((normalizedMooreComplex (QuotientModule)).obj Y) :=
  inclusionOfMooreComplexMap (X ⊗ Y) ≫
    alternatingAlexanderWhitney X Y ≫
    HomologicalComplex.tensorHom
      (DoldKan.PInftyToNormalizedMooreComplex X)
      (DoldKan.PInftyToNormalizedMooreComplex Y)

@[simp]
theorem normalizedAlexanderWhitney_f (n : ℕ) :
    (normalizedAlexanderWhitney X Y).f n =
      normalizedAlexanderWhitneyDegree X Y n := rfl

/-- The normalized Alexander--Whitney chain map is natural in both variables. -/
theorem normalizedAlexanderWhitney_natural
    {X' Y' : SimplicialObject (QuotientModule)}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    normalizedAlexanderWhitney X Y ≫
        HomologicalComplex.tensorHom
          ((normalizedMooreComplex (QuotientModule)).map f)
          ((normalizedMooreComplex (QuotientModule)).map g) =
      (normalizedMooreComplex (QuotientModule)).map (f ⊗ₘ g) ≫
        normalizedAlexanderWhitney X' Y' := by
  simp only [normalizedAlexanderWhitney, Category.assoc]
  have htensor :
      HomologicalComplex.tensorHom
            (DoldKan.PInftyToNormalizedMooreComplex X)
            (DoldKan.PInftyToNormalizedMooreComplex Y) ≫
          HomologicalComplex.tensorHom
            ((normalizedMooreComplex (QuotientModule)).map f)
            ((normalizedMooreComplex (QuotientModule)).map g) =
        HomologicalComplex.tensorHom
          (DoldKan.PInftyToNormalizedMooreComplex X ≫
            (normalizedMooreComplex (QuotientModule)).map f)
          (DoldKan.PInftyToNormalizedMooreComplex Y ≫
            (normalizedMooreComplex (QuotientModule)).map g) := by
    exact MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _
  erw [htensor]
  erw [← DoldKan.PInftyToNormalizedMooreComplex_naturality f,
    ← DoldKan.PInftyToNormalizedMooreComplex_naturality g]
  have htensor' :
      HomologicalComplex.tensorHom
          ((alternatingFaceMapComplex (QuotientModule)).map f ≫
            DoldKan.PInftyToNormalizedMooreComplex X')
          ((alternatingFaceMapComplex (QuotientModule)).map g ≫
            DoldKan.PInftyToNormalizedMooreComplex Y') =
        HomologicalComplex.tensorHom
            ((alternatingFaceMapComplex (QuotientModule)).map f)
            ((alternatingFaceMapComplex (QuotientModule)).map g) ≫
          HomologicalComplex.tensorHom
            (DoldKan.PInftyToNormalizedMooreComplex X')
            (DoldKan.PInftyToNormalizedMooreComplex Y') := by
    exact (MonoidalCategory.tensorHom_comp_tensorHom
      ((alternatingFaceMapComplex (QuotientModule)).map f)
      ((alternatingFaceMapComplex (QuotientModule)).map g)
      (DoldKan.PInftyToNormalizedMooreComplex X')
      (DoldKan.PInftyToNormalizedMooreComplex Y')).symm
  erw [htensor']
  erw [← Category.assoc
    (alternatingAlexanderWhitney X Y)
    (HomologicalComplex.tensorHom
      ((alternatingFaceMapComplex (QuotientModule)).map f)
      ((alternatingFaceMapComplex (QuotientModule)).map g))
    (HomologicalComplex.tensorHom
      (DoldKan.PInftyToNormalizedMooreComplex X')
      (DoldKan.PInftyToNormalizedMooreComplex Y'))]
  rw [alternatingAlexanderWhitney_natural X Y f g]
  have hinc := congrArg
    (fun t => t ≫ alternatingAlexanderWhitney X' Y' ≫
      HomologicalComplex.tensorHom
        (DoldKan.PInftyToNormalizedMooreComplex X')
        (DoldKan.PInftyToNormalizedMooreComplex Y'))
    ((inclusionOfMooreComplex (QuotientModule)).naturality (f ⊗ₘ g)).symm
  exact (Category.assoc _ _ _).symm.trans (hinc.trans (Category.assoc _ _ _))

/-- The normalized Alexander--Whitney counit on the monoidal unit. -/
def normalizedAlexanderWhitneyUnit :
    (normalizedMooreComplex (QuotientModule)).obj
        (𝟙_ (SimplicialObject (QuotientModule))) ⟶
      𝟙_ (ChainComplex (QuotientModule) ℕ) := by
  change
    (normalizedMooreComplex (QuotientModule)).obj
        (𝟙_ (SimplicialObject (QuotientModule))) ⟶
      (ChainComplex.single₀ (QuotientModule)).obj (𝟙_ (QuotientModule))
  refine (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨(NormalizedMooreComplex.objX
      (𝟙_ (SimplicialObject (QuotientModule))) 0).arrow, ?_⟩
  rw [normalizedMooreComplex_objD]
  simp only [NormalizedMooreComplex.objD, Nat.reduceAdd,
    Monoidal.tensorUnit_obj, NormalizedMooreComplex.objX_add_one,
    NormalizedMooreComplex.objX_zero, Fin.isValue]
  have hf := CategoryTheory.Subobject.finset_inf_arrow_factors Finset.univ
    (fun _ : Fin 1 => Limits.kernelSubobject (𝟙 (𝟙_ (QuotientModule))))
    (0 : Fin 1) (by simp)
  have hz := (Limits.kernelSubobject_factors_iff
    (𝟙 (𝟙_ (QuotientModule))) _).mp hf
  rw [Category.comp_id] at hz
  exact (congrArg (fun t => (t ≫ inv (⊤ : Subobject (𝟙_ (QuotientModule))).arrow) ≫
    (⊤ : Subobject (𝟙_ (QuotientModule))).arrow) hz).trans (by simp only [zero_comp]; rfl)

@[simp]
theorem normalizedAlexanderWhitneyUnit_f_zero :
    normalizedAlexanderWhitneyUnit.f 0 =
      (NormalizedMooreComplex.objX
        (𝟙_ (SimplicialObject (QuotientModule))) 0).arrow := by
  apply ChainComplex.toSingle₀Equiv_symm_apply_f_zero

@[simp]
theorem normalizedAlexanderWhitneyUnit_f_succ (n : ℕ) :
    normalizedAlexanderWhitneyUnit.f (n + 1) = 0 := by
  apply (HomologicalComplex.isZero_single_obj_X
    (c := ComplexShape.down ℕ) 0 (𝟙_ (QuotientModule)) (n + 1) (by omega)).eq_of_tgt

/-- The normalized unit map expressed through the standard alternating-chain augmentation. -/
def normalizedAlexanderWhitneyUnitViaEpsilon :
    (normalizedMooreComplex (QuotientModule)).obj
        (𝟙_ (SimplicialObject (QuotientModule))) ⟶
      𝟙_ (ChainComplex (QuotientModule) ℕ) :=
  inclusionOfMooreComplexMap
      (𝟙_ (SimplicialObject (QuotientModule))) ≫
    AlternatingFaceMapComplex.ε.app
      (SimplicialObject.Augmented.const.obj (𝟙_ (QuotientModule)))

theorem normalizedAlexanderWhitneyUnitViaEpsilon_eq :
    normalizedAlexanderWhitneyUnitViaEpsilon =
      normalizedAlexanderWhitneyUnit := by
  apply HomologicalComplex.to_single_hom_ext
  simp [normalizedAlexanderWhitneyUnitViaEpsilon]
  rfl

/-- Retracting alternating chains and then applying the normalized unit map is the standard
alternating-chain augmentation. -/
theorem pInfty_comp_normalizedAlexanderWhitneyUnit :
    DoldKan.PInftyToNormalizedMooreComplex
          (𝟙_ (SimplicialObject (QuotientModule))) ≫
        normalizedAlexanderWhitneyUnit =
      AlternatingFaceMapComplex.ε.app
        (SimplicialObject.Augmented.const.obj (𝟙_ (QuotientModule))) := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [AlternatingFaceMapComplex.obj_X, Monoidal.tensorUnit_obj,
    ChainComplex.single₀_obj_zero, HomologicalComplex.comp_f,
    DoldKan.PInftyToNormalizedMooreComplex_f,
    NormalizedMooreComplex.objX_zero, DoldKan.PInfty_f_0,
    normalizedAlexanderWhitneyUnit_f_zero,
    AlternatingFaceMapComplex.ε_app_f_zero, Functor.id_obj,
    SimplicialObject.Augmented.const_obj_hom, NatTrans.id_app]
  exact Subobject.factorThru_arrow _ _ _

/-- Naturality of normalized Alexander--Whitney in its left variable. -/
theorem normalizedAlexanderWhitney_natural_left
    {X Y : SimplicialObject (QuotientModule)} (f : X ⟶ Y)
    (X' : SimplicialObject (QuotientModule)) :
    normalizedAlexanderWhitney X X' ≫
        (quotientModuleDoldKanEquivalence.functor.map f ▷
          quotientModuleDoldKanEquivalence.functor.obj X') =
      quotientModuleDoldKanEquivalence.functor.map (f ▷ X') ≫
        normalizedAlexanderWhitney Y X' := by
  have h := normalizedAlexanderWhitney_natural X X' f (CategoryStruct.id X')
  rw [CategoryTheory.Functor.map_id] at h
  exact h

/-- Naturality of normalized Alexander--Whitney in its right variable. -/
theorem normalizedAlexanderWhitney_natural_right
    {X Y : SimplicialObject (QuotientModule)}
    (X' : SimplicialObject (QuotientModule)) (f : X ⟶ Y) :
    normalizedAlexanderWhitney X' X ≫
        (quotientModuleDoldKanEquivalence.functor.obj X' ◁
          quotientModuleDoldKanEquivalence.functor.map f) =
      quotientModuleDoldKanEquivalence.functor.map (X' ◁ f) ≫
        normalizedAlexanderWhitney X' Y := by
  have h := normalizedAlexanderWhitney_natural X' X (CategoryStruct.id X') f
  rw [CategoryTheory.Functor.map_id] at h
  exact h

/-- Package normalized Alexander--Whitney once its associativity and two unit laws are proved. -/
@[implicit_reducible]
def normalizedMooreOplaxMonoidalCandidate
    (hassoc : ∀ X Y Z : SimplicialObject (QuotientModule),
      normalizedAlexanderWhitney (X ⊗ Y) Z ≫
          (normalizedAlexanderWhitney X Y ▷
            quotientModuleDoldKanEquivalence.functor.obj Z) ≫
          (α_
            (quotientModuleDoldKanEquivalence.functor.obj X)
            (quotientModuleDoldKanEquivalence.functor.obj Y)
            (quotientModuleDoldKanEquivalence.functor.obj Z)).hom =
        quotientModuleDoldKanEquivalence.functor.map (α_ X Y Z).hom ≫
          normalizedAlexanderWhitney X (Y ⊗ Z) ≫
          (quotientModuleDoldKanEquivalence.functor.obj X ◁
            normalizedAlexanderWhitney Y Z))
    (hleft : ∀ X : SimplicialObject (QuotientModule),
      (λ_ (quotientModuleDoldKanEquivalence.functor.obj X)).inv =
        quotientModuleDoldKanEquivalence.functor.map (λ_ X).inv ≫
          normalizedAlexanderWhitney
            (𝟙_ (SimplicialObject (QuotientModule))) X ≫
          (normalizedAlexanderWhitneyUnit ▷
            quotientModuleDoldKanEquivalence.functor.obj X))
    (hright : ∀ X : SimplicialObject (QuotientModule),
      (ρ_ (quotientModuleDoldKanEquivalence.functor.obj X)).inv =
        quotientModuleDoldKanEquivalence.functor.map (ρ_ X).inv ≫
          normalizedAlexanderWhitney X
            (𝟙_ (SimplicialObject (QuotientModule))) ≫
          (quotientModuleDoldKanEquivalence.functor.obj X ◁
            normalizedAlexanderWhitneyUnit)) :
    NormalizedMooreOplaxMonoidal where
  η := normalizedAlexanderWhitneyUnit
  δ := normalizedAlexanderWhitney
  δ_natural_left := normalizedAlexanderWhitney_natural_left
  δ_natural_right := normalizedAlexanderWhitney_natural_right
  oplax_associativity := hassoc
  oplax_left_unitality := hleft
  oplax_right_unitality := hright


end QuotientDoldKanMonoidal
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
