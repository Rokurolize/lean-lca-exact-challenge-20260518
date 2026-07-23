/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.QuotientAlexanderWhitneyCoassociativityTripleSummands

/-! # Projected Alexander--Whitney coassociativity -/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
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

variable (X Y Z : SimplicialObject (QuotientModule))

theorem aw_left_iterated_projection (p q r : ℕ) :
    (alternatingAlexanderWhitney (X ⊗ Y) Z).f (p + q + r) ≫
        (HomologicalComplex.tensorHom (alternatingAlexanderWhitney X Y)
          (𝟙 (alternatingChains Z))).f (p + q + r) ≫
        complexLeftTripleProjection (alternatingChains X) (alternatingChains Y)
          (alternatingChains Z) p q r (p + q + r) rfl =
      (X.map
            (SimplexCategory.subinterval
              (n := p + q + r) 0 p (by omega)).op ⊗ₘ
        Y.map
          (SimplexCategory.subinterval
            (n := p + q + r) p q (by omega)).op) ⊗ₘ
        Z.map
          (SimplexCategory.subinterval
            (n := p + q + r) (p + q) r (by omega)).op := by
  have hproj := tensorHom_comp_complexTensorPairProjection
    (alternatingAlexanderWhitney X Y) (𝟙 (alternatingChains Z))
    (p + q) r (p + q + r) (by omega)
  have hcomp := congrArg
    (fun t ↦
      (alternatingAlexanderWhitney (X ⊗ Y) Z).f (p + q + r) ≫ t ≫
        (complexTensorPairProjection (alternatingChains X) (alternatingChains Y)
            p q (p + q) rfl ⊗ₘ 𝟙 ((alternatingChains Z).X r))) hproj
  calc
    _ = (alternatingAlexanderWhitney (X ⊗ Y) Z).f (p + q + r) ≫
        complexTensorPairProjection (alternatingChains (X ⊗ Y))
          (alternatingChains Z) (p + q) r (p + q + r) (by omega) ≫
        ((((alternatingAlexanderWhitney X Y).f (p + q)) ⊗ₘ
            ((𝟙 (alternatingChains Z) :
              alternatingChains Z ⟶ alternatingChains Z).f r)) ≫
          (complexTensorPairProjection (alternatingChains X) (alternatingChains Y)
              p q (p + q) rfl ⊗ₘ 𝟙 ((alternatingChains Z).X r))) := by
      simpa only [complexLeftTripleProjection, Category.assoc] using hcomp
    _ = _ := by
      simp only [HomologicalComplex.id_f,
        MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]
      rw [← Category.assoc,
        alternatingAlexanderWhitney_comp_complexTensorPairProjection]
      rw [alternatingAlexanderWhitney_comp_complexTensorPairProjection]
      simp only [Monoidal.tensorObj_map]
      erw [MonoidalCategory.tensorHom_comp_tensorHom]
      erw [MonoidalCategory.tensorHom_comp_tensorHom]
      erw [Category.comp_id]
      rw [← X.map_comp, ← Y.map_comp]
      simp only [← op_comp]
      rw [aw_front_front, aw_middle_left]

theorem complexAssociator_comp_rightTripleProjection
    (K L M : ChainComplex (QuotientModule) ℕ)
    (p q r n : ℕ) (h : p + q + r = n) :
    ((α_ K L M).hom.f n) ≫ complexRightTripleProjection K L M p q r n h =
      complexLeftTripleProjection K L M p q r n h ≫
        (α_ (K.X p) (L.X q) (M.X r)).hom := by
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro i j k hijk
  have hassoc :
      (α_ K L M).hom.f n =
        (HomologicalComplex.mapBifunctorAssociatorX
          (MonoidalCategory.curriedAssociatorNatIso (QuotientModule)) K L M
          (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ) n).hom := rfl
  rw [hassoc, HomologicalComplex.ι_mapBifunctorAssociatorX_hom_assoc]
  change i + j + k = n at hijk
  by_cases ht : (i, j, k) = (p, q, r)
  · have hi : i = p := congrArg (fun t ↦ t.1) ht
    have hj : j = q := congrArg (fun t ↦ t.2.1) ht
    have hk : k = r := congrArg (fun t ↦ t.2.2) ht
    subst i
    subst j
    subst k
    have hr := complexRightTripleIncl_proj_self K L M p q r n hijk
    have hl := complexLeftTripleIncl_proj_self K L M p q r n hijk
    change _ ≫ complexRightTripleProjection K L M p q r n h = 𝟙 _ at hr
    change _ ≫ complexLeftTripleProjection K L M p q r n h = 𝟙 _ at hl
    slice_lhs 2 3 => erw [hr]
    slice_rhs 1 2 => erw [hl]
    rfl
  · have hr :=
      complexRightTripleIncl_proj_ne K L M i j k p q r n hijk h ht
    have hl :=
      complexLeftTripleIncl_proj_ne K L M i j k p q r n hijk h ht
    change _ ≫ complexRightTripleProjection K L M p q r n h = 0 at hr
    change _ ≫ complexLeftTripleProjection K L M p q r n h = 0 at hl
    slice_lhs 2 3 => erw [hr]
    slice_rhs 1 2 => erw [hl]
    rfl

theorem alternatingAlexanderWhitney_coassociativity_projected
    (p q r : ℕ) :
    (((alternatingAlexanderWhitney (X ⊗ Y) Z).f (p + q + r) ≫
          (HomologicalComplex.tensorHom (alternatingAlexanderWhitney X Y)
            (𝟙 (alternatingChains Z))).f (p + q + r)) ≫
        ((α_ (alternatingChains X) (alternatingChains Y)
          (alternatingChains Z)).hom.f (p + q + r))) ≫
        complexRightTripleProjection (alternatingChains X) (alternatingChains Y)
          (alternatingChains Z) p q r (p + q + r) rfl =
      ((((alternatingFaceMapComplex (QuotientModule)).map
            ((α_ X Y Z).hom)).f (p + q + r) ≫
          (alternatingAlexanderWhitney X (Y ⊗ Z)).f (p + q + r)) ≫
        (HomologicalComplex.tensorHom (𝟙 (alternatingChains X))
          (alternatingAlexanderWhitney Y Z)).f (p + q + r)) ≫
        complexRightTripleProjection (alternatingChains X) (alternatingChains Y)
          (alternatingChains Z) p q r (p + q + r) rfl := by
  calc
    _ = (((alternatingAlexanderWhitney (X ⊗ Y) Z).f (p + q + r) ≫
          (HomologicalComplex.tensorHom (alternatingAlexanderWhitney X Y)
            (𝟙 (alternatingChains Z))).f (p + q + r)) ≫
          complexLeftTripleProjection (alternatingChains X) (alternatingChains Y)
            (alternatingChains Z) p q r (p + q + r) rfl) ≫
        (α_ ((alternatingChains X).X p) ((alternatingChains Y).X q)
          ((alternatingChains Z).X r)).hom := by
      simp only [Category.assoc]
      rw [complexAssociator_comp_rightTripleProjection]
    _ = ((X.map
              (SimplexCategory.subinterval
                (n := p + q + r) 0 p (by omega)).op ⊗ₘ
            Y.map
              (SimplexCategory.subinterval
                (n := p + q + r) p q (by omega)).op) ⊗ₘ
          Z.map
            (SimplexCategory.subinterval
              (n := p + q + r) (p + q) r (by omega)).op) ≫
        (α_ ((alternatingChains X).X p) ((alternatingChains Y).X q)
          ((alternatingChains Z).X r)).hom := by
      have hleft := congrArg
        (fun t ↦ t ≫
          (α_ ((alternatingChains X).X p) ((alternatingChains Y).X q)
            ((alternatingChains Z).X r)).hom)
        (aw_left_iterated_projection X Y Z p q r)
      simpa only [Category.assoc] using hleft
    _ = _ := by
      erw [MonoidalCategory.associator_naturality]
      have hright := congrArg
        (fun t =>
          (α_ ((alternatingChains X).X (p + q + r))
              ((alternatingChains Y).X (p + q + r))
              ((alternatingChains Z).X (p + q + r))).hom ≫ t)
        (aw_right_iterated_projection X Y Z p q r).symm
      simpa only [Category.assoc, alternatingFaceMapComplex_map_f,
        alternatingFaceMapComplex_obj_X, Monoidal.associator_hom_app] using hright


end QuotientDoldKanMonoidal
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
