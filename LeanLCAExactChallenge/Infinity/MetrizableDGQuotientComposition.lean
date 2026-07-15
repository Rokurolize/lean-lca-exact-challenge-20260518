/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientCompositionMerge
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-! # Active frontier for composition in the corrected Drinfeld quotient -/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory
open CategoryTheory.MonoidalCategory

section QuotientCoefficient

/-- A universe-1 copy of the integer coefficient ring for the large quotient carrier. -/
abbrev QuotientCoefficientRing := ULift.{1} ℤ

attribute [-instance] ULift.semiring

local instance quotientCoefficientCarrierModule (M : ModuleCat.{1} ℤ) :
    Module QuotientCoefficientRing (ULift.{0} M) := by
  infer_instance

attribute [-instance] ULift.module

/-- A large integer module regarded over the universe-matched coefficient ring. -/
abbrev quotientCoefficientModule (M : ModuleCat.{1} ℤ) :
    ModuleCat.{1} QuotientCoefficientRing :=
  ModuleCat.of QuotientCoefficientRing (ULift.{0} M)

/-- Transport an integer-linear map to the universe-matched coefficient modules. -/
def quotientLinearMapChangeScalars {M N : ModuleCat.{1} ℤ} (f : M →ₗ[ℤ] N) :
    quotientCoefficientModule M →ₗ[QuotientCoefficientRing]
      quotientCoefficientModule N where
  toFun x := ULift.up (f x.down)
  map_add' x y := by
    apply ULift.down_injective
    exact f.map_add x.down y.down
  map_smul' r x := by
    apply ULift.down_injective
    exact map_zsmul f r.down x.down

/-- Change large integer modules to the universe-matched coefficient category. -/
def quotientCoefficientChange : ModuleCat.{1} ℤ ⥤
    ModuleCat.{1} QuotientCoefficientRing where
  obj := quotientCoefficientModule
  map f := ModuleCat.ofHom (quotientLinearMapChangeScalars f.hom)
  map_id _ := by
    apply ModuleCat.hom_ext
    rfl
  map_comp _ _ := by
    apply ModuleCat.hom_ext
    rfl

instance quotientCoefficientChangePreservesZeroMorphisms :
    quotientCoefficientChange.PreservesZeroMorphisms where
  map_zero := by
    intro M N
    apply ModuleCat.hom_ext
    rfl

/-- The corrected quotient Hom cochain complex over universe-matched coefficients. -/
def quotientCoefficientCochainComplex (X Y : ComplexCategory) :
    CochainComplex (ModuleCat.{1} QuotientCoefficientRing) ℤ :=
  (quotientCoefficientChange.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (quotientDGMappingCochainComplex X Y)

@[simp]
theorem quotientCoefficientCochainComplex_X (X Y : ComplexCategory) (n : ℤ) :
    (quotientCoefficientCochainComplex X Y).X n =
      quotientCoefficientModule (quotientGradedModule X Y n) :=
  rfl

@[simp]
theorem quotientCoefficientCochainComplex_d_succ
    (X Y : ComplexCategory) (n : ℤ) :
    (quotientCoefficientCochainComplex X Y).d n (n + 1) =
      ModuleCat.ofHom
        (quotientLinearMapChangeScalars (quotientTotalDifferential X Y n).hom) := by
  change quotientCoefficientChange.map
      ((quotientDGMappingCochainComplex X Y).d n (n + 1)) = _
  rw [quotientDGMappingCochainComplex_d_succ]
  rfl

/-- Transport an integer-bilinear map to the universe-matched coefficient modules. -/
def quotientBilinearMapChangeScalars {M N P : ModuleCat.{1} ℤ}
    (f : M →ₗ[ℤ] N →ₗ[ℤ] P) :
    quotientCoefficientModule M →ₗ[QuotientCoefficientRing]
      quotientCoefficientModule N →ₗ[QuotientCoefficientRing]
        quotientCoefficientModule P where
  toFun x :=
    { toFun := fun y ↦ ULift.up (f x.down y.down)
      map_add' := fun y₁ y₂ ↦ by
        apply ULift.down_injective
        exact (f x.down).map_add y₁.down y₂.down
      map_smul' := fun r y ↦ by
        apply ULift.down_injective
        simp [ULift.smul_def] }
  map_add' x₁ x₂ := by
    ext y
    simp [quotientCoefficientCarrierModule]
  map_smul' r x := by
    ext y
    change f (r.down • x.down) y.down = r.down • f x.down y.down
    exact DFunLike.congr_fun (map_zsmul f r.down x.down) y.down

/-- Homogeneous quotient composition as a morphism out of the honest large tensor product. -/
def quotientCompositionTensorMap (X Y Z : ComplexCategory) (n m : ℤ) :
    quotientCoefficientModule (quotientGradedModule X Y n) ⊗
        quotientCoefficientModule (quotientGradedModule Y Z m) ⟶
      quotientCoefficientModule (quotientGradedModule X Z (n + m)) :=
  ModuleCat.ofHom (TensorProduct.lift
    (quotientBilinearMapChangeScalars (quotientCompositionMap X Y Z n m)))

@[simp]
theorem quotientCompositionTensorMap_tmul
    (X Y Z : ComplexCategory) (n m : ℤ)
    (x : quotientGradedModule X Y n) (y : quotientGradedModule Y Z m) :
    (quotientCompositionTensorMap X Y Z n m).hom
        (ULift.up x ⊗ₜ[QuotientCoefficientRing] ULift.up y) =
      ULift.up (quotientCompositionMap X Y Z n m x y) :=
  rfl

end QuotientCoefficient

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
