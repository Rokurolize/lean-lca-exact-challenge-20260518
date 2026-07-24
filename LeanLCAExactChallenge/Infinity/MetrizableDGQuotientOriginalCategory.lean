/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientInclusion
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.CategoryTheory.Enriched.Basic

/-!
# The coefficient-changed original DG category

The original Hom cochain complexes are transported to the coefficient ring used by the
corrected Drinfeld quotient. This file constructs their composition and identity before
packaging the canonical zero-word enriched functor into the quotient.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

attribute [-instance] ULift.semiring

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

/-- A small integer module transported to the quotient's universe-matched coefficient ring. -/
abbrev OriginalCoefficientModule (M : ModuleCat.{0} ℤ) :
    ModuleCat.{1} QuotientCoefficientRing :=
  quotientCoefficientModule ((ModuleCat.uliftFunctor.{1} ℤ).obj M)

/-- Direct coefficient change from small integer modules to quotient coefficient modules. -/
def originalCoefficientChangeDirect : ModuleCat.{0} ℤ ⥤
    ModuleCat.{1} QuotientCoefficientRing :=
  ModuleCat.uliftFunctor.{1} ℤ ⋙ quotientCoefficientChange

/-- The original DG Hom cochain complex after coefficient change. -/
abbrev OriginalCoefficientCochainComplex (X Y : ComplexCategory) :
    QuotientDGCochain :=
  originalCoefficientCochainComplex X Y

@[simp]
theorem OriginalCoefficientCochainComplex_X
    (X Y : ComplexCategory) (n : ℤ) :
    (OriginalCoefficientCochainComplex X Y).X n =
      OriginalCoefficientModule ((dgHomZModuleCochainComplex X Y).X n) :=
  rfl

/-- Transport a small integer-bilinear map to quotient coefficient modules. -/
def originalTensorMapChangeScalars {M N P : ModuleCat.{0} ℤ}
    (f : M ⊗ N ⟶ P) :
    OriginalCoefficientModule M ⊗ OriginalCoefficientModule N ⟶
      OriginalCoefficientModule P :=
  ModuleCat.ofHom (TensorProduct.lift
    (quotientBilinearMapChangeScalars (uliftBilinearMap f)))

@[simp]
theorem originalTensorMapChangeScalars_tmul
    {M N P : ModuleCat.{0} ℤ} (f : M ⊗ N ⟶ P) (x : M) (y : N) :
    (originalTensorMapChangeScalars f).hom
      (ULift.up (ULift.up x) ⊗ₜ[QuotientCoefficientRing]
        ULift.up (ULift.up y)) =
      ULift.up (ULift.up (f.hom (x ⊗ₜ[ℤ] y))) :=
  rfl

/-- Composition on the coefficient-changed original DG Hom complexes. -/
def OriginalCoefficientDGComposition (K L M : ComplexCategory) :
    HomologicalComplex.tensorObj
      (OriginalCoefficientCochainComplex L M)
      (OriginalCoefficientCochainComplex K L) ⟶
      OriginalCoefficientCochainComplex K M where
  f n := HomologicalComplex.mapBifunctorDesc fun p q h =>
    originalTensorMapChangeScalars (dgCochainCompTensorReversed K L M h)
  comm' n m hnm := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    rw [HomologicalComplex.ι_mapBifunctorDesc_assoc]
    rw [HomologicalComplex.mapBifunctor.d_eq, ← Category.assoc, Preadditive.comp_add,
      Preadditive.add_comp, HomologicalComplex.mapBifunctor.ι_D₁,
      HomologicalComplex.mapBifunctor.ι_D₂]
    change p + q = n at hpq
    change n + 1 = m at hnm
    rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
      (show p + 1 = p + 1 by rfl) q m (by change p + 1 + q = m; omega)]
    rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ p
      (show q + 1 = q + 1 by rfl) m (by change p + (q + 1) = m; omega)]
    simp only [Linear.units_smul_comp, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc]
    rw [Units.smul_def, Units.smul_def]
    change _ = (1 : ℤ) • _ + (p.negOnePow : ℤ) • _
    rw [one_smul]
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext y x
    rcases y with ⟨y⟩
    rcases y with ⟨y⟩
    rcases x with ⟨x⟩
    rcases x with ⟨x⟩
    apply ULift.down_injective
    apply ULift.down_injective
    change CochainComplex.HomComplex.δ n m
        (x.comp y (by omega)) = _
    change _ =
      x.comp (CochainComplex.HomComplex.δ p (p + 1) y) (by omega) +
        p.negOnePow •
          (CochainComplex.HomComplex.δ q (q + 1) x).comp y (by omega)
    exact CochainComplex.HomComplex.δ_comp x y (by omega)
      (q + 1) (p + 1) m hnm rfl rfl

@[simp]
theorem OriginalCoefficientDGComposition_f
    (K L M : ComplexCategory) (n : ℤ) :
    (OriginalCoefficientDGComposition K L M).f n =
      HomologicalComplex.mapBifunctorDesc fun _p _q h =>
        originalTensorMapChangeScalars (dgCochainCompTensorReversed K L M h) :=
  rfl

/-- Identity span in the coefficient-changed original DG Hom complex. -/
def OriginalCoefficientDGIdentitySpan (K : ComplexCategory) :
    𝟙_ (ModuleCat.{1} QuotientCoefficientRing) ⟶
      (OriginalCoefficientCochainComplex K K).X 0 :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton QuotientCoefficientRing _
    (ULift.up (ULift.up (identityCochain K))))

/-- Identity of the coefficient-changed original DG category. -/
def OriginalCoefficientDGIdentity (K : ComplexCategory) :
    𝟙_ QuotientDGCochain ⟶ OriginalCoefficientCochainComplex K K :=
  HomologicalComplex.mkHomFromSingle (OriginalCoefficientDGIdentitySpan K) (by
    rintro _ rfl
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply ULift.down_injective
    apply ULift.down_injective
    change ((dgHomZModuleCochainComplex K K).d 0 1).hom
      (x.down • identityCochain K) = 0
    calc
      _ = x.down • ((dgHomZModuleCochainComplex K K).d 0 1).hom
          (identityCochain K) :=
        ((dgHomZModuleCochainComplex K K).d 0 1).hom.toAddMonoidHom.map_zsmul _ _
      _ = 0 := by rw [identityCochain_d, zsmul_zero])

@[simp]
theorem OriginalCoefficientDGIdentity_f_zero (K : ComplexCategory) :
    (OriginalCoefficientDGIdentity K).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))).hom ≫
        OriginalCoefficientDGIdentitySpan K :=
  rfl

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
