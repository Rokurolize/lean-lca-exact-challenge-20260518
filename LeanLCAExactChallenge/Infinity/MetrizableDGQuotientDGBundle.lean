/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientCompositionMerge
import Mathlib.Algebra.Homology.Monoidal

/-! # DG enrichment for the corrected Drinfeld quotient -/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory
open CategoryTheory.MonoidalCategory

/-- The monoidal carrier of the corrected quotient enrichment. -/
abbrev QuotientDGCochain :=
  CochainComplex (ModuleCat.{1} QuotientCoefficientRing) ℤ

/-- The coefficient-changed quotient differential in degree `n`. -/
def quotientCoefficientDifferential
    (X Y : ComplexCategory) (n : ℤ) :
    quotientCoefficientModule (quotientGradedModule X Y n) ⟶
      quotientCoefficientModule (quotientGradedModule X Y (n + 1)) :=
  ModuleCat.ofHom
    (quotientLinearMapChangeScalars (quotientTotalDifferential X Y n).hom)

/-- Quotient composition satisfies the cochain Leibniz identity after coefficient change. -/
theorem quotientCompositionTensorMap_leibniz
    (X Y Z : ComplexCategory) (n m : ℤ) :
  quotientCompositionTensorMap X Y Z n m ≫
      quotientCoefficientDifferential X Z (n + m) =
    ((𝟙 _ ⊗ₘ quotientCoefficientDifferential Y Z m) ≫
        quotientCompositionTensorMap X Y Z n (m + 1) ≫
        eqToHom (congrArg
          (fun k ↦ quotientCoefficientModule (quotientGradedModule X Z k))
          (rightLeibnizDegreeEq n m))) +
      m.negOnePow •
        ((quotientCoefficientDifferential X Y n ⊗ₘ 𝟙 _) ≫
          quotientCompositionTensorMap X Y Z (n + 1) m ≫
          eqToHom (congrArg
            (fun k ↦ quotientCoefficientModule (quotientGradedModule X Z k))
            (leftLeibnizDegreeEq n m))) := by
  apply quotientCoefficientTensorMap_ext_on_summands
  rintro ⟨w, d⟩ ⟨v, e⟩ x y
  have hright :
      (quotientTotalDifferential Y Z m).hom
          ((Limits.Sigma.ι
            (fun u : GradedSummandIndex Y Z m ↦ largeSummandModule u)
            ⟨v, e⟩).hom y) =
        (internalDifferentialFromSummand e +
          contractionDifferentialFromSummand e).hom y := by
    change
      (Limits.Sigma.ι
        (fun u : GradedSummandIndex Y Z m ↦ largeSummandModule u)
        ⟨v, e⟩ ≫ quotientTotalDifferential Y Z m).hom y = _
    rw [quotientTotalDifferential_inclusion]
  have hleft :
      (quotientTotalDifferential X Y n).hom
          ((Limits.Sigma.ι
            (fun u : GradedSummandIndex X Y n ↦ largeSummandModule u)
            ⟨w, d⟩).hom x) =
        (internalDifferentialFromSummand d +
          contractionDifferentialFromSummand d).hom x := by
    change
      (Limits.Sigma.ι
        (fun u : GradedSummandIndex X Y n ↦ largeSummandModule u)
        ⟨w, d⟩ ≫ quotientTotalDifferential X Y n).hom x = _
    rw [quotientTotalDifferential_inclusion]
  unfold quotientCoefficientDifferential
  rw [quotientCompositionTensorMap_comp_changeScalars_tmul]
  simp only [ModuleCat.hom_add, LinearMap.add_apply]
  rw [quotientCompositionTensorMap_changeScalars_right_cast_tmul] <;> try omega
  rw [Units.smul_def]
  simp only [ModuleCat.hom_smul, LinearMap.smul_apply]
  rw [quotientCompositionTensorMap_changeScalars_left_cast_tmul] <;> try omega
  apply ULift.down_injective
  rw [quotientCompositionMap_on_summands, hright, hleft]
  change _ = _ + (m.negOnePow : ℤ) • _
  simpa only [Units.smul_def] using largeSummandCompositionMap_leibniz d e x y

private lemma quotientCoefficientCast_comp_d
    (X Y : ComplexCategory) {a b c : ℤ} (hab : a = b)
    (hbc : b + 1 = c) (hac : a + 1 = c) :
    eqToHom (congrArg
        (fun k ↦ quotientCoefficientModule (quotientGradedModule X Y k)) hab) ≫
        (quotientCoefficientCochainComplex X Y).d b c =
      quotientCoefficientDifferential X Y a ≫
        eqToHom (congrArg
          (fun k ↦ quotientCoefficientModule (quotientGradedModule X Y k)) hac) := by
  subst b
  subst c
  rw [quotientCoefficientCochainComplex_d_succ]
  simp only [quotientCoefficientDifferential, eqToHom_refl, Category.comp_id,
    Category.id_comp]

/-- Composition of corrected quotient morphism cochain complexes. -/
def quotientDGComposition (K L M : ComplexCategory) :
    HomologicalComplex.tensorObj
        (quotientCoefficientCochainComplex L M)
        (quotientCoefficientCochainComplex K L) ⟶
      quotientCoefficientCochainComplex K M where
  f n := HomologicalComplex.mapBifunctorDesc fun p q h ↦
    (β_ _ _).hom ≫ quotientCompositionTensorMap K L M q p ≫
      eqToHom (congrArg
        (fun k ↦ quotientCoefficientModule (quotientGradedModule K M k))
        ((Int.add_comm q p).trans h))
  comm' n m hnm := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    rw [HomologicalComplex.ι_mapBifunctorDesc_assoc]
    rw [HomologicalComplex.mapBifunctor.d_eq]
    simp only [← Category.assoc, Preadditive.comp_add, Preadditive.add_comp,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂]
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
    simp only [quotientCoefficientCochainComplex_X]
    rw [quotientCoefficientCochainComplex_d_succ L M p,
      quotientCoefficientCochainComplex_d_succ K L q]
    have hqp : q + p = n := by omega
    have hnext : (q + p) + 1 = m := by omega
    have hleibniz := quotientCompositionTensorMap_leibniz K L M q p
    have hcast := quotientCoefficientCast_comp_d K M hqp hnm hnext
    erw [hcast]
    have hright (W : ModuleCat.{1} QuotientCoefficientRing)
        (g : quotientCoefficientModule (quotientGradedModule K M (q + (p + 1))) ⟶ W) :
        (quotientCoefficientDifferential L M p ▷
            quotientCoefficientModule (quotientGradedModule K L q)) ≫
              (β_ _ _).hom ≫ quotientCompositionTensorMap K L M q (p + 1) ≫ g =
          (β_ _ _).hom ≫
            (quotientCoefficientModule (quotientGradedModule K L q) ◁
              quotientCoefficientDifferential L M p) ≫
                quotientCompositionTensorMap K L M q (p + 1) ≫ g := by
      simpa only [Category.assoc] using
        BraidedCategory.braiding_naturality_left_assoc
          (quotientCoefficientDifferential L M p)
          (quotientCoefficientModule (quotientGradedModule K L q))
          (quotientCompositionTensorMap K L M q (p + 1) ≫ g)
    have hleft (W : ModuleCat.{1} QuotientCoefficientRing)
        (g : quotientCoefficientModule (quotientGradedModule K M ((q + 1) + p)) ⟶ W) :
        (quotientCoefficientModule (quotientGradedModule L M p) ◁
            quotientCoefficientDifferential K L q) ≫
              (β_ _ _).hom ≫ quotientCompositionTensorMap K L M (q + 1) p ≫ g =
          (β_ _ _).hom ≫
            (quotientCoefficientDifferential K L q ▷
              quotientCoefficientModule (quotientGradedModule L M p)) ≫
                quotientCompositionTensorMap K L M (q + 1) p ≫ g := by
      simpa only [Category.assoc] using
        BraidedCategory.braiding_naturality_right_assoc
          (quotientCoefficientModule (quotientGradedModule L M p))
          (quotientCoefficientDifferential K L q)
          (quotientCompositionTensorMap K L M (q + 1) p ≫ g)
    simp only [quotientCoefficientDifferential] at hright hleft
    simp only [curriedTensor_map_app, curriedTensor_obj_map]
    erw [hright, hleft]
    have h := congrArg
      (fun f ↦ (β_ _ _).hom ≫ f ≫
        eqToHom (congrArg
          (fun k ↦ quotientCoefficientModule (quotientGradedModule K M k)) hnext))
      hleibniz
    change @Eq
      (quotientCoefficientModule (quotientGradedModule L M p) ⊗
          quotientCoefficientModule (quotientGradedModule K L q) ⟶
        quotientCoefficientModule (quotientGradedModule K M m)) _ _
    convert h using 1 <;> simp only [Category.assoc, Preadditive.comp_add,
      Preadditive.add_comp,
      Linear.comp_smul, Linear.smul_comp, quotientCoefficientDifferential,
      MonoidalCategory.tensorHom_def, MonoidalCategory.whiskerLeft_id,
      MonoidalCategory.id_whiskerRight, Category.comp_id, Category.id_comp,
      Units.smul_def, eqToHom_trans] <;> rfl

@[simp]
theorem quotientDGComposition_f (K L M : ComplexCategory) (n : ℤ) :
    (quotientDGComposition K L M).f n =
      HomologicalComplex.mapBifunctorDesc fun p q h ↦
        (β_ _ _).hom ≫ quotientCompositionTensorMap K L M q p ≫
          eqToHom (congrArg
            (fun k ↦ quotientCoefficientModule (quotientGradedModule K M k))
            ((Int.add_comm q p).trans h)) :=
  rfl

/-- The coefficient-module span-singleton morphism at the quotient identity element. -/
def quotientIdentitySpan (K : ComplexCategory) :
    𝟙_ (ModuleCat.{1} QuotientCoefficientRing) ⟶
      quotientCoefficientModule (quotientGradedModule K K 0) :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton QuotientCoefficientRing _
    (ULift.up (quotientIdentityElement K)))

/-- The quotient identity element, regarded as a chain map from the monoidal unit. -/
def quotientDGIdentity (K : ComplexCategory) :
    𝟙_ QuotientDGCochain ⟶ quotientCoefficientCochainComplex K K :=
  HomologicalComplex.mkHomFromSingle (quotientIdentitySpan K) (by
    rintro _ rfl
    rw [quotientCoefficientCochainComplex_d_succ K K 0]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply ULift.down_injective
    change (quotientTotalDifferential K K 0).hom
      (x.down • quotientIdentityElement K) = 0
    calc
      _ = x.down • (quotientTotalDifferential K K 0).hom
          (quotientIdentityElement K) :=
        (quotientTotalDifferential K K 0).hom.toAddMonoidHom.map_zsmul _ _
      _ = 0 := by rw [quotientIdentityElement_closed, zsmul_zero])

@[simp]
theorem quotientDGIdentity_f_zero (K : ComplexCategory) :
    (quotientDGIdentity K).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))).hom ≫
        quotientIdentitySpan K := by
  unfold quotientDGIdentity
  apply HomologicalComplex.mkHomFromSingle_f

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
