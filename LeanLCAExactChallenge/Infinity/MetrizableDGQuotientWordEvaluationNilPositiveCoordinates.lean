/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientWordEvaluationHeadContractionTail

/-! # Zero-left/positive-right coordinates for corrected Drinfeld evaluation

This module normalizes the result of adjoining a zero-length word on the left of a positive
Drinfeld word.  The resulting positive word has the same intermediate objects, its first degree
is the sum of the two boundary degrees, and its recursive tail is exactly the original positive
word's tail.  These are the dependent coordinates needed for the remaining multiplicativity
base case.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

namespace AnnihilatingEnrichedFunctorData

variable {D : Type*} [EnrichedCategory QuotientDGCochain D]
    (E : AnnihilatingEnrichedFunctorData D)

/-- Prefixing a positive word by an arbitrary zero-length word only changes its source. -/
theorem nilAppendPositiveWord_eq
    {W X Y : ComplexCategory} {k : ℕ}
    (intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory) :
    (nil W X).append
        ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) =
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord W Y) := by
  simp only [append, nil, Nat.zero_add, DrinfeldWord.mk.injEq]
  constructor
  · trivial
  refine (Fin.heq_fun_iff (Nat.zero_add (k + 1))).mpr ?_
  intro i
  simp only [Fin.addCases, not_lt_zero, ↓reduceDIte, Nat.add_zero,
    Fin.subNat_zero, eq_rec_constant]
  apply congrArg intermediate
  apply Fin.ext
  rfl

/-- The canonical positive profile obtained by composing a zero-word profile on the left. -/
def nilPositiveDegreeProfile
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord W Y)
      (p + n) :=
  ((nilDegreeProfile W X p).append d).castWord
    (nilAppendPositiveWord_eq intermediate)

/-- The normalized zero-left/positive-right profile consists of the merged head degree followed
by the unchanged recursive tail degrees. -/
theorem nilPositiveDegreeProfile_degreeList
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    (nilPositiveDegreeProfile (W := W) p d).degreeList =
      (p + d.arrowDegree 0) :: (tailDegreeProfile d).degreeList := by
  calc
    (nilPositiveDegreeProfile (W := W) p d).degreeList =
        ((nilDegreeProfile W X p).append d).degreeList :=
      degreeList_castWord ((nilDegreeProfile W X p).append d)
        (nilAppendPositiveWord_eq intermediate)
    _ = degreeBoundaryMerge (nilDegreeProfile W X p).degreeList d.degreeList :=
      DegreeProfile.degreeList_append _ _
    _ = degreeBoundaryMerge [p]
        (d.arrowDegree 0 :: (tailDegreeProfile d).degreeList) := by
      rw [degreeList_eq_head_cons_tail d]
      congr 1
    _ = (p + d.arrowDegree 0) :: (tailDegreeProfile d).degreeList := by
      rfl

/-- The first degree of a zero-left/positive-right composite is the sum of the two ordinary
boundary degrees. -/
theorem nilPositiveDegreeProfile_arrowDegree_zero
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    (nilPositiveDegreeProfile (W := W) p d).arrowDegree 0 =
      p + d.arrowDegree 0 := by
  have hsplit := degreeList_eq_head_cons_tail
    (nilPositiveDegreeProfile (W := W) p d)
  have hfull := nilPositiveDegreeProfile_degreeList (W := W) p d
  exact (List.cons.inj (hsplit.symm.trans hfull)).1

/-- Removing the merged head leaves the original positive word's tail degree. -/
theorem nilPositiveTailDegree_eq
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    tailDegree (nilPositiveDegreeProfile (W := W) p d) = tailDegree d := by
  unfold tailDegree
  rw [nilPositiveDegreeProfile_arrowDegree_zero]
  omega

/-- The normalized recursive tail profile in the original tail degree. -/
def nilPositiveTailProfile
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    DegreeProfile (tailWord (Y := Y) intermediate) (tailDegree d) :=
  (tailDegreeProfile (nilPositiveDegreeProfile (W := W) p d)).transport rfl
    (nilPositiveTailDegree_eq (W := W) p d)

/-- The normalized recursive tail profile is exactly the original tail profile. -/
theorem nilPositiveTailProfile_eq
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    nilPositiveTailProfile (W := W) p d = tailDegreeProfile d := by
  apply DegreeProfile.eq_of_degreeList_eq
  have hsplit := degreeList_eq_head_cons_tail
    (nilPositiveDegreeProfile (W := W) p d)
  have hhead := nilPositiveDegreeProfile_arrowDegree_zero (W := W) p d
  have hsplit' :
      (nilPositiveDegreeProfile (W := W) p d).degreeList =
        (p + d.arrowDegree 0) ::
          (tailDegreeProfile
            (nilPositiveDegreeProfile (W := W) p d)).degreeList :=
    hsplit.trans (congrArg
      (fun a : ℤ ↦ a ::
        (tailDegreeProfile
          (nilPositiveDegreeProfile (W := W) p d)).degreeList) hhead)
  have hfull := nilPositiveDegreeProfile_degreeList (W := W) p d
  have htail :
      (tailDegreeProfile
          (nilPositiveDegreeProfile (W := W) p d)).degreeList =
        (tailDegreeProfile d).degreeList :=
    (List.cons.inj (hsplit'.symm.trans hfull)).2
  calc
    (nilPositiveTailProfile (W := W) p d).degreeList =
        (tailDegreeProfile
          (nilPositiveDegreeProfile (W := W) p d)).degreeList := by
      exact DegreeProfile.degreeList_transport rfl
        (nilPositiveTailDegree_eq (W := W) p d)
        (tailDegreeProfile (nilPositiveDegreeProfile (W := W) p d))
    _ = (tailDegreeProfile d).degreeList := htail

/-- Canonical transport from the recursively exposed tail to the original positive tail. -/
def nilPositiveTailSummandIso
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    summandModule
        (tailDegreeProfile (nilPositiveDegreeProfile (W := W) p d)) ≅
      summandModule (tailDegreeProfile d) :=
  summandModuleTransportIso rfl
      (nilPositiveTailDegree_eq (W := W) p d)
      (tailDegreeProfile (nilPositiveDegreeProfile (W := W) p d)) ≪≫
    eqToIso (congrArg summandModule (nilPositiveTailProfile_eq (W := W) p d))

private theorem nilPositiveComp_eqToHom
    {A B C : ModuleCat.{0} ℤ} (f : A ⟶ B) (g : B ⟶ C)
    (hf : ∃ h : A = B, f = eqToHom h)
    (hg : ∃ h : B = C, g = eqToHom h) :
    ∃ h : A = C, f ≫ g = eqToHom h := by
  obtain ⟨hAB, rfl⟩ := hf
  obtain ⟨hBC, rfl⟩ := hg
  exact ⟨hAB.trans hBC, by simp⟩

private theorem nilPositiveEqToHom_heq_id
    {A B : ModuleCat.{0} ℤ} (h : A = B) :
    HEq (eqToHom h) (𝟙 A) := by
  subst B
  rfl

private theorem nilPositiveSummandModuleCastWordIso_hom_eqToHom
    {X Y : ComplexCategory} {w v : DrinfeldWord X Y} {n : ℤ}
    (h : w = v) (d : DegreeProfile w n) :
    ∃ hM : summandModule d = summandModule (d.castWord h),
      (summandModuleCastWordIso h d).hom = eqToHom hM := by
  subst v
  exact ⟨rfl, rfl⟩

/-- The recursive tail transport is one equality transport. -/
theorem nilPositiveTailSummandIso_hom_eqToHom
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    ∃ h : summandModule
          (tailDegreeProfile (nilPositiveDegreeProfile (W := W) p d)) =
        summandModule (tailDegreeProfile d),
      (nilPositiveTailSummandIso (W := W) p d).hom = eqToHom h := by
  unfold nilPositiveTailSummandIso summandModuleTransportIso
  simp only [Iso.trans_hom, eqToIso.hom]
  exact nilPositiveComp_eqToHom _ _ ⟨_, rfl⟩ ⟨_, rfl⟩

/-- The normalized composite summand is its merged head factor tensored with the unchanged
recursive tail summand. -/
def nilPositiveSummandIso
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    summandModule ((nilDegreeProfile W X p).append d) ≅
      factorModule (nilPositiveDegreeProfile (W := W) p d) 0 ⊗
        summandModule (tailDegreeProfile d) :=
  summandModuleCastWordIso (nilAppendPositiveWord_eq intermediate)
      ((nilDegreeProfile W X p).append d) ≪≫
    eqToIso (summandModule_succ (nilPositiveDegreeProfile (W := W) p d)) ≪≫
    MonoidalCategory.tensorIso (Iso.refl _)
      (nilPositiveTailSummandIso (W := W) p d)

/-- The composite positive-coordinate transport is heterogeneously the identity. -/
theorem nilPositiveSummandIso_hom_heq_id
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    HEq (nilPositiveSummandIso (W := W) p d).hom
      (𝟙 (summandModule ((nilDegreeProfile W X p).append d))) := by
  unfold nilPositiveSummandIso
  simp only [Iso.trans_hom, MonoidalCategory.tensorIso_hom,
    Iso.refl_hom, eqToIso.hom]
  obtain ⟨h₁, hh₁⟩ := nilPositiveSummandModuleCastWordIso_hom_eqToHom
    (nilAppendPositiveWord_eq intermediate)
    ((nilDegreeProfile W X p).append d)
  obtain ⟨h₃, hh₃⟩ := nilPositiveTailSummandIso_hom_eqToHom
    (W := W) p d
  let h₂ := summandModule_succ (nilPositiveDegreeProfile (W := W) p d)
  have hTensor : ∃ h,
      (𝟙 (factorModule (nilPositiveDegreeProfile (W := W) p d) 0) ⊗ₘ
          (nilPositiveTailSummandIso (W := W) p d).hom) = eqToHom h := by
    rw [hh₃]
    exact ⟨congrArg₂ (fun A B : ModuleCat.{0} ℤ ↦ A ⊗ B) rfl h₃,
      by simp⟩
  have hFirst : ∃ h,
      (summandModuleCastWordIso (nilAppendPositiveWord_eq intermediate)
          ((nilDegreeProfile W X p).append d)).hom ≫ eqToHom h₂ = eqToHom h :=
    nilPositiveComp_eqToHom _ _ ⟨h₁, hh₁⟩ ⟨h₂, rfl⟩
  rw [← Category.assoc]
  obtain ⟨h, hh⟩ := nilPositiveComp_eqToHom _ _ hFirst hTensor
  rw [hh]
  exact nilPositiveEqToHom_heq_id h

end AnnihilatingEnrichedFunctorData
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
