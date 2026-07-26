/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientWordEvaluationCochain

/-! # Positive-word differential compatibility -/

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

@[reassoc]
private lemma ιTensorObj_tensorHom_local
    {K₁ K₂ L₁ L₂ : QuotientDGCochain} (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂)
    {p q n : ℤ} (h : p + q = n) :
    HomologicalComplex.ιTensorObj K₁ K₂ p q n h ≫
        (HomologicalComplex.tensorHom f g).f n =
      (f.f p ⊗ₘ g.f q) ≫ HomologicalComplex.ιTensorObj L₁ L₂ p q n h := by
  exact GradedObject.Monoidal.ι_tensorHom f.f g.f p q n h

/-- Composing a homogeneous target element with the target identity returns that element. -/
theorem composeElement_identity
    (X Y : ComplexCategory) (p : ℤ) (x : (E.hom X Y).X p) :
    E.composeElement X Y Y p 0 p (by omega) x
        (targetDGIdentityElement (E.obj Y)) = x := by
  let B := E.hom X Y
  let I := 𝟙_ (QuotientDGCochain)
  let μ := eComp QuotientDGCochain (E.obj Y) (E.obj Y) (E.obj X)
  let η := eId QuotientDGCochain (E.obj Y)
  have hunit := congrArg (fun f : B ⟶ B ↦ f.f p)
    (e_id_comp QuotientDGCochain (E.obj Y) (E.obj X))
  have happ := ConcreteCategory.congr_hom hunit x
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at happ
  change (((HomologicalComplex.leftUnitor' B).inv p ≫ _) ≫ _) x = x at happ
  rw [HomologicalComplex.leftUnitor'_inv] at happ
  have hwhisker :
      (η ▷ B).f p = (HomologicalComplex.tensorHom η (𝟙 B)).f p := rfl
  rw [hwhisker] at happ
  simp only [Category.assoc, ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply] at happ
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))
  have hι := ιTensorObj_tensorHom_local η (𝟙 B)
    (show 0 + p = p by omega)
  have hιapp := ConcreteCategory.congr_hom hι
    (e.inv.hom (1 : QuotientCoefficientRing) ⊗ₜ[QuotientCoefficientRing] x)
  simp only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.tensorHom_tmul,
    HomologicalComplex.id_f, CategoryTheory.id_apply] at hιapp
  dsimp only [e] at hιapp
  have hιapp' :
      (HomologicalComplex.tensorHom η (𝟙 B)).f p
          ((HomologicalComplex.ιTensorObj
            (HomologicalComplex.tensorUnit
              (ModuleCat.{1} QuotientCoefficientRing) (ComplexShape.up ℤ))
            B 0 p p (by omega))
            ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
              (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))).inv.hom 1
                ⊗ₜ[QuotientCoefficientRing] x)) =
        (HomologicalComplex.ιTensorObj
          (E.obj Y ⟶[QuotientDGCochain] E.obj Y) B 0 p p (by omega))
          (η.f 0
              ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
                (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))).inv.hom 1)
              ⊗ₜ[QuotientCoefficientRing] x) := by
    exact hιapp
  have hμ := congrArg (fun z ↦ μ.f p z) hιapp'
  have hright := hμ.symm.trans happ
  change E.composeElement X Y Y p 0 p (by omega) x
      (targetDGIdentityElement (E.obj Y)) = x at hright
  exact hright

/-- Transporting the output degree of a homogeneous target composition only changes its
degree proof. -/
theorem composeElement_cast_output
    (X Y Z : ComplexCategory) (p q n m : ℤ)
    (h : q + p = n) (hn : n = m)
    (x : (E.hom X Y).X p) (y : (E.hom Y Z).X q) :
    (eqToHom (congrArg (fun r ↦ (E.hom X Z).X r) hn)).hom
        (E.composeElement X Y Z p q n h x y) =
      E.composeElement X Y Z p q m (h.trans hn) x y := by
  subst m
  rfl

/-- The tail degree after raising the head is the original tail degree. -/
def tailDegree_raise_zero_eq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    n + 1 - (d.raise 0).arrowDegree 0 + 1 = tailDegree d := by
  simp [DegreeProfile.raise, tailDegree]

/-- Raising the head factor does not alter the tail profile after degree transport. -/
theorem tailDegreeProfile_raise_zero
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    (tailDegreeProfile (d.raise 0)).castTotal (tailDegree_raise_zero_eq d) =
      tailDegreeProfile d := by
  apply DegreeProfile.ext
  funext i
  simp [DegreeProfile.raise]

/-- The tail degree after raising a tail factor is the successor of the original tail degree. -/
def tailDegree_raise_succ_eq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    n + 1 - (d.raise i.succ).arrowDegree 0 + 1 = tailDegree d + 1 := by
  have hne : (0 : Fin (k + 2)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  simp [DegreeProfile.raise, tailDegree, hne]
  omega

/-- Raising a tail factor is the same as raising the corresponding tail-profile factor. -/
theorem tailDegreeProfile_raise_succ
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    (tailDegreeProfile (d.raise i.succ)).castTotal (tailDegree_raise_succ_eq d i) =
      (tailDegreeProfile d).raise i := by
  apply DegreeProfile.ext
  funext j
  simp [DegreeProfile.raise]

/-- The leading contraction suffix is the tail degree. -/
theorem contractionSuffix_zero_eq_tail
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    d.contractionSuffix 0 = tailDegree d := by
  unfold DegreeProfile.contractionSuffix tailDegree
  rw [Finset.sum_filter, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, Nat.lt_irrefl, if_false,
    Nat.zero_lt_succ, if_true, zero_add]
  have hd := d.totalDegree
  rw [Fin.sum_univ_succ] at hd
  change d.arrowDegree 0 + (∑ i : Fin (k + 1), d.arrowDegree i.succ) - (k + 1) = n at hd
  omega

/-- The leading contraction sign is the parity of the tail degree. -/
theorem contractionSign_zero_eq_tail
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    d.contractionSign 0 = (tailDegree d).negOnePow := by
  rw [d.contractionSign_eq_negOnePow, contractionSuffix_zero_eq_tail]

/-- The leading internal suffix is one less than the tail degree. -/
theorem suffixTotal_zero_eq_tail_sub_one
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    d.suffixTotal 0 = tailDegree d - 1 := by
  unfold DegreeProfile.suffixTotal tailDegree
  rw [Finset.sum_filter, Fin.sum_univ_succ]
  simp only [Fin.lt_def, Fin.val_zero, Fin.val_succ, Nat.lt_irrefl,
    if_false, Nat.zero_lt_succ, if_true, zero_add]
  have hd := d.totalDegree
  rw [Fin.sum_univ_succ] at hd
  change d.arrowDegree 0 + (∑ i : Fin (k + 1), d.arrowDegree i.succ) - (k + 1) = n at hd
  omega

/-- The leading internal sign is the negative of the tail-degree parity. -/
theorem internalSign_zero_eq_neg_tail
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    d.internalSign 0 = -(tailDegree d).negOnePow := by
  rw [d.internalSign_eq_negOnePow, suffixTotal_zero_eq_tail_sub_one]
  rw [show tailDegree d - 1 = tailDegree d + (-1) by omega,
    Int.negOnePow_add, Int.negOnePow_neg, Int.negOnePow_one]
  simp

/-- Internal signs on tail factors agree with the tail profile. -/
theorem internalSign_succ_eq_tail
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    d.internalSign i.succ = (tailDegreeProfile d).internalSign i := by
  rw [d.internalSign_eq_negOnePow,
    (tailDegreeProfile d).internalSign_eq_negOnePow]
  congr 1
  unfold DegreeProfile.suffixTotal
  simp only [tailDegreeProfile_arrowDegree]
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_succ]
  simp

/-- Contraction signs on tail positions agree with the tail profile. -/
theorem contractionSign_succ_eq_tail
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin k) :
    d.contractionSign i.succ = (tailDegreeProfile d).contractionSign i := by
  rw [d.contractionSign_eq_negOnePow,
    (tailDegreeProfile d).contractionSign_eq_negOnePow]
  congr 1
  unfold DegreeProfile.contractionSuffix
  simp only [tailDegreeProfile_arrowDegree]
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_succ]
  simp

/-- The head Hom complex of a positive word is the explicit source-to-first-intermediate Hom. -/
def positiveHeadHomComplexEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (_d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    dgHomZModuleCochainComplex
        (({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y).arrowSource 0)
        (({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y).arrowTarget 0) =
      dgHomZModuleCochainComplex X (intermediate 0).obj := by
  have hs :
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y).arrowSource 0 = X :=
    arrowSource_zero_eq_source _
  have ht :
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y).arrowTarget 0 =
        (intermediate 0).obj := by
    unfold arrowTarget vertex object
    rw [Fin.cases_succ]
    have hzero : (0 : Fin (k + 2)) = (0 : Fin (k + 1)).castSucc := rfl
    rw [hzero, Fin.lastCases_castSucc]
  exact congrArg₂ dgHomZModuleCochainComplex hs ht

/-- In original-Hom coordinates, the head factor differential is the Hom-complex differential. -/
theorem factorDifferential_zero_original
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d 0) :
    (eqToHom (factorModule_zero_succ (d.raise 0))).hom
        ((factorDifferential d 0 0).hom x) =
      ((dgHomZModuleCochainComplex X (intermediate 0).obj).d
        (d.arrowDegree 0) ((d.raise 0).arrowDegree 0))
          ((eqToHom (factorModule_zero_succ d)).hom x) := by
  let hC := positiveHeadHomComplexEq d
  have hcomm := ConcreteCategory.congr_hom
    ((eqToHom hC).comm (d.arrowDegree 0) (d.arrowDegree 0 + 1)) x
  simp only [HomologicalComplex.eqToHom_f, ModuleCat.comp_apply] at hcomm
  unfold factorDifferential
  simp only [eq_self, ↓reduceDIte]
  change ((eqToHom (factorModule_zero_succ (d.raise 0))).hom
      (((dgHomZModuleCochainComplex
        (({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y).arrowSource 0)
        (({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y).arrowTarget 0)).d
          (d.arrowDegree 0) (d.arrowDegree 0 + 1)).hom x)) = _
  change ((dgHomZModuleCochainComplex X (intermediate 0).obj).d
      (d.arrowDegree 0) (d.arrowDegree 0 + 1)).hom
        ((eqToHom (factorModule_zero_succ d)).hom x) =
    (eqToHom (factorModule_zero_succ (d.raise 0))).hom
      (((dgHomZModuleCochainComplex
        (({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y).arrowSource 0)
        (({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y).arrowTarget 0)).d
          (d.arrowDegree 0) (d.arrowDegree 0 + 1)).hom x) at hcomm
  exact hcomm.symm

/-- The first-factor map intertwines the head internal differential. -/
theorem firstFactorMap_factorDifferential_zero
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d 0) :
    E.firstFactorMap (d.raise 0) ((factorDifferential d 0 0).hom x) =
      ((E.hom X (intermediate 0).obj).d
        (d.arrowDegree 0) (d.arrowDegree 0 + 1)) (E.firstFactorMap d x) := by
  unfold firstFactorMap
  change E.factorMap X (intermediate 0).obj ((d.raise 0).arrowDegree 0)
      ((eqToHom (factorModule_zero_succ (d.raise 0))).hom
        ((factorDifferential d 0 0).hom x)) = _
  rw [factorDifferential_zero_original]
  simpa [DegreeProfile.raise] using
    (E.factorMap_d X (intermediate 0).obj (d.arrowDegree 0)
      ((eqToHom (factorModule_zero_succ d)).hom x)).symm

/-- The natural differential target degree of the contracted head is the head degree. -/
def firstContractionDifferentialTargetEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    (-1 + d.arrowDegree 0) + 1 = d.arrowDegree 0 := by omega

/-- The contracted raised-head degree is the original head degree. -/
def raisedHeadContractDegreeEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    -1 + (d.raise 0).arrowDegree 0 = d.arrowDegree 0 := by
  simp [DegreeProfile.raise]

set_option maxHeartbeats 4000000 in
-- Elaborating the dependent degree transports in this formula exceeds the default limit.
/-- The differential of the first factor followed by a contraction is the factor minus the
same construction applied to the factor differential. -/
theorem firstContractionMap_d
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d 0) :
    (eqToHom (congrArg
      (fun q ↦ (E.hom X (intermediate 0).obj).X q)
      (firstContractionDifferentialTargetEq d))).hom
        (((E.hom X (intermediate 0).obj).d
          (-1 + d.arrowDegree 0) ((-1 + d.arrowDegree 0) + 1))
            (E.firstContractionMap d x)) =
      E.firstFactorMap d x -
        (eqToHom (congrArg
          (fun q ↦ (E.hom X (intermediate 0).obj).X q)
          (raisedHeadContractDegreeEq d))).hom
            (E.firstContractionMap (d.raise 0) ((factorDifferential d 0 0).hom x)) := by
  let C := E.hom X (intermediate 0).obj
  let hout := firstContractionDifferentialTargetEq d
  let τ : C.X ((-1 + d.arrowDegree 0) + 1) ⟶ C.X (d.arrowDegree 0) :=
    eqToHom (congrArg C.X hout)
  have hleib := E.composeElement_d X (intermediate 0).obj (intermediate 0).obj
    (d.arrowDegree 0) (-1) (E.firstFactorMap d x) (E.contraction (intermediate 0))
  have hcast := congrArg (fun z ↦ τ.hom z) hleib
  simp only [map_add, Units.smul_def, map_zsmul] at hcast
  have hunitCast := E.composeElement_cast_output X (intermediate 0).obj
    (intermediate 0).obj (d.arrowDegree 0) ((-1 : ℤ) + 1)
    ((-1 + d.arrowDegree 0) + 1) (d.arrowDegree 0)
    (by omega) hout (E.firstFactorMap d x)
    (((E.hom (intermediate 0).obj (intermediate 0).obj).d
      (-1) ((-1 : ℤ) + 1)) (E.contraction (intermediate 0)))
  have hdiffCast := E.composeElement_cast_output X (intermediate 0).obj
    (intermediate 0).obj (d.arrowDegree 0 + 1) (-1)
    ((-1 + d.arrowDegree 0) + 1) (d.arrowDegree 0)
    (by omega) hout
    (((E.hom X (intermediate 0).obj).d
      (d.arrowDegree 0) (d.arrowDegree 0 + 1)) (E.firstFactorMap d x))
    (E.contraction (intermediate 0))
  dsimp only [τ, C] at hcast
  have hcontr :
      ((E.hom (intermediate 0).obj (intermediate 0).obj).d
        (-1) ((-1 : ℤ) + 1)) (E.contraction (intermediate 0)) =
        targetDGIdentityElement (E.obj (intermediate 0).obj) := by
    simpa using E.contraction_d (intermediate 0)
  have hidentity :
      E.composeElement X (intermediate 0).obj (intermediate 0).obj
        (d.arrowDegree 0) ((-1 : ℤ) + 1) (d.arrowDegree 0) (by omega)
        (E.firstFactorMap d x) (targetDGIdentityElement (E.obj (intermediate 0).obj)) =
      E.firstFactorMap d x := by
    simpa using E.composeElement_identity X (intermediate 0).obj
      (d.arrowDegree 0) (E.firstFactorMap d x)
  rw [hunitCast, hdiffCast, hcontr, hidentity,
    ← E.firstFactorMap_factorDifferential_zero] at hcast
  have hraised :
      (eqToHom (congrArg C.X (raisedHeadContractDegreeEq d))).hom
          (E.firstContractionMap (d.raise 0) ((factorDifferential d 0 0).hom x)) =
        E.composeElement X (intermediate 0).obj (intermediate 0).obj
          (d.arrowDegree 0 + 1) (-1) (d.arrowDegree 0) (by omega)
          (E.firstFactorMap (d.raise 0) ((factorDifferential d 0 0).hom x))
          (E.contraction (intermediate 0)) := by
    unfold firstContractionMap composeFirstMap
    simpa [C, raisedHeadContractDegreeEq, DegreeProfile.raise] using
      E.composeElement_cast_output X (intermediate 0).obj (intermediate 0).obj
        ((d.raise 0).arrowDegree 0) (-1)
        (-1 + (d.raise 0).arrowDegree 0) (d.arrowDegree 0) rfl
        (raisedHeadContractDegreeEq d)
        (E.firstFactorMap (d.raise 0) ((factorDifferential d 0 0).hom x))
        (E.contraction (intermediate 0))
  rw [hraised]
  have hfirst :
      E.firstContractionMap d x =
        E.composeElement X (intermediate 0).obj (intermediate 0).obj
          (d.arrowDegree 0) (-1) (-1 + d.arrowDegree 0) rfl
          (E.firstFactorMap d x) (E.contraction (intermediate 0)) := by
    rfl
  rw [hfirst]
  simpa only [C, τ, hout, Int.negOnePow_neg, Int.negOnePow_one,
    Units.val_neg, Units.val_one, neg_one_smul, one_smul,
    sub_eq_add_neg] using hcast

end AnnihilatingEnrichedFunctorData

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
