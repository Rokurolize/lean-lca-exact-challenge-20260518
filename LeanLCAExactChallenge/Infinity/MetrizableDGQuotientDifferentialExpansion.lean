import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientDifferentialEvaluation
import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientPairCancellation

/-!
# Expansion of the corrected Drinfeld differential square

This file decomposes the square of the candidate differential on an arbitrary word summand
and proves the internal-factor and double-contraction cancellations. The remaining mixed
structural-map commutation is isolated by the expansion.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory

theorem map_heq_of_target_eq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y₁ Y₂ : C} (hY : Y₁ = Y₂)
    {f : X ⟶ Y₁} {g : X ⟶ Y₂} (hfg : HEq f g) :
    HEq (F.map f) (F.map g) := by
  subst Y₂
  have hfg' : f = g := eq_of_heq hfg
  subst g
  rfl

theorem comp_eq_of_middle_eq_heq {C : Type*} [Category C]
    {X Y₁ Y₂ Z : C} (hY : Y₁ = Y₂)
    {f₁ : X ⟶ Y₁} {f₂ : X ⟶ Y₂} {g₁ : Y₁ ⟶ Z} {g₂ : Y₂ ⟶ Z}
    (hf : HEq f₁ f₂) (hg : HEq g₁ g₂) : f₁ ≫ g₁ = f₂ ≫ g₂ := by
  subst Y₂
  rw [eq_of_heq hf, eq_of_heq hg]

theorem cast_degreeProfile_eq_castWord_expansion
    {X Y : ComplexCategory} {w v : DrinfeldWord X Y} {n : ℤ}
    (h : w = v) (d : DegreeProfile w n) :
    cast (congrArg (fun q : DrinfeldWord X Y ↦ DegreeProfile q n) h) d =
      d.castWord h := by
  subst h
  rfl

theorem gradedSummandIndex_eq_of_castWord_eq
    {X Y : ComplexCategory} {w v : DrinfeldWord X Y} {n : ℤ}
    (h : w = v) (d : DegreeProfile w n) (e : DegreeProfile v n)
    (hd : d.castWord h = e) :
    (⟨w, d⟩ : GradedSummandIndex X Y n) = ⟨v, e⟩ := by
  apply Sigma.ext h
  have hde : d.castWord h ≍ e := heq_of_eq hd
  let hty := congrArg (fun q : DrinfeldWord X Y ↦ DegreeProfile q n) h
  apply (cast_heq_iff_heq hty d e).mp
  convert hde using 1
  exact cast_degreeProfile_eq_castWord_expansion h d

/-- Four-family expansion of the candidate differential square on one arbitrary summand. -/
theorem quotientTotalDifferential_inclusion_square_expansion
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    (Limits.Sigma.ι
        (fun s : GradedSummandIndex X Y n ↦ largeSummandModule s) ⟨w, d⟩ ≫
      quotientTotalDifferential X Y n) ≫ quotientTotalDifferential X Y (n + 1) =
      internalDifferentialFromSummand d ≫ quotientInternalDifferential X Y (n + 1) +
        internalDifferentialFromSummand d ≫
          quotientContractionDifferential X Y (n + 1) +
        contractionDifferentialFromSummand d ≫
          quotientInternalDifferential X Y (n + 1) +
        contractionDifferentialFromSummand d ≫
          quotientContractionDifferential X Y (n + 1) := by
  rw [quotientTotalDifferential_inclusion]
  simp only [quotientTotalDifferential, Preadditive.add_comp, Preadditive.comp_add]
  abel

/-- Expand the internal-then-internal family by its first differentiated factor. -/
theorem internalDifferentialFromSummand_comp_internalDifferential
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    internalDifferentialFromSummand d ≫ quotientInternalDifferential X Y (n + 1) =
      ∑ i, d.internalSign i •
        ((ModuleCat.uliftFunctor.{1} ℤ).map (internalDifferentialTensorMap d i) ≫
          internalDifferentialFromSummand (d.raise i)) := by
  change (∑ i, d.internalSign i • internalDifferentialLargeMap d i) ≫
      quotientInternalDifferential X Y (n + 1) = _
  simp only [Preadditive.sum_comp, largeModule_zsmul_comp,
    internalDifferentialLargeMap_comp_internalDifferential]

/-- Expand the internal-then-contraction family by its first differentiated factor. -/
theorem internalDifferentialFromSummand_comp_contractionDifferential
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    internalDifferentialFromSummand d ≫
        quotientContractionDifferential X Y (n + 1) =
      ∑ i, d.internalSign i •
        ((ModuleCat.uliftFunctor.{1} ℤ).map (internalDifferentialTensorMap d i) ≫
          contractionDifferentialFromSummand (d.raise i)) := by
  unfold internalDifferentialFromSummand
  simp only [Preadditive.sum_comp, largeModule_zsmul_comp,
    internalDifferentialLargeMap_comp_contractionDifferential]

/-- Expand the contraction-then-internal family by its first contracted position. -/
theorem contractionDifferentialFromSummand_comp_internalDifferential
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    contractionDifferentialFromSummand d ≫
        quotientInternalDifferential X Y (n + 1) =
      ∑ i, d.contractionSign i •
        ((ModuleCat.uliftFunctor.{1} ℤ).map (contractionTensorMap d i) ≫
          internalDifferentialFromSummand (d.contract i)) := by
  unfold contractionDifferentialFromSummand
  simp only [Preadditive.sum_comp, contractionLargeMap_comp_internalDifferential]

/-- Expand the contraction-then-contraction family by its first contracted position. -/
theorem contractionDifferentialFromSummand_comp_contractionDifferential
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    contractionDifferentialFromSummand d ≫
        quotientContractionDifferential X Y (n + 1) =
      ∑ i, d.contractionSign i •
        ((ModuleCat.uliftFunctor.{1} ℤ).map (contractionTensorMap d i) ≫
          contractionDifferentialFromSummand (d.contract i)) := by
  unfold contractionDifferentialFromSummand
  simp only [Preadditive.sum_comp, contractionLargeMap_comp_contractionDifferential]
  rfl

def contractionPairLargeMap
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (p : ContractionPairIndex (k + 1)) :
    Quiver.Hom (largeSummandModule
      (⟨{ length := k + 2, intermediate := intermediate }, d⟩ :
        GradedSummandIndex X Y n))
      (quotientGradedModule X Y ((n + 1) + 1)) :=
  (ModuleCat.uliftFunctor.{1} ℤ).map
      (contractionTensorMap d p.1 ≫
        contractionTensorMap (d.contract p.1) p.2) ≫
    Limits.Sigma.ι
      (fun s : GradedSummandIndex X Y ((n + 1) + 1) ↦ largeSummandModule s)
      ⟨eraseIntermediate
          (eraseIntermediate
            ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y)
            p.1) p.2,
        (d.contract p.1).contract p.2⟩

theorem contractionPairLargeMap_swap
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (p : ContractionPairIndex (k + 1)) :
    contractionPairLargeMap d (contractionPairSwap p) =
      contractionPairLargeMap d p := by
  let s₁ : GradedSummandIndex X Y ((n + 1) + 1) :=
    ⟨eraseIntermediate
        (eraseIntermediate
          ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y)
          (contractionPairSwap p).1) (contractionPairSwap p).2,
      (d.contract (contractionPairSwap p).1).contract
        (contractionPairSwap p).2⟩
  let s₂ : GradedSummandIndex X Y ((n + 1) + 1) :=
    ⟨eraseIntermediate
        (eraseIntermediate
          ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y)
          p.1) p.2,
      (d.contract p.1).contract p.2⟩
  have hs : s₁ = s₂ := by
    exact (gradedSummandIndex_eq_of_castWord_eq
      (eraseIntermediate_twice_swap intermediate p.1 p.2)
      ((d.contract p.1).contract p.2)
      ((d.contract (contractionPairSwap p).1).contract
        (contractionPairSwap p).2)
      (DegreeProfile.contract_contract_swap intermediate d p.1 p.2)).symm
  have hm : largeSummandModule s₁ = largeSummandModule s₂ :=
    congrArg largeSummandModule hs
  unfold contractionPairLargeMap
  apply comp_eq_of_middle_eq_heq hm
  · obtain ⟨htarget, _⟩ := test_contractionPairTargetIso_hom_eqToHom d p.1 p.2
    apply map_heq_of_target_eq (ModuleCat.uliftFunctor.{1} ℤ) htarget.symm
    exact (test_contractionPairTensorMap_heq d p.1 p.2).symm
  · exact congr_arg_heq
      (fun s ↦ Limits.Sigma.ι
        (fun t : GradedSummandIndex X Y ((n + 1) + 1) ↦ largeSummandModule t) s) hs

theorem contractionTensorMap_comp_contractionLargeMap
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    (ModuleCat.uliftFunctor.{1} ℤ).map (contractionTensorMap d i) ≫
        contractionLargeMap (d.contract i) j =
      (d.contract i).contractionSign j • contractionPairLargeMap d (i, j) := by
  unfold contractionLargeMap contractionPairLargeMap
  rw [Preadditive.comp_zsmul]
  rw [← Category.assoc, ← Functor.map_comp]

def contractionPairTerm
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (p : ContractionPairIndex (k + 1)) :
    Quiver.Hom (largeSummandModule
      (⟨{ length := k + 2, intermediate := intermediate }, d⟩ :
        GradedSummandIndex X Y n))
      (quotientGradedModule X Y ((n + 1) + 1)) :=
  contractionPairCoefficientFor d.arrowDegree p • contractionPairLargeMap d p

theorem sum_contractionPairTerm_eq_zero
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n) :
    ∑ p : ContractionPairIndex (k + 1), contractionPairTerm d p = 0 := by
  unfold contractionPairTerm
  exact sum_contractionPairIndex_smul_eq_zero_of_swap
    (contractionPairCoefficientFor d.arrowDegree) (contractionPairLargeMap d)
    (contractionPairCoefficientFor_swap d.arrowDegree)
    (contractionPairLargeMap_swap d)

theorem contractionDifferentialFromSummand_comp_contractionDifferential_eq_pair_sum
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n) :
    contractionDifferentialFromSummand d ≫
        quotientContractionDifferential X Y (n + 1) =
      ∑ i, ∑ j, contractionPairTerm d (i, j) := by
  rw [contractionDifferentialFromSummand_comp_contractionDifferential]
  unfold contractionDifferentialFromSummand
  apply Finset.sum_congr rfl
  intro i _
  rw [Preadditive.comp_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [contractionTensorMap_comp_contractionLargeMap, smul_smul]
  unfold contractionPairTerm contractionPairCoefficientFor
  rw [DegreeProfile.contractionSign_eq_contractionSignFor,
    DegreeProfile.contractionSign_eq_contractionSignFor]
  rfl

theorem contractionDifferentialFromSummand_comp_contractionDifferential_eq_zero_ge_two
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n) :
    contractionDifferentialFromSummand d ≫
        quotientContractionDifferential X Y (n + 1) = 0 := by
  rw [contractionDifferentialFromSummand_comp_contractionDifferential_eq_pair_sum]
  rw [← Fintype.sum_prod_type]
  exact sum_contractionPairTerm_eq_zero d

theorem contractionDifferentialFromSummand_comp_contractionDifferential_eq_zero
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    contractionDifferentialFromSummand d ≫
        quotientContractionDifferential X Y (n + 1) = 0 := by
  cases w with
  | mk k intermediate =>
      cases k with
      | zero =>
          unfold contractionDifferentialFromSummand
          simp
      | succ k =>
          cases k with
          | zero =>
              rw [contractionDifferentialFromSummand_comp_contractionDifferential]
              have hsecond : contractionDifferentialFromSummand (d.contract 0) = 0 := by
                unfold contractionDifferentialFromSummand
                apply Finset.sum_eq_zero
                intro j _
                have hlength : (eraseIntermediate
                    ({ length := 0 + 1, intermediate := intermediate } :
                      DrinfeldWord X Y) 0).length = 0 := by
                  have h := eraseIntermediate_length
                    ({ length := 0 + 1, intermediate := intermediate } :
                      DrinfeldWord X Y) 0
                  change (eraseIntermediate
                    ({ length := 0 + 1, intermediate := intermediate } :
                      DrinfeldWord X Y) 0).length + 1 = 1 at h
                  omega
                exact Fin.elim0 (Fin.cast hlength j)
              rw [Fin.sum_univ_succ, hsecond]
              simp
          | succ k =>
              exact contractionDifferentialFromSummand_comp_contractionDifferential_eq_zero_ge_two d

theorem quotientContractionDifferential_square
    (X Y : ComplexCategory) (n : ℤ) :
    quotientContractionDifferential X Y n ≫
      quotientContractionDifferential X Y (n + 1) = 0 := by
  apply Limits.Sigma.hom_ext
  intro s
  rw [← Category.assoc, quotientContractionDifferential_inclusion,
    Limits.comp_zero]
  exact contractionDifferentialFromSummand_comp_contractionDifferential_eq_zero s.2

/-- Ordered pairs of distinct internal-factor positions. -/
abbrev InternalPairIndex (k : ℕ) := {p : Fin k × Fin k // p.1 ≠ p.2}

def internalPairLargeMap
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i j : Fin (w.length + 1)) :
    Quiver.Hom (largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n))
      (quotientGradedModule X Y ((n + 1) + 1)) :=
  (ModuleCat.uliftFunctor.{1} ℤ).map
      (internalDifferentialTensorMap d i ≫
        internalDifferentialTensorMap (d.raise i) j) ≫
    Limits.Sigma.ι
      (fun s : GradedSummandIndex X Y ((n + 1) + 1) ↦ largeSummandModule s)
      ⟨w, (d.raise i).raise j⟩

theorem internalPairLargeMap_comm_of_ne
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i j : Fin (w.length + 1)) (hij : i ≠ j) :
    internalPairLargeMap d i j = internalPairLargeMap d j i := by
  let s₁ : GradedSummandIndex X Y ((n + 1) + 1) :=
    ⟨w, (d.raise i).raise j⟩
  let s₂ : GradedSummandIndex X Y ((n + 1) + 1) :=
    ⟨w, (d.raise j).raise i⟩
  have hs : s₁ = s₂ := by
    apply Sigma.ext
    · rfl
    · exact heq_of_eq (d.raise_comm i j)
  have hm : largeSummandModule s₁ = largeSummandModule s₂ :=
    congrArg largeSummandModule hs
  apply comp_eq_of_middle_eq_heq hm
  · apply map_heq_of_target_eq (ModuleCat.uliftFunctor.{1} ℤ)
      (congrArg (fun e ↦ summandModule e) (d.raise_comm i j))
    exact internalDifferentialTensorMap_comm_heq_of_ne d i j hij
  · exact congr_arg_heq
      (fun s ↦ Limits.Sigma.ι
        (fun t : GradedSummandIndex X Y ((n + 1) + 1) ↦ largeSummandModule t) s) hs

theorem internalPairLargeMap_self_eq_zero
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin (w.length + 1)) :
    internalPairLargeMap d i i = 0 := by
  unfold internalPairLargeMap
  rw [internalDifferentialTensorMap_self_comp, Functor.map_zero]
  simp

theorem internalDifferentialMap_comp_internalLargeMap
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i j : Fin (w.length + 1)) :
    (ModuleCat.uliftFunctor.{1} ℤ).map (internalDifferentialTensorMap d i) ≫
        internalDifferentialLargeMap (d.raise i) j =
      internalPairLargeMap d i j := by
  unfold internalDifferentialLargeMap internalPairLargeMap
  rw [Functor.map_comp]
  simp only [Category.assoc]

/-- Exchange the two internal-factor differential orders. -/
def internalPairSwap {k : ℕ} (p : InternalPairIndex k) : InternalPairIndex k :=
  ⟨⟨p.1.2, p.1.1⟩, Ne.symm p.2⟩

@[simp]
theorem internalPairSwap_fst {k : ℕ} (p : InternalPairIndex k) :
    (internalPairSwap p).1.1 = p.1.2 := rfl

@[simp]
theorem internalPairSwap_snd {k : ℕ} (p : InternalPairIndex k) :
    (internalPairSwap p).1.2 = p.1.1 := rfl

theorem internalPairSwap_ne {k : ℕ} (p : InternalPairIndex k) :
    internalPairSwap p ≠ p := by
  intro h
  exact p.2 (congrArg (fun q ↦ q.1.1) h).symm

@[simp]
theorem internalPairSwap_involutive {k : ℕ} (p : InternalPairIndex k) :
    internalPairSwap (internalPairSwap p) = p := by
  apply Subtype.ext
  exact Prod.swap_swap p.1

def internalAllPairCoefficient
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (p : Fin (w.length + 1) × Fin (w.length + 1)) : ℤ :=
  d.internalSign p.1 * (d.raise p.1).internalSign p.2

/-- Product of the two Koszul coefficients for an ordered pair of internal factors. -/
def internalPairCoefficient
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (p : InternalPairIndex (w.length + 1)) : ℤ :=
  internalAllPairCoefficient d p.1

/-- Exchanging two distinct internal-factor orders negates their combined coefficient. -/
theorem internalPairCoefficient_swap
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (p : InternalPairIndex (w.length + 1)) :
    internalPairCoefficient d (internalPairSwap p) = -internalPairCoefficient d p := by
  rcases lt_or_gt_of_ne p.2 with h | h
  · rw [internalPairCoefficient, internalPairCoefficient,
      internalAllPairCoefficient, internalAllPairCoefficient,
      internalPairSwap_fst, internalPairSwap_snd,
      d.internalSign_raise_of_lt p.1.2 p.1.1 h,
      d.internalSign_raise_of_le p.1.1 p.1.2 h.le]
    ring
  · rw [internalPairCoefficient, internalPairCoefficient,
      internalAllPairCoefficient, internalAllPairCoefficient,
      internalPairSwap_fst, internalPairSwap_snd,
      d.internalSign_raise_of_le p.1.2 p.1.1 h.le,
      d.internalSign_raise_of_lt p.1.1 p.1.2 h]
    ring

theorem internalAllPairCoefficient_swap_of_ne
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (p : Fin (w.length + 1) × Fin (w.length + 1))
    (hp : p.1 ≠ p.2) :
    internalAllPairCoefficient d p.swap = -internalAllPairCoefficient d p := by
  rcases p with ⟨i, j⟩
  let q : InternalPairIndex (w.length + 1) := ⟨(i, j), hp⟩
  simpa [q, internalPairCoefficient, internalPairSwap, Prod.swap] using
    internalPairCoefficient_swap d q

def internalAllPairTerm
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (p : Fin (w.length + 1) × Fin (w.length + 1)) :
    Quiver.Hom (largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n))
      (quotientGradedModule X Y ((n + 1) + 1)) :=
  internalAllPairCoefficient d p • internalPairLargeMap d p.1 p.2

theorem internalAllPairTerm_add_swap_eq_zero
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (p : Fin (w.length + 1) × Fin (w.length + 1)) :
    internalAllPairTerm d p + internalAllPairTerm d p.swap = 0 := by
  by_cases hp : p.1 = p.2
  · rcases p with ⟨i, j⟩
    change i = j at hp
    subst j
    simp [internalAllPairTerm, internalPairLargeMap_self_eq_zero]
  · rw [internalAllPairTerm, internalAllPairTerm,
      internalAllPairCoefficient_swap_of_ne d p hp]
    rw [show internalPairLargeMap d p.swap.1 p.swap.2 =
        internalPairLargeMap d p.1 p.2 by
      exact internalPairLargeMap_comm_of_ne d p.2 p.1 (Ne.symm hp)]
    simp

theorem sum_internalAllPairTerm_eq_zero
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    ∑ p : Fin (w.length + 1) × Fin (w.length + 1), internalAllPairTerm d p = 0 := by
  classical
  simpa using Finset.sum_involution (s := Finset.univ)
    (f := internalAllPairTerm d) (fun p _ ↦ p.swap)
    (fun p _ ↦ internalAllPairTerm_add_swap_eq_zero d p)
    (fun p _ hp ↦ by
      intro hswap
      have hdiag : p.1 = p.2 := (congrArg Prod.fst hswap).symm
      rw [internalAllPairTerm] at hp
      rw [hdiag, internalPairLargeMap_self_eq_zero] at hp
      simp at hp)
    (fun _ _ ↦ Finset.mem_univ _)
    (fun p _ ↦ Prod.swap_swap p)

theorem internalDifferentialFromSummand_comp_internalDifferential_eq_pair_sum
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    internalDifferentialFromSummand d ≫ quotientInternalDifferential X Y (n + 1) =
      ∑ i, ∑ j, internalAllPairTerm d (i, j) := by
  rw [internalDifferentialFromSummand_comp_internalDifferential]
  unfold internalDifferentialFromSummand
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, Finset.smul_sum,
    smul_smul, internalDifferentialMap_comp_internalLargeMap,
    internalAllPairTerm, internalAllPairCoefficient]

theorem internalDifferentialFromSummand_comp_internalDifferential_eq_zero
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    internalDifferentialFromSummand d ≫ quotientInternalDifferential X Y (n + 1) = 0 := by
  rw [internalDifferentialFromSummand_comp_internalDifferential_eq_pair_sum]
  rw [← Fintype.sum_prod_type]
  exact sum_internalAllPairTerm_eq_zero d

theorem quotientInternalDifferential_square
    (X Y : ComplexCategory) (n : ℤ) :
    quotientInternalDifferential X Y n ≫
      quotientInternalDifferential X Y (n + 1) = 0 := by
  apply Limits.Sigma.hom_ext
  intro s
  rw [← Category.assoc, quotientInternalDifferential_inclusion, Limits.comp_zero]
  exact internalDifferentialFromSummand_comp_internalDifferential_eq_zero s.2

/-- The combined coefficients of all distinct ordered internal-factor pairs sum to zero. -/
theorem sum_internalPairCoefficient_eq_zero
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    ∑ p : InternalPairIndex (w.length + 1), internalPairCoefficient d p = 0 := by
  classical
  apply Finset.sum_ninvolution internalPairSwap
  · intro p
    rw [internalPairCoefficient_swap]
    omega
  · intro p _
    exact internalPairSwap_ne p
  · intro p
    simp
  · intro p
    exact internalPairSwap_involutive p

/-- Swap-invariant structural maps cancel with the actual internal-pair coefficients. -/
theorem sum_internalPairCoefficient_smul_eq_zero_of_swap
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) {P Q : ModuleCat.{1} ℤ}
    (f : InternalPairIndex (w.length + 1) → Quiver.Hom P Q)
    (hf : ∀ p, f (internalPairSwap p) = f p) :
    ∑ p, internalPairCoefficient d p • f p = 0 := by
  classical
  apply Finset.sum_ninvolution internalPairSwap
  · intro p
    rw [internalPairCoefficient_swap, hf]
    simp
  · intro p _
    exact internalPairSwap_ne p
  · intro p
    simp
  · intro p
    exact internalPairSwap_involutive p

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
