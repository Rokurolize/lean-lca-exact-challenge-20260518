import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientDifferentialEvaluation
import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientEraseFactors

/-!
# Expansion of the corrected Drinfeld differential square

This file decomposes the square of the candidate differential on an arbitrary word summand
and proves the coefficient cancellation for distinct pairs of internal-factor differentials.
The remaining structural-map commutation and double-contraction identities are not asserted.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory

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

/-- Ordered pairs of distinct internal-factor positions. -/
abbrev InternalPairIndex (k : ℕ) := {p : Fin k × Fin k // p.1 ≠ p.2}

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

/-- Product of the two Koszul coefficients for an ordered pair of internal factors. -/
def internalPairCoefficient
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (p : InternalPairIndex (w.length + 1)) : ℤ :=
  d.internalSign p.1.1 * (d.raise p.1.1).internalSign p.1.2

/-- Exchanging two distinct internal-factor orders negates their combined coefficient. -/
theorem internalPairCoefficient_swap
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (p : InternalPairIndex (w.length + 1)) :
    internalPairCoefficient d (internalPairSwap p) = -internalPairCoefficient d p := by
  rcases lt_or_gt_of_ne p.2 with h | h
  · rw [internalPairCoefficient, internalPairCoefficient,
      internalPairSwap_fst, internalPairSwap_snd,
      d.internalSign_raise_of_le p.1.2 p.1.1 h.le,
      d.internalSign_raise_of_lt p.1.1 p.1.2 h]
    ring
  · rw [internalPairCoefficient, internalPairCoefficient,
      internalPairSwap_fst, internalPairSwap_snd,
      d.internalSign_raise_of_lt p.1.2 p.1.1 h,
      d.internalSign_raise_of_le p.1.1 p.1.2 h.le]
    ring

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
