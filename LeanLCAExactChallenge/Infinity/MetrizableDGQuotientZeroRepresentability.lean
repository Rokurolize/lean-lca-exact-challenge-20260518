/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientEnrichedCoefficientUniqueness
import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientWordEvaluationCore

/-! # Zero representability in the corrected Drinfeld quotient -/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge.Infinity.MetrizableBoundedComplexes.DrinfeldWord

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped MonoidalCategory ZeroObject

private theorem tensor_subsingleton_left
    (M N : ModuleCat.{0} ℤ) [Subsingleton M] :
    Subsingleton (↑(M ⊗ N) : Type) := by
  change Subsingleton (TensorProduct ℤ M N)
  refine ⟨fun x y ↦ ?_⟩
  suffices h : ∀ z : TensorProduct ℤ M N, z = 0 by
    exact (h x).trans (h y).symm
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul m n =>
      rw [show m = 0 from Subsingleton.elim _ _]
      exact TensorProduct.zero_tmul _ _
  | add x y hx hy => simp [hx, hy]

private theorem tensor_subsingleton_right
    (M N : ModuleCat.{0} ℤ) [Subsingleton N] :
    Subsingleton (↑(M ⊗ N) : Type) := by
  change Subsingleton (TensorProduct ℤ M N)
  refine ⟨fun x y ↦ ?_⟩
  suffices h : ∀ z : TensorProduct ℤ M N, z = 0 by
    exact (h x).trans (h y).symm
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul m n =>
      rw [show n = 0 from Subsingleton.elim _ _]
      exact TensorProduct.tmul_zero _ _
  | add x y hx hy => simp [hx, hy]

private theorem subsingleton_of_iso {M N : ModuleCat.{u} ℤ} (e : M ≅ N)
    [Subsingleton N] : Subsingleton M := by
  refine ⟨fun x y ↦ ?_⟩
  have hxy : e.hom.hom x = e.hom.hom y := Subsingleton.elim _ _
  calc
    x = e.inv.hom (e.hom.hom x) := by
      simpa only [ModuleCat.comp_apply, ModuleCat.id_apply] using
        (ConcreteCategory.congr_hom e.hom_inv_id x).symm
    _ = e.inv.hom (e.hom.hom y) := congrArg e.inv.hom hxy
    _ = y := by
      simpa only [ModuleCat.comp_apply, ModuleCat.id_apply] using
        ConcreteCategory.congr_hom e.hom_inv_id y

private theorem zeroSourceHomDegree_subsingleton (X : ComplexCategory) (n : ℤ) :
    Subsingleton ((dgHomZModuleCochainComplex (0 : ComplexCategory) X).X n) := by
  refine ⟨fun a b ↦ ?_⟩
  apply CochainComplex.HomComplex.Cochain.ext
  intro p q hpq
  let h0 : IsZero ((underlyingComplex (0 : ComplexCategory)).X p) :=
    (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p).map_isZero
      ((BoundedComplexCategory.ι MetrizableLCA.{0}).map_isZero (isZero_zero _))
  exact h0.eq_of_src _ _

private theorem zeroTargetHomDegree_subsingleton (X : ComplexCategory) (n : ℤ) :
    Subsingleton ((dgHomZModuleCochainComplex X (0 : ComplexCategory)).X n) := by
  refine ⟨fun a b ↦ ?_⟩
  apply CochainComplex.HomComplex.Cochain.ext
  intro p q hpq
  let h0 : IsZero ((underlyingComplex (0 : ComplexCategory)).X q) :=
    (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) q).map_isZero
      ((BoundedComplexCategory.ι MetrizableLCA.{0}).map_isZero (isZero_zero _))
  exact h0.eq_of_tgt _ _

theorem summandModule_zero_source_subsingleton :
    ∀ (k : ℕ) {Y : ComplexCategory}
      (intermediate : Fin k → CorrectedAcyclicComplexCategory) {n : ℤ}
      (d : DegreeProfile
        ({ length := k, intermediate := intermediate } : DrinfeldWord 0 Y) n),
      Subsingleton (summandModule d)
  | 0, Y, intermediate, n, d => by
      have hintermediate : intermediate =
          (Fin.elim0 : Fin 0 → CorrectedAcyclicComplexCategory) := Subsingleton.elim _ _
      subst intermediate
      letI := zeroSourceHomDegree_subsingleton Y n
      exact subsingleton_of_iso (nilSummandIsoOriginal 0 Y d)
  | k + 1, Y, intermediate, n, d => by
      letI : Subsingleton (factorModule d 0) := by
        unfold factorModule
        have hsource :
            ({ length := k + 1, intermediate := intermediate } :
              DrinfeldWord (0 : ComplexCategory) Y).arrowSource 0 = 0 := by
          unfold arrowSource
          exact vertex_zero _
        have htarget :
            ({ length := k + 1, intermediate := intermediate } :
              DrinfeldWord (0 : ComplexCategory) Y).arrowTarget 0 =
              (intermediate 0).obj := by
          unfold arrowTarget vertex object
          simp only [Fin.cases_succ]
          rw [show (0 : Fin (k + 2)) = (0 : Fin (k + 1)).castSucc by rfl]
          rw [Fin.lastCases_castSucc]
        rw [hsource, htarget]
        change Subsingleton
          ((dgHomZModuleCochainComplex 0 (intermediate 0).obj).X (d.arrowDegree 0))
        exact zeroSourceHomDegree_subsingleton _ _
      letI : Subsingleton
          (↑(factorModule d 0 ⊗ summandModule (tailDegreeProfile d)) : Type) :=
        tensor_subsingleton_left _ _
      exact subsingleton_of_iso
        (eqToIso (AnnihilatingEnrichedFunctorData.summandModule_succ d))

theorem summandModule_zero_target_subsingleton :
    ∀ (k : ℕ) {X : ComplexCategory}
      (intermediate : Fin k → CorrectedAcyclicComplexCategory) {n : ℤ}
      (d : DegreeProfile
        ({ length := k, intermediate := intermediate } : DrinfeldWord X 0) n),
      Subsingleton (summandModule d)
  | 0, X, intermediate, n, d => by
      have hintermediate : intermediate =
          (Fin.elim0 : Fin 0 → CorrectedAcyclicComplexCategory) := Subsingleton.elim _ _
      subst intermediate
      letI := zeroTargetHomDegree_subsingleton X n
      exact subsingleton_of_iso (nilSummandIsoOriginal X 0 d)
  | k + 1, X, intermediate, n, d => by
      letI : Subsingleton (summandModule (tailDegreeProfile d)) :=
        summandModule_zero_target_subsingleton k (fun i ↦ intermediate i.succ)
          (tailDegreeProfile d)
      letI : Subsingleton
          (↑(factorModule d 0 ⊗ summandModule (tailDegreeProfile d)) : Type) :=
        tensor_subsingleton_right _ _
      exact subsingleton_of_iso
        (eqToIso (AnnihilatingEnrichedFunctorData.summandModule_succ d))

private theorem largeSummandModule_zero_source_subsingleton
    {Y : ComplexCategory} {n : ℤ}
    (s : GradedSummandIndex (0 : ComplexCategory) Y n) :
    Subsingleton (largeSummandModule s) := by
  letI : Subsingleton (summandModule s.2) :=
    summandModule_zero_source_subsingleton s.1.length s.1.intermediate s.2
  refine ⟨fun x y ↦ ?_⟩
  apply ULift.ext
  exact Subsingleton.elim x.down y.down

private theorem largeSummandModule_zero_target_subsingleton
    {X : ComplexCategory} {n : ℤ}
    (s : GradedSummandIndex X (0 : ComplexCategory) n) :
    Subsingleton (largeSummandModule s) := by
  letI : Subsingleton (summandModule s.2) :=
    summandModule_zero_target_subsingleton s.1.length s.1.intermediate s.2
  refine ⟨fun x y ↦ ?_⟩
  apply ULift.ext
  exact Subsingleton.elim x.down y.down

theorem quotientGradedModule_zero_source_subsingleton
    (Y : ComplexCategory) (n : ℤ) :
    Subsingleton (quotientGradedModule (0 : ComplexCategory) Y n) := by
  classical
  let Z : GradedSummandIndex (0 : ComplexCategory) Y n → ModuleCat.{1} ℤ :=
    fun s ↦ largeSummandModule s
  let e := ModuleCat.coprodIsoDirectSum.{0, 1, 1} Z
  letI : Subsingleton (ModuleCat.of ℤ
      (DirectSum (GradedSummandIndex (0 : ComplexCategory) Y n) (fun s ↦ Z s))) := by
    refine ⟨fun x y ↦ ?_⟩
    suffices h : ∀ z : DirectSum (GradedSummandIndex (0 : ComplexCategory) Y n)
        (fun s ↦ Z s), z = 0 by
      exact (h x).trans (h y).symm
    intro z
    induction z using DirectSum.induction_on with
    | zero => rfl
    | of i x =>
        letI : Subsingleton (Z i) := largeSummandModule_zero_source_subsingleton i
        rw [show x = 0 from Subsingleton.elim _ _]
        simp
    | add x y hx hy => simp [hx, hy]
  exact subsingleton_of_iso e

theorem quotientGradedModule_zero_target_subsingleton
    (X : ComplexCategory) (n : ℤ) :
    Subsingleton (quotientGradedModule X (0 : ComplexCategory) n) := by
  classical
  let Z : GradedSummandIndex X (0 : ComplexCategory) n → ModuleCat.{1} ℤ :=
    fun s ↦ largeSummandModule s
  let e := ModuleCat.coprodIsoDirectSum.{0, 1, 1} Z
  letI : Subsingleton (ModuleCat.of ℤ
      (DirectSum (GradedSummandIndex X (0 : ComplexCategory) n) (fun s ↦ Z s))) := by
    refine ⟨fun x y ↦ ?_⟩
    suffices h : ∀ z : DirectSum (GradedSummandIndex X (0 : ComplexCategory) n)
        (fun s ↦ Z s), z = 0 by
      exact (h x).trans (h y).symm
    intro z
    induction z using DirectSum.induction_on with
    | zero => rfl
    | of i x =>
        letI : Subsingleton (Z i) := largeSummandModule_zero_target_subsingleton i
        rw [show x = 0 from Subsingleton.elim _ _]
        simp
    | add x y hx hy => simp [hx, hy]
  exact subsingleton_of_iso e

private theorem quotientCoefficientModule_subsingleton
    (M : ModuleCat.{1} ℤ) [Subsingleton M] :
    Subsingleton (quotientCoefficientModule M) := by
  refine ⟨fun x y ↦ ?_⟩
  apply ULift.ext
  exact Subsingleton.elim x.down y.down

theorem quotientCoefficientDegree_zero_source_subsingleton
    (Y : ComplexCategory) (n : ℤ) :
    Subsingleton ((quotientCoefficientCochainComplex
      (0 : ComplexCategory) Y).X n) := by
  change Subsingleton
    (quotientCoefficientModule (quotientGradedModule (0 : ComplexCategory) Y n))
  letI : Subsingleton (quotientGradedModule (0 : ComplexCategory) Y n) :=
    quotientGradedModule_zero_source_subsingleton Y n
  exact quotientCoefficientModule_subsingleton _

theorem quotientCoefficientDegree_zero_target_subsingleton
    (X : ComplexCategory) (n : ℤ) :
    Subsingleton ((quotientCoefficientCochainComplex
      X (0 : ComplexCategory)).X n) := by
  change Subsingleton
    (quotientCoefficientModule (quotientGradedModule X (0 : ComplexCategory) n))
  letI : Subsingleton (quotientGradedModule X (0 : ComplexCategory) n) :=
    quotientGradedModule_zero_target_subsingleton X n
  exact quotientCoefficientModule_subsingleton _

private theorem quotientCochain_isZero_of_components_subsingleton
    (K : QuotientDGCochain) (h : ∀ n, Subsingleton (K.X n)) : IsZero K := by
  refine ⟨fun L => ⟨⟨⟨0⟩, fun f => ?_⟩⟩,
    fun L => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩
  · apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    letI : Subsingleton (K.X n) := h n
    rw [show x = 0 from Subsingleton.elim _ _]
    simp
  · apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    letI : Subsingleton (K.X n) := h n
    exact Subsingleton.elim _ _

theorem quotientCoefficientCochainComplex_zero_source_isZero
    (Y : ComplexCategory) :
    IsZero (quotientCoefficientCochainComplex (0 : ComplexCategory) Y) :=
  quotientCochain_isZero_of_components_subsingleton _
    (quotientCoefficientDegree_zero_source_subsingleton Y)

theorem quotientCoefficientCochainComplex_zero_target_isZero
    (X : ComplexCategory) :
    IsZero (quotientCoefficientCochainComplex X (0 : ComplexCategory)) :=
  quotientCochain_isZero_of_components_subsingleton _
    (quotientCoefficientDegree_zero_target_subsingleton X)

/-- The zero bounded complex, regarded as an object of the corrected quotient enrichment. -/
def quotientDGZeroObject : CorrectedQuotientDGCategory :=
  Opposite.op (0 : ComplexCategory)

theorem quotientDGEnrichedHom_fromZero_isZero
    (K : CorrectedQuotientDGCategory) :
    IsZero (quotientDGEnrichedHom quotientDGZeroObject K) := by
  change IsZero (quotientCoefficientCochainComplex K.unop (0 : ComplexCategory))
  exact quotientCoefficientCochainComplex_zero_target_isZero K.unop

theorem quotientDGEnrichedHom_toZero_isZero
    (K : CorrectedQuotientDGCategory) :
    IsZero (quotientDGEnrichedHom K quotientDGZeroObject) := by
  change IsZero (quotientCoefficientCochainComplex (0 : ComplexCategory) K.unop)
  exact quotientCoefficientCochainComplex_zero_source_isZero K.unop

/-- Every quotient enriched Hom out of the zero object is canonically the zero complex. -/
def quotientDGEnrichedHomFromZeroIso
    (K : CorrectedQuotientDGCategory) :
    quotientDGEnrichedHom quotientDGZeroObject K ≅ 0 :=
  (quotientDGEnrichedHom_fromZero_isZero K).iso (isZero_zero QuotientDGCochain)

/-- Every quotient enriched Hom into the zero object is canonically the zero complex. -/
def quotientDGEnrichedHomToZeroIso
    (K : CorrectedQuotientDGCategory) :
    quotientDGEnrichedHom K quotientDGZeroObject ≅ 0 :=
  (quotientDGEnrichedHom_toZero_isZero K).iso (isZero_zero QuotientDGCochain)

/-- Natural enriched-Hom representability of the zero object in both variances. -/
structure QuotientDGZeroEnrichedHomRepresentability where
  fromZero : ∀ X : CorrectedQuotientDGCategory,
    quotientDGEnrichedHom quotientDGZeroObject X ≅ 0
  toZero : ∀ X : CorrectedQuotientDGCategory,
    quotientDGEnrichedHom X quotientDGZeroObject ≅ 0
  fromZero_comp : ∀ X Y : CorrectedQuotientDGCategory,
    quotientDGEnrichedComp quotientDGZeroObject X Y ≫ (fromZero Y).hom = 0
  comp_toZero : ∀ X Y : CorrectedQuotientDGCategory,
    quotientDGEnrichedComp X Y quotientDGZeroObject ≫ (toZero X).hom = 0

/-- The corrected Drinfeld quotient has a genuine enriched zero object. -/
noncomputable def quotientDGZeroEnrichedHomRepresentability :
    QuotientDGZeroEnrichedHomRepresentability where
  fromZero := quotientDGEnrichedHomFromZeroIso
  toZero := quotientDGEnrichedHomToZeroIso
  fromZero_comp X Y := by
    exact (isZero_zero QuotientDGCochain).eq_of_tgt _ _
  comp_toZero X Y := by
    exact (isZero_zero QuotientDGCochain).eq_of_tgt _ _

end LeanLCAExactChallenge.Infinity.MetrizableBoundedComplexes.DrinfeldWord
