/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientWordEvaluationNilPositiveSummand
import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientInclusionFunctor

/-! # Zero-left/positive-right summand composition on pure tensors

This module applies the normalized zero-left/positive-right composition map to canonical pure
head/tail coordinates.  The zero-word factor composes with the positive head and the recursive
tail passes through unchanged.
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

set_option maxHeartbeats 4000000 in
-- Normalizing the dependent source and target coordinates expands the generic merge map.
/-- Quotient summand composition with a zero word composes the first two factors and preserves
the positive tail. -/
theorem summandCompositionMap_nil_positive_coordinates
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    summandCompositionMap (nilDegreeProfile W X p) d ≫
        (nilPositiveSummandIso (W := W) p d).hom =
      ((summandLastFactorIso (nilDegreeProfile W X p)).hom ⊗ₘ
          (summandFirstFactorIso d).hom) ≫
        (tensorModuleListAppendIso
          (compositionLeftPrefix (nilDegreeProfile W X p) ++
            [factorModule (nilDegreeProfile W X p) (Fin.last (nil W X).length)])
          (factorModule d 0 :: compositionRightSuffix d)).hom ≫
        eqToHom (congrArg tensorModuleList
          (appendBoundaryListsEq
            (compositionLeftPrefix (nilDegreeProfile W X p))
            (factorModule (nilDegreeProfile W X p) (Fin.last (nil W X).length))
            (factorModule d 0) (compositionRightSuffix d))) ≫
        (α_ (factorModule (nilDegreeProfile W X p) 0) (factorModule d 0)
          (tensorModuleList (compositionRightSuffix d))).inv ≫
        (nilPositiveHeadCompositionMap (W := W) p d ⊗ₘ
          eqToHom (nilPositiveTailListEq d)) := by
  rw [summandCompositionMap_eq_boundary_decomposition]
  simp only [Category.assoc]
  slice_lhs 5 6 =>
    rw [nilPositiveTarget_transport]
  slice_lhs 4 6 =>
    change
      (adjacentMergeAfter [] (ys := compositionRightSuffix d)
          (compositionBoundaryMap (nilDegreeProfile W X p) d)).tensorMap ≫
        (tensorMapDataReplaceAfter []
          (eqToHom (nilPositiveBoundaryModule_eq (W := W) p d))
          (compositionRightSuffix d)).tensorMap ≫
        eqToHom (nilPositiveTargetTailEq (W := W) p d)
    rw [nilPositiveBoundaryTailMap]

set_option maxHeartbeats 4000000 in
-- Applying the transported summand-composition equality expands several dependent tensor maps.
/-- A zero-word factor composed with a positive pure tensor composes only with its head. -/
theorem summandCompositionMap_nil_positive_apply_tensor
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : (dgHomZModuleCochainComplex W X).X p)
    (y : factorModule d 0)
    (t : summandModule (tailDegreeProfile d)) :
    (nilPositiveSummandIso (W := W) p d).hom.hom
        ((summandCompositionMap (nilDegreeProfile W X p) d).hom
          ((nilSummandIsoOriginal W X (nilDegreeProfile W X p)).inv.hom x ⊗ₜ[ℤ]
            (eqToHom (summandModule_succ d).symm).hom (y ⊗ₜ[ℤ] t))) =
      (nilPositiveHeadCompositionMap (W := W) p d).hom
          ((eqToHom (factorModule_nilDegreeProfile W X p).symm).hom x ⊗ₜ[ℤ] y) ⊗ₜ[ℤ]
        t := by
  change ((summandCompositionMap (nilDegreeProfile W X p) d ≫
      (nilPositiveSummandIso (W := W) p d).hom).hom
        ((nilSummandIsoOriginal W X (nilDegreeProfile W X p)).inv.hom x ⊗ₜ[ℤ]
          (eqToHom (summandModule_succ d).symm).hom (y ⊗ₜ[ℤ] t))) = _
  rw [summandCompositionMap_nil_positive_coordinates]
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul]
  have hleft := ConcreteCategory.congr_hom
    (nilSummandIsoOriginal_inv_comp_lastFactorIso_hom W X p) x
  simp only [ModuleCat.comp_apply] at hleft
  rw [hleft]
  have hright := ConcreteCategory.congr_hom
    (nilPositiveRightSource_decompose d) (y ⊗ₜ[ℤ] t)
  simp only [ModuleCat.comp_apply] at hright
  rw [hright]
  change
    (nilPositiveHeadCompositionMap (W := W) p d ⊗ₘ
        eqToHom (nilPositiveTailListEq d)).hom
      ((α_ (factorModule (nilDegreeProfile W X p) 0) (factorModule d 0)
          (tensorModuleList (compositionRightSuffix d))).inv.hom
        ((tensorModuleListAppendIso
          [factorModule (nilDegreeProfile W X p) 0]
          (factorModule d 0 :: compositionRightSuffix d)).hom.hom
          ((ρ_ (factorModule (nilDegreeProfile W X p) 0)).inv.hom
              ((eqToHom (factorModule_nilDegreeProfile W X p).symm).hom x) ⊗ₜ[ℤ]
            (𝟙 (factorModule d 0) ⊗ₘ
              eqToHom (nilPositiveTailListEq d).symm).hom (y ⊗ₜ[ℤ] t)))) = _
  rw [tensorModuleListAppendIso_singleton_apply]
  simp only [ModuleCat.MonoidalCategory.tensorHom_tmul,
    CategoryTheory.id_apply]
  rw [ModuleCat.MonoidalCategory.associator_inv_apply]
  rw [ModuleCat.MonoidalCategory.tensorHom_tmul]
  have htail := ConcreteCategory.congr_hom
    (eqToIso (nilPositiveTailListEq d)).inv_hom_id t
  simp only [ModuleCat.comp_apply, eqToIso.hom, eqToIso.inv,
    CategoryTheory.id_apply] at htail
  rw [htail]

end AnnihilatingEnrichedFunctorData
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
