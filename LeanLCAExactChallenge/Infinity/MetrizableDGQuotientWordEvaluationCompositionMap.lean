/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientWordEvaluationCompositionRemainder

/-! # Recursive summand composition for corrected Drinfeld word evaluation

This module combines the recursive composition remainder with the append tensor isomorphism.  It
proves that composing a positive-word summand fixes the first factor and recursively composes only
the tail summand.
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

/-- Prefixing a tensor-list map by one module is ordinary left tensoring. -/
theorem tensorModuleListWhiskerLeft_singleton
    (M : ModuleCat.{0} ℤ) {Ms Ns : List (ModuleCat.{0} ℤ)}
    (f : tensorModuleList Ms ⟶ tensorModuleList Ns) :
    tensorModuleListWhiskerLeft [M] f = 𝟙 M ⊗ₘ f := by
  unfold tensorModuleListWhiskerLeft
  simp only [tensorModuleListAppendIso, List.cons_append, List.nil_append,
    id_tensorHom]
  dsimp
  monoidal

/-- The append tensor map for a positive word is its head associator followed by the append
tensor map of the tail. -/
theorem positiveCompositionSourceMap
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    (tensorModuleListAppendIso
        (finFamilyList (factorModule d))
        (finFamilyList (factorModule e))).hom ≫
      eqToHom (congrArg tensorModuleList
        (positiveCompositionSourceListEq d e)) =
    (eqToHom (summandModule_succ d) ⊗ₘ 𝟙 (summandModule e)) ≫
      (α_ (factorModule d 0) (summandModule (tailDegreeProfile d))
        (summandModule e)).hom ≫
      (𝟙 (factorModule d 0) ⊗ₘ
        (tensorModuleListAppendIso
          (finFamilyList (factorModule (tailDegreeProfile d)))
          (finFamilyList (factorModule e))).hom) := by
  rw [← tensorModuleListAppendIso_eqToHom
    (finFamilyList_factorModule_eq_head_tail d) rfl]
  rfl

/-- Canonical target transport from positive composition to the composed recursive tail. -/
def positiveCompositionTargetIso
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    summandModule (d.append e) ≅
      factorModule d 0 ⊗ summandModule ((tailDegreeProfile d).append e) :=
  eqToIso (congrArg tensorModuleList (positiveCompositionTargetListEq d e))

/-- Composition of a positive summand preserves the head and recursively composes its tail. -/
theorem summandCompositionMap_positive_recursive
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    summandCompositionMap d e ≫ (positiveCompositionTargetIso d e).hom =
      (eqToHom (summandModule_succ d) ⊗ₘ 𝟙 (summandModule e)) ≫
        (α_ (factorModule d 0) (summandModule (tailDegreeProfile d))
          (summandModule e)).hom ≫
        (𝟙 (factorModule d 0) ⊗ₘ
          summandCompositionMap (tailDegreeProfile d) e) := by
  rw [summandCompositionMap_eq_normalized,
    normalizedSummandCompositionMap_eq_append_remainder,
    summandCompositionRemainder_positive_recursive]
  unfold positiveCompositionTargetIso
  simp only [eqToIso.hom, Category.assoc]
  slice_lhs 4 5 => rw [eqToHom_trans]
  simp only [eqToHom_refl, Category.comp_id]
  slice_lhs 1 2 => rw [positiveCompositionSourceMap]
  rw [tensorModuleListWhiskerLeft_singleton]
  simp only [Category.assoc]
  slice_lhs 3 4 => rw [← MonoidalCategory.id_tensor_comp]
  rw [← normalizedSummandCompositionMap_eq_append_remainder,
    ← summandCompositionMap_eq_normalized]

end AnnihilatingEnrichedFunctorData
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
