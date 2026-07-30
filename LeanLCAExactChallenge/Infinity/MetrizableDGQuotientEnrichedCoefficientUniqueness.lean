/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientEnrichedPositiveUniqueness
import Mathlib.Algebra.Category.ModuleCat.Products

/-! # Coefficient-level uniqueness for the corrected Drinfeld quotient -/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory
open CategoryTheory.Limits

namespace EnrichedFunctor

variable {D : Type*} [EnrichedCategory QuotientDGCochain D]

/-- Graded coproduct evaluation after restriction is the original quotient-enriched Hom map on
the underlying integer module. -/
theorem restriction_evaluateGradedValue
    (G : EnrichedFunctor QuotientDGCochain CorrectedQuotientDGCategory D)
    (X Y : ComplexCategory) (n : ℤ) (z : quotientGradedModule X Y n) :
    (AnnihilatingEnrichedFunctorData.restriction G).evaluateGradedValue X Y n z =
      (G.map (Opposite.op Y) (Opposite.op X)).f n (ULift.up z) := by
  classical
  let Z : GradedSummandIndex X Y n → ModuleCat.{1} ℤ :=
    fun s ↦ largeSummandModule s
  let e := ModuleCat.coprodIsoDirectSum.{0, 1, 1} Z
  let u := e.hom.hom z
  have hz : e.inv.hom u = z := by
    have h := ConcreteCategory.congr_hom e.hom_inv_id z
    dsimp only [u]
    simpa only [ModuleCat.comp_apply, CategoryTheory.id_apply] using h
  rw [← hz]
  change
    (AnnihilatingEnrichedFunctorData.restriction G).evaluateGradedValue X Y n
        (e.inv.hom u) =
      (G.map (Opposite.op Y) (Opposite.op X)).f n (ULift.up (e.inv.hom u))
  induction u using DirectSum.induction_on with
  | zero =>
      change
        (AnnihilatingEnrichedFunctorData.restriction G).evaluateGradedModule X Y n 0 =
          (G.map (Opposite.op Y) (Opposite.op X)).f n (ULift.up 0)
      have hup : (ULift.up (0 : quotientGradedModule X Y n) :
          quotientCoefficientModule (quotientGradedModule X Y n)) = 0 := by
        apply ULift.down_injective
        rfl
      rw [map_zero]
      have hzero := congrArg
        (fun y ↦ (G.map (Opposite.op Y) (Opposite.op X)).f n y) hup
      exact (hzero.trans (map_zero _)).symm
  | of s x =>
      rcases s with ⟨w, d⟩
      have hlof := ConcreteCategory.congr_hom
        (ModuleCat.lof_coprodIsoDirectSum_inv.{0, 1, 1} Z ⟨w, d⟩) x
      simp only [ModuleCat.comp_apply] at hlof
      have hinv : e.inv.hom
          (DirectSum.of (fun i ↦ Z i) ⟨w, d⟩ x) =
          (Limits.Sigma.ι Z ⟨w, d⟩).hom x := by
        rw [← DirectSum.lof_eq_of ℤ]
        exact hlof
      rw [hinv]
      dsimp only [Z] at x
      rcases x with ⟨x⟩
      rw [AnnihilatingEnrichedFunctorData.evaluateGradedValue_inclusion]
      exact restriction_evaluateWord G d x
  | add a b ha hb =>
      simp only [map_add]
      rw [AnnihilatingEnrichedFunctorData.evaluateGradedValue_add]
      have hup : (ULift.up (e.inv.hom a + e.inv.hom b) :
          quotientCoefficientModule (quotientGradedModule X Y n)) =
          ULift.up (e.inv.hom a) + ULift.up (e.inv.hom b) := rfl
      have hG := congrArg
        (fun y ↦ (G.map (Opposite.op Y) (Opposite.op X)).f n y) hup
      have hmap := ((G.map (Opposite.op Y) (Opposite.op X)).f n).hom.map_add
        (ULift.up (e.inv.hom a)) (ULift.up (e.inv.hom b))
      exact (congrArg₂ (· + ·) ha hb).trans (hG.trans hmap).symm

/-- Coefficient-changed evaluation after restriction is the original quotient-enriched Hom map
in every degree. -/
theorem restriction_evaluateCoefficientDegree
    (G : EnrichedFunctor QuotientDGCochain CorrectedQuotientDGCategory D)
    (X Y : ComplexCategory) (n : ℤ) :
    (AnnihilatingEnrichedFunctorData.restriction G).evaluateCoefficientDegree X Y n =
      (G.map (Opposite.op Y) (Opposite.op X)).f n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rcases x with ⟨x⟩
  rw [AnnihilatingEnrichedFunctorData.evaluateCoefficientDegree_apply_up]
  exact restriction_evaluateGradedValue G X Y n x

/-- The cochain evaluator built from a restricted quotient functor is its original Hom map. -/
theorem restriction_evaluateCochainMap
    (G : EnrichedFunctor QuotientDGCochain CorrectedQuotientDGCategory D)
    (X Y : ComplexCategory) :
    (AnnihilatingEnrichedFunctorData.restriction G).evaluateCochainMap X Y =
      G.map (Opposite.op Y) (Opposite.op X) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact restriction_evaluateCoefficientDegree G X Y n

/-- Enriched extension after restriction is the original quotient-enriched functor. -/
theorem enrichedExtension_restriction
    (G : EnrichedFunctor QuotientDGCochain CorrectedQuotientDGCategory D) :
    (AnnihilatingEnrichedFunctorData.restriction G).enrichedExtension = G := by
  apply CategoryTheory.EnrichedFunctor.ext
    (F := (AnnihilatingEnrichedFunctorData.restriction G).enrichedExtension)
    (G := G) QuotientDGCochain (fun _ ↦ rfl)
  intro K L
  change (AnnihilatingEnrichedFunctorData.restriction G).evaluateCochainMap
      L.unop K.unop = G.map K L
  exact restriction_evaluateCochainMap G L.unop K.unop

/-- The corrected Drinfeld quotient has the functor-level universal property for annihilating
enriched-functor data. -/
def annihilatingDataEquivEnrichedFunctor :
    AnnihilatingEnrichedFunctorData D ≃
      EnrichedFunctor QuotientDGCochain CorrectedQuotientDGCategory D where
  toFun E := E.enrichedExtension
  invFun G := AnnihilatingEnrichedFunctorData.restriction G
  left_inv E := E.restriction_enrichedExtension
  right_inv G := enrichedExtension_restriction G

end EnrichedFunctor

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
