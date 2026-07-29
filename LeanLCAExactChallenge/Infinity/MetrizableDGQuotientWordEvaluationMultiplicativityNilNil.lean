/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientWordEvaluationMultiplicativityInduction
import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientInclusionFunctor

/-! # Zero-word multiplicativity for corrected Drinfeld evaluation

This module proves multiplicativity of corrected Drinfeld word evaluation when both words have
length zero.  It relates direct dependent transport of the composed summand to the explicit
zero-word composition coordinates, applies preservation of original DG composition, and then
returns the result to the original append degree.
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

/-- Transporting the composition profile of two zero-length words gives the canonical profile
in the target composition degree. -/
theorem nilCompositionTransportProfileEq
    (X Y Z : ComplexCategory) (n m : ℤ) :
    ((nilDegreeProfile X Y n).append (nilDegreeProfile Y Z m)).transport
        (nil_append_nil X Y Z) (Int.add_comm n m) =
      nilDegreeProfile X Z (m + n) :=
  degreeProfile_nil_eq_nilDegreeProfile X Z (m + n) _

/-- The direct transport used by zero-word composition agrees with word/profile transport. -/
theorem nilCompositionTransportIso_eq
    (X Y Z : ComplexCategory) (n m : ℤ) :
    nilCompositionTransportIso X Y Z n m =
      summandModuleTransportIso (nil_append_nil X Y Z) (Int.add_comm n m)
          ((nilDegreeProfile X Y n).append (nilDegreeProfile Y Z m)) ≪≫
        eqToIso (congrArg summandModule
          (nilCompositionTransportProfileEq X Y Z n m)) := by
  rfl

/-- Evaluation of a composed zero-word summand after its canonical output transport is ordinary
zero-word evaluation. -/
theorem evaluateWord_nil_nil_transport
    (X Y Z : ComplexCategory) (n m : ℤ)
    (u : summandModule
      ((nilDegreeProfile X Y n).append (nilDegreeProfile Y Z m))) :
    (eqToHom (congrArg (fun q ↦ (E.hom X Z).X q)
      (Int.add_comm n m))).hom
        (E.evaluateWord ((nil X Y).append (nil Y Z))
          ((nilDegreeProfile X Y n).append (nilDegreeProfile Y Z m)) u) =
      E.factorMap X Z (m + n)
        ((nilSummandIsoOriginal X Z (nilDegreeProfile X Z (m + n))).hom.hom
          ((nilCompositionTransportIso X Y Z n m).hom.hom u)) := by
  let d := (nilDegreeProfile X Y n).append (nilDegreeProfile Y Z m)
  let hw := nil_append_nil X Y Z
  let hn := Int.add_comm n m
  let hp := nilCompositionTransportProfileEq X Y Z n m
  have htransport := E.evaluateWord_transport_apply hw hn d u
  have hprofile := E.evaluateWord_profile_eq_apply hp
    ((eqToHom (summandModuleTransportEq hw hn d)).hom u)
  have hresult := hprofile.trans htransport
  rw [E.evaluateWord_nil_apply] at hresult
  unfold evaluateNilProfile at hresult
  have hiso := congrArg Iso.hom (nilCompositionTransportIso_eq X Y Z n m)
  have hinput := ConcreteCategory.congr_hom hiso u
  simp only [Iso.trans_hom, ModuleCat.comp_apply, summandModuleTransportIso,
    eqToIso.hom] at hinput
  rw [← hinput] at hresult
  simp only [LinearMap.comp_apply] at hresult
  exact hresult.symm

/-- Corrected word evaluation is multiplicative when both source words have length zero, after
transporting the output to the target composition degree. -/
theorem evaluateWord_multiplicative_nil_nil_transport
    (X Y Z : ComplexCategory) (n m : ℤ)
    (x : (dgHomZModuleCochainComplex X Y).X n)
    (y : (dgHomZModuleCochainComplex Y Z).X m) :
    (eqToHom (congrArg (fun q ↦ (E.hom X Z).X q)
      (Int.add_comm n m))).hom
        (E.evaluateWord ((nil X Y).append (nil Y Z))
          ((nilDegreeProfile X Y n).append (nilDegreeProfile Y Z m))
          ((summandCompositionMap
            (nilDegreeProfile X Y n) (nilDegreeProfile Y Z m)).hom
            ((nilSummandIsoOriginal X Y (nilDegreeProfile X Y n)).inv.hom x ⊗ₜ[ℤ]
              (nilSummandIsoOriginal Y Z (nilDegreeProfile Y Z m)).inv.hom y))) =
      E.composeElement X Y Z n m (m + n) rfl
        (E.factorMap X Y n x) (E.factorMap Y Z m y) := by
  let d := nilDegreeProfile X Y n
  let e := nilDegreeProfile Y Z m
  let sx := (ConcreteCategory.hom (nilSummandIsoOriginal X Y d).inv) x
  let sy := (ConcreteCategory.hom (nilSummandIsoOriginal Y Z e).inv) y
  let u := (ConcreteCategory.hom (summandCompositionMap d e)) (sx ⊗ₜ[ℤ] sy)
  rw [E.evaluateWord_nil_nil_transport X Y Z n m u]
  have htransport := ConcreteCategory.congr_hom
    (nilCompositionTransportIso_to_boundary X Y Z n m) u
  simp only [ModuleCat.comp_apply] at htransport
  have hcomposition := ConcreteCategory.congr_hom
    (summandCompositionMap_nil_nil X Y Z n m) (x ⊗ₜ[ℤ] y)
  simp only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.tensorHom_tmul] at hcomposition
  dsimp only [u, sx, sy, d, e] at htransport
  rw [hcomposition] at htransport
  have hcast := dgCochainCompTensor_cast_tmul X Y Z rfl
    (Int.add_comm n m) (Int.add_comm n m) x y
  have horiginal := htransport.trans hcast
  rw [horiginal]
  exact E.factorMap_compose X Y Z n m (m + n) (Int.add_comm n m) x y

/-- Corrected word evaluation is multiplicative on two zero-length words in the original append
degree. -/
theorem evaluateWord_multiplicative_nil_nil
    (X Y Z : ComplexCategory) (n m : ℤ)
    (x : (dgHomZModuleCochainComplex X Y).X n)
    (y : (dgHomZModuleCochainComplex Y Z).X m) :
    E.evaluateWord ((nil X Y).append (nil Y Z))
        ((nilDegreeProfile X Y n).append (nilDegreeProfile Y Z m))
        ((summandCompositionMap
          (nilDegreeProfile X Y n) (nilDegreeProfile Y Z m)).hom
          ((nilSummandIsoOriginal X Y (nilDegreeProfile X Y n)).inv.hom x ⊗ₜ[ℤ]
            (nilSummandIsoOriginal Y Z (nilDegreeProfile Y Z m)).inv.hom y)) =
      E.composeElement X Y Z n m (n + m)
        (wordEvaluationCompositionDegreeEq n m)
        (E.factorMap X Y n x) (E.factorMap Y Z m y) := by
  let hout := congrArg (fun q ↦ (E.hom X Z).X q) (Int.add_comm n m)
  apply (ModuleCat.mono_iff_injective (eqToIso hout).hom).1 inferInstance
  have hleft := E.evaluateWord_multiplicative_nil_nil_transport X Y Z n m x y
  have hright := E.composeElement_cast_output X Y Z n m (n + m) (m + n)
    (wordEvaluationCompositionDegreeEq n m) (Int.add_comm n m)
    (E.factorMap X Y n x) (E.factorMap Y Z m y)
  exact hleft.trans hright.symm

end AnnihilatingEnrichedFunctorData
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
