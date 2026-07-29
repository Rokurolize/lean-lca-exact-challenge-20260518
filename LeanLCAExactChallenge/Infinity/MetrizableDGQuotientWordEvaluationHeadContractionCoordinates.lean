/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientWordEvaluationMultiplicativityNilNil

/-! # Head/contraction coordinates for corrected Drinfeld evaluation

This module presents the first ordinary factor of a positive Drinfeld word and the formal
contraction at its first intermediate object in explicit summand coordinates. The direct target
coordinates preserve the head factor and retain the second identity factor of the formal
contraction.
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

/-- The zero-word summand element represented by the first ordinary factor. -/
def positiveHeadSummandElement
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d 0) :
    summandModule
      (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)) :=
  (nilSummandIsoOriginal X (intermediate 0).obj
    (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0))).inv
      ((eqToHom (factorModule_zero_succ d)).hom x)

/-- The degree profile after composing the zero-word head with the formal contraction. -/
abbrev headContractionDegreeProfile
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :=
  (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
    (singletonContractingDegreeProfile (intermediate 0))

/-- The first factor after the head/contraction composition is the original head factor. -/
theorem headContractionFactor_zero
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    factorModule
        ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
          (singletonContractingDegreeProfile (intermediate 0))) 0 =
      factorModule d 0 := by
  let h := nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)
  let c := singletonContractingDegreeProfile (intermediate 0)
  calc
    factorModule (h.append c) 0 =
        factorModule (h.append c) (appendBoundaryArrowIndex (nil X (intermediate 0).obj)
          (singleton (intermediate 0).obj (intermediate 0).obj (intermediate 0))) := by
      congr 2
    _ = compositionBoundaryModule h c := factorModule_append_boundary h c
    _ = (dgHomZModuleCochainComplex X (intermediate 0).obj).X (d.arrowDegree 0) := by
      dsimp [h, c]
      unfold compositionBoundaryModule
      have hs :
          (nil X (intermediate 0).obj).arrowSource
            (Fin.last (nil X (intermediate 0).obj).length) = X := by
        rw [show Fin.last (nil X (intermediate 0).obj).length = 0 by
          apply Fin.ext
          rfl]
        exact nil_arrowSource_zero X (intermediate 0).obj
      have ht :
          (singleton (intermediate 0).obj (intermediate 0).obj
            (intermediate 0)).arrowTarget 0 = (intermediate 0).obj := by
        rfl
      rw [hs, ht]
      have hp :
          (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).arrowDegree
              (Fin.last (nil X (intermediate 0).obj).length) = d.arrowDegree 0 := by
        rfl
      have hc :
          (singletonContractingDegreeProfile (intermediate 0)).arrowDegree 0 = 0 := by
        rfl
      rw [hp, hc, Int.add_zero]
    _ = factorModule d 0 := (factorModule_zero_succ d).symm

/-- The second factor after the head/contraction composition is the remaining identity factor. -/
theorem headContractionFactor_one
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    factorModule
        ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
          (singletonContractingDegreeProfile (intermediate 0))) 1 =
      (dgHomZModuleCochainComplex (intermediate 0).obj (intermediate 0).obj).X 0 := by
  change factorModule (singletonContractingDegreeProfile (intermediate 0)) 1 = _
  rfl

/-- The head/contraction output has exactly the remaining identity as its suffix. -/
theorem headContractionRightSuffix
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    compositionRightSuffix
        ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
          (singletonContractingDegreeProfile (intermediate 0))) =
      [factorModule
        ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
          (singletonContractingDegreeProfile (intermediate 0))) 1] := by
  rfl

/-- The first factor of the formal contraction is the degree-zero endomorphism module. -/
theorem singletonContractingFactor_zero
    (A : CorrectedAcyclicComplexCategory) :
    factorModule (singletonContractingDegreeProfile A) 0 =
      (dgHomZModuleCochainComplex A.obj A.obj).X 0 := by
  rfl

/-- The identity cochain as an element map into the first singleton factor. -/
def singletonContractingFirstIdentityMap
    (A : CorrectedAcyclicComplexCategory) :
    𝟙_ (ModuleCat.{0} ℤ) ⟶ factorModule (singletonContractingDegreeProfile A) 0 :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _
    ((eqToHom (singletonContractingFactor_zero A).symm).hom (identityCochain A.obj)))

/-- The first singleton identity map evaluates to the identity cochain at one. -/
theorem singletonContractingFirstIdentityMap_apply_one
    (A : CorrectedAcyclicComplexCategory) :
    (singletonContractingFirstIdentityMap A).hom 1 =
      (eqToHom (singletonContractingFactor_zero A).symm).hom
        (identityCochain A.obj) := by
  unfold singletonContractingFirstIdentityMap
  exact LinearMap.toSpanSingleton_apply_one ℤ _ _

/-- The singleton contraction has exactly its second factor as right suffix. -/
@[simp]
theorem compositionRightSuffix_singletonContracting
    (A : CorrectedAcyclicComplexCategory) :
    compositionRightSuffix (singletonContractingDegreeProfile A) =
      [factorModule (singletonContractingDegreeProfile A) 1] := by
  rfl

/-- The second factor of the formal contraction is the degree-zero endomorphism module. -/
theorem singletonContractingFactor_one
    (A : CorrectedAcyclicComplexCategory) :
    factorModule (singletonContractingDegreeProfile A) 1 =
      (dgHomZModuleCochainComplex A.obj A.obj).X 0 := by
  rfl

/-- In first-factor coordinates, the formal contraction is the two identity factors
with the terminal tensor unit retained. -/
theorem singletonFirstFactorIso_contractingElement
    (A : CorrectedAcyclicComplexCategory) :
    (summandFirstFactorIso (singletonContractingDegreeProfile A)).hom
        (singletonContractingElement A) =
      (eqToHom (singletonContractingFactor_zero A).symm).hom
          (identityCochain A.obj) ⊗ₜ[ℤ]
        (ρ_ (factorModule (singletonContractingDegreeProfile A) 1)).inv.hom
          ((eqToHom (singletonContractingFactor_one A).symm).hom
            (identityCochain A.obj)) := by
  let c := singletonContractingDegreeProfile A
  have hlist : finFamilyList (factorModule c) =
      factorModule c 0 :: compositionRightSuffix c := rfl
  have hfirst : (summandFirstFactorIso c).hom =
      eqToHom (congrArg tensorModuleList hlist) := by
    unfold summandFirstFactorIso
    congr 1
  rw [hfirst]
  have hlistProof : hlist = rfl := Subsingleton.elim _ _
  rw [hlistProof]
  simp only [eqToHom_refl]
  unfold singletonContractingElement singletonSummandIsoTensor
  simp only [ModuleCat.MonoidalCategory.rightUnitor_inv_apply]
  rfl

/-- The identity factor left after composing the head with the formal contraction. -/
def headContractionIdentityTail
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    tensorModuleList (compositionRightSuffix
      ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
        (singletonContractingDegreeProfile (intermediate 0)))) :=
  (eqToHom (congrArg tensorModuleList (headContractionRightSuffix d).symm)).hom
    ((ρ_ (factorModule
      ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
        (singletonContractingDegreeProfile (intermediate 0))) 1)).inv.hom
      ((eqToHom (headContractionFactor_one d).symm).hom
        (identityCochain (intermediate 0).obj)))

/-- The explicit head/tail tensor agrees with the right-associated intermediate
coordinate object. -/
def headFirstCoordinateEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    factorModule
        ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
          (singletonContractingDegreeProfile (intermediate 0))) 0 ⊗
        tensorModuleList (compositionRightSuffix
          ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
            (singletonContractingDegreeProfile (intermediate 0)))) =
      tensorModuleList
        (factorModule
            ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
              (singletonContractingDegreeProfile (intermediate 0))) 0 ::
          compositionRightSuffix
            ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
              (singletonContractingDegreeProfile (intermediate 0)))) :=
  rfl

/-- The direct head-with-remaining-identity presentation of the intermediate summand. -/
def headContractionDirectSummand
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d 0) :
    summandModule
      ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
        (singletonContractingDegreeProfile (intermediate 0))) :=
  (summandFirstFactorIso
      ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
        (singletonContractingDegreeProfile (intermediate 0)))).inv
    ((eqToHom (headFirstCoordinateEq d)).hom
      ((eqToHom (headContractionFactor_zero d).symm).hom x ⊗ₜ[ℤ]
        headContractionIdentityTail d))

/-- The first factor as a map into the zero-word summand. -/
def positiveHeadSummandMap
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    factorModule d 0 ⟶
      summandModule (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)) :=
  eqToHom (factorModule_zero_succ d) ≫
    (nilSummandIsoOriginal X (intermediate 0).obj
      (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0))).inv

/-- The formal contraction in binary tensor coordinates. -/
def singletonContractingBinaryCoordinates (A : CorrectedAcyclicComplexCategory) :=
  (singletonSummandIsoTensor A.obj A.obj A
    (singletonContractingDegreeProfile A)).hom (singletonContractingElement A)

/-- The binary coordinate is the pair of identity cochains. -/
theorem singletonContractingBinaryCoordinates_eq
    (A : CorrectedAcyclicComplexCategory) :
    singletonContractingBinaryCoordinates A =
      identityCochain A.obj ⊗ₜ[ℤ] identityCochain A.obj := by
  unfold singletonContractingBinaryCoordinates
  exact singletonSummandIsoTensorAt_contractingElement A

/-- The span map selecting the formal contraction in binary coordinates. -/
def singletonContractingBinaryMap (A : CorrectedAcyclicComplexCategory) :
    𝟙_ (ModuleCat.{0} ℤ) ⟶
      factorModule (singletonContractingDegreeProfile A) 0 ⊗
        factorModule (singletonContractingDegreeProfile A) 1 :=
  ModuleCat.ofHom
    (LinearMap.toSpanSingleton ℤ _ (singletonContractingBinaryCoordinates A))

/-- The formal contraction as a map out of the tensor unit. -/
def singletonContractingElementMap (A : CorrectedAcyclicComplexCategory) :
    𝟙_ (ModuleCat.{0} ℤ) ⟶ summandModule (singletonContractingDegreeProfile A) :=
  singletonContractingBinaryMap A ≫
    (singletonSummandIsoTensor A.obj A.obj A
      (singletonContractingDegreeProfile A)).inv

/-- The binary-coordinate construction evaluates to the actual formal contraction at one. -/
theorem singletonContractingElementMap_apply_one
    (A : CorrectedAcyclicComplexCategory) :
    (singletonContractingElementMap A).hom 1 = singletonContractingElement A := by
  unfold singletonContractingElementMap singletonContractingBinaryMap
  change (singletonSummandIsoTensor A.obj A.obj A
      (singletonContractingDegreeProfile A)).inv.hom
      ((LinearMap.toSpanSingleton ℤ _ (singletonContractingBinaryCoordinates A)) 1) =
    singletonContractingElement A
  rw [LinearMap.toSpanSingleton_apply_one]
  unfold singletonContractingBinaryCoordinates
  exact (singletonSummandIsoTensor A.obj A.obj A
    (singletonContractingDegreeProfile A)).hom_inv_id_apply _

/-- The formal contraction's remaining identity factor as a map from the tensor unit. -/
def singletonContractingTailMap (A : CorrectedAcyclicComplexCategory) :
    𝟙_ (ModuleCat.{0} ℤ) ⟶
      tensorModuleList (compositionRightSuffix (singletonContractingDegreeProfile A)) :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _
    ((ρ_ (factorModule (singletonContractingDegreeProfile A) 1)).inv.hom
      ((eqToHom (singletonContractingFactor_one A).symm).hom (identityCochain A.obj))))

/-- The singleton tail identity map evaluates to its chosen coordinate at one. -/
theorem singletonContractingTailMap_apply_one
    (A : CorrectedAcyclicComplexCategory) :
    (singletonContractingTailMap A).hom 1 =
      (ρ_ (factorModule (singletonContractingDegreeProfile A) 1)).inv.hom
        ((eqToHom (singletonContractingFactor_one A).symm).hom
          (identityCochain A.obj)) := by
  unfold singletonContractingTailMap
  exact LinearMap.toSpanSingleton_apply_one ℤ _ _

/-- The remaining identity factor as a map out of the tensor unit. -/
def headContractionIdentityTailMap
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    𝟙_ (ModuleCat.{0} ℤ) ⟶ tensorModuleList (compositionRightSuffix
      ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
        (singletonContractingDegreeProfile (intermediate 0)))) :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (headContractionIdentityTail d))

@[simp]
theorem headContractionIdentityTailMap_apply_one
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    (headContractionIdentityTailMap d).hom 1 = headContractionIdentityTail d := by
  unfold headContractionIdentityTailMap
  exact LinearMap.toSpanSingleton_apply_one ℤ _ _

/-- Transporting the singleton tail through a zero-word append gives the output identity tail. -/
theorem singletonContractingTailMap_to_headTail
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    singletonContractingTailMap (intermediate 0) ≫
        eqToHom (congrArg tensorModuleList
          (compositionRightSuffix_zero_append_eq
            (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0))
            (singletonContractingDegreeProfile (intermediate 0))).symm) =
      headContractionIdentityTailMap d := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change (eqToHom (congrArg tensorModuleList
      (compositionRightSuffix_zero_append_eq
        (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0))
        (singletonContractingDegreeProfile (intermediate 0))).symm)).hom
      ((singletonContractingTailMap (intermediate 0)).hom 1) =
    (headContractionIdentityTailMap d).hom 1
  rw [singletonContractingTailMap_apply_one]
  change _ = (LinearMap.toSpanSingleton ℤ _ (headContractionIdentityTail d)) 1
  rw [LinearMap.toSpanSingleton_apply_one]
  unfold headContractionIdentityTail
  congr 1

/-- The explicit tensor object agrees with the right-associated singleton coordinate object. -/
def singletonFirstCoordinateEq (A : CorrectedAcyclicComplexCategory) :
    factorModule (singletonContractingDegreeProfile A) 0 ⊗
        tensorModuleList (compositionRightSuffix (singletonContractingDegreeProfile A)) =
      tensorModuleList
        (factorModule (singletonContractingDegreeProfile A) 0 ::
          compositionRightSuffix (singletonContractingDegreeProfile A)) :=
  rfl

/-- In first-factor coordinates, the formal contraction map is the tensor of its two identity
maps. -/
theorem singletonContractingElementMap_comp_firstFactorIso
    (A : CorrectedAcyclicComplexCategory) :
    singletonContractingElementMap A ≫
        (summandFirstFactorIso (singletonContractingDegreeProfile A)).hom =
      (λ_ (𝟙_ (ModuleCat.{0} ℤ))).inv ≫
        (singletonContractingFirstIdentityMap A ⊗ₘ singletonContractingTailMap A) ≫
        eqToHom (singletonFirstCoordinateEq A) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change (summandFirstFactorIso (singletonContractingDegreeProfile A)).hom.hom
      ((singletonContractingElementMap A).hom 1) = _
  rw [singletonContractingElementMap_apply_one]
  change (summandFirstFactorIso (singletonContractingDegreeProfile A)).hom.hom
      (singletonContractingElement A) =
    (eqToHom (singletonFirstCoordinateEq A)).hom
      ((singletonContractingFirstIdentityMap A ⊗ₘ
        singletonContractingTailMap A).hom
        ((λ_ (𝟙_ (ModuleCat.{0} ℤ))).inv.hom 1))
  rw [ModuleCat.MonoidalCategory.leftUnitor_inv_apply]
  rw [ModuleCat.MonoidalCategory.tensorHom_tmul,
    singletonContractingFirstIdentityMap_apply_one,
    singletonContractingTailMap_apply_one]
  rw [singletonFirstFactorIso_contractingElement]
  unfold singletonFirstCoordinateEq
  rfl

/-- The zero-word head map in its unique last-factor coordinates. -/
theorem positiveHeadSummandMap_comp_lastFactorIso
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    positiveHeadSummandMap d ≫
        (summandLastFactorIso
          (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0))).hom =
      eqToHom (factorModule_zero_succ d) ≫
        (ρ_ (factorModule
          (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)) 0)).inv := by
  unfold positiveHeadSummandMap
  simp only [Category.assoc]
  rw [nilSummandIsoOriginal_inv_comp_lastFactorIso_hom]

/-- The input map for composing the head with the formal contraction. -/
def headContractionInputMap
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    factorModule d 0 ⟶
      summandModule (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)) ⊗
        summandModule (singletonContractingDegreeProfile (intermediate 0)) :=
  (ρ_ (factorModule d 0)).inv ≫
    (positiveHeadSummandMap d ⊗ₘ singletonContractingElementMap (intermediate 0))

/-- The direct map whose value is the head factor followed by the remaining identity. -/
def headContractionDirectMap
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    factorModule d 0 ⟶ summandModule
      ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
        (singletonContractingDegreeProfile (intermediate 0))) :=
  (ρ_ (factorModule d 0)).inv ≫
    (eqToHom (headContractionFactor_zero d).symm ⊗ₘ
      headContractionIdentityTailMap d) ≫
    eqToHom (headFirstCoordinateEq d) ≫
    (summandFirstFactorIso
      ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
        (singletonContractingDegreeProfile (intermediate 0)))).inv

end AnnihilatingEnrichedFunctorData
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
