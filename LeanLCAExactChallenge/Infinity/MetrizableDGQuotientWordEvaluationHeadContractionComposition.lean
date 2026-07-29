/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientWordEvaluationHeadContractionCoordinates

/-! # Head/contraction summand composition for corrected Drinfeld evaluation

This module compares the explicit head/formal-contraction coordinates with the actual quotient
summand composition map. The boundary composition is a right unit, so the original head factor
survives while the formal contraction's second identity factor remains as the suffix.
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

/-- The nil/singleton boundary module normalized to the nil factor. -/
theorem headZeroBoundaryModule_eq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    zeroMiddleRightBoundaryModule
        (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0))
        (singletonContractingDegreeProfile (intermediate 0)) =
      factorModule (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)) 0 := by
  unfold zeroMiddleRightBoundaryModule factorModule
  change (dgHomZModuleCochainComplex X (intermediate 0).obj).X
      (d.arrowDegree 0 + 0) =
    (dgHomZModuleCochainComplex X (intermediate 0).obj).X (d.arrowDegree 0)
  rw [Int.add_zero]

/-- The nil/singleton boundary map with normalized codomain. -/
def headZeroBoundaryMap
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    factorModule (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)) 0 ⊗
        factorModule (singletonContractingDegreeProfile (intermediate 0)) 0 ⟶
      factorModule (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)) 0 :=
  zeroMiddleRightBoundaryMap
      (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0))
      (singletonContractingDegreeProfile (intermediate 0)) ≫
    eqToHom (headZeroBoundaryModule_eq d)

/-- The actual composition boundary module normalized to the nil factor. -/
theorem headActualBoundaryModule_eq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    compositionBoundaryModule
        (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0))
        (singletonContractingDegreeProfile (intermediate 0)) =
      factorModule (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)) 0 :=
  (zeroMiddleRightBoundaryModule_eq
      (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0))
      (singletonContractingDegreeProfile (intermediate 0))).symm.trans
    (headZeroBoundaryModule_eq d)

/-- Explicit object equalities turn heterogeneous morphism equality into equality after
transport. -/
theorem hom_eq_transport_of_heq
    {C : Type*} [Category C]
    {X X' Y Y' : C} (hX : X = X') (hY : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) :
    f = eqToHom hX ≫ g ≫ eqToHom hY.symm := by
  subst X'
  subst Y'
  simpa using eq_of_heq h

/-- A transported equality of morphisms yields the corresponding heterogeneous equality. -/
theorem hom_heq_of_eq_transport
    {C : Type*} [Category C]
    {X X' Y Y' : C} (hX : X = X') (hY : Y = Y')
    (f : X ⟶ Y) (g : X' ⟶ Y')
    (h : f = eqToHom hX ≫ g ≫ eqToHom hY.symm) : HEq f g := by
  subst X'
  subst Y'
  simpa using heq_of_eq h

/-- The actual boundary source transported from the nil-specialized source. -/
theorem headActualBoundarySource_eq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    factorModule (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)) 0 ⊗
        factorModule (singletonContractingDegreeProfile (intermediate 0)) 0 =
      factorModule (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0))
          (Fin.last (nil X (intermediate 0).obj).length) ⊗
        factorModule (singletonContractingDegreeProfile (intermediate 0)) 0 := by
  congr 1

/-- The actual boundary map equals the nil-specialized map after source and target transport. -/
theorem headActualBoundaryMap_eq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    headZeroBoundaryMap d =
      eqToHom (headActualBoundarySource_eq d) ≫
        compositionBoundaryMap
          (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0))
          (singletonContractingDegreeProfile (intermediate 0)) ≫
        eqToHom (headActualBoundaryModule_eq d) := by
  let h := nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)
  let c := singletonContractingDegreeProfile (intermediate 0)
  let hm := zeroMiddleRightBoundaryModule_eq h c
  have hmap := hom_eq_transport_of_heq
    (headActualBoundarySource_eq d) hm
    (zeroMiddleRightBoundaryMap_heq h c)
  unfold headZeroBoundaryMap
  dsimp only [h, c, hm] at hmap
  rw [hmap]
  simp only [Category.assoc, eqToHom_trans]

/-- The normalized nil/singleton boundary map is a right unit. -/
theorem headZeroBoundaryMap_unit
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    (ρ_ (factorModule
      (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)) 0)).inv ≫
        (𝟙 _ ⊗ₘ singletonContractingFirstIdentityMap (intermediate 0)) ≫
        headZeroBoundaryMap d =
      𝟙 (factorModule
        (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)) 0) := by
  unfold headZeroBoundaryMap singletonContractingFirstIdentityMap
    zeroMiddleRightBoundaryMap
  convert dgCochainCompTensorOfEq_right_unit_raw
    X (intermediate 0).obj (intermediate 0).obj rfl (d.arrowDegree 0) using 1 <;> rfl

/-- The actual nil/singleton boundary map, including its source and target transports, is a
right unit. -/
theorem headActualBoundaryMap_unit
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    (ρ_ (factorModule
      (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)) 0)).inv ≫
        (𝟙 _ ⊗ₘ singletonContractingFirstIdentityMap (intermediate 0)) ≫
        eqToHom (headActualBoundarySource_eq d) ≫
        compositionBoundaryMap
          (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0))
          (singletonContractingDegreeProfile (intermediate 0)) ≫
        eqToHom (headActualBoundaryModule_eq d) =
      𝟙 (factorModule
        (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)) 0) := by
  calc
    _ = (ρ_ (factorModule
          (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)) 0)).inv ≫
        (𝟙 _ ⊗ₘ singletonContractingFirstIdentityMap (intermediate 0)) ≫
        headZeroBoundaryMap d := by
          rw [headActualBoundaryMap_eq]
    _ = _ := headZeroBoundaryMap_unit d

/-- A right unit can be eliminated while retaining an arbitrary tensor tail. -/
theorem rightUnit_with_tail
    {M N T : ModuleCat.{0} ℤ}
    (u : 𝟙_ (ModuleCat.{0} ℤ) ⟶ N)
    (t : 𝟙_ (ModuleCat.{0} ℤ) ⟶ T)
    (f : M ⊗ N ⟶ M)
    (hunit : (ρ_ M).inv ≫ (𝟙 M ⊗ₘ u) ≫ f = 𝟙 M) :
    (ρ_ M).inv ≫
        (𝟙 M ⊗ₘ ((λ_ (𝟙_ (ModuleCat.{0} ℤ))).inv ≫ (u ⊗ₘ t))) ≫
        (α_ M N T).inv ≫ (f ⊗ₘ 𝟙 T) =
      (ρ_ M).inv ≫ (𝟙 M ⊗ₘ t) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hx := ConcreteCategory.congr_hom hunit x
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul,
    ModuleCat.MonoidalCategory.associator_inv_apply,
    CategoryTheory.id_apply] at hx ⊢
  rw [ModuleCat.MonoidalCategory.tensorHom_tmul, hx, CategoryTheory.id_apply]

/-- A right-unit adjacent merge remains an identity after adjoining an arbitrary suffix. -/
theorem adjacentMergeAfter_tensorMap_right_unit_suffix
    (xs ys : List (ModuleCat.{0} ℤ)) {M N : ModuleCat.{0} ℤ}
    (u : 𝟙_ (ModuleCat.{0} ℤ) ⟶ N) (f : M ⊗ N ⟶ M)
    (hunit : (ρ_ M).inv ≫ (𝟙 M ⊗ₘ u) ≫ f = 𝟙 M) :
    tensorModuleListWhiskerRight ys
      ((ρ_ (tensorModuleList (xs ++ [M]))).inv ≫
        (𝟙 (tensorModuleList (xs ++ [M])) ⊗ₘ (u ≫ (ρ_ N).inv)) ≫
        (tensorModuleListAppendIso (xs ++ [M]) [N]).hom ≫
        eqToHom (congrArg tensorModuleList (appendSingletonPairEq xs M N)) ≫
        (adjacentMergeAfter xs (ys := []) f).tensorMap) =
      𝟙 (tensorModuleList ((xs ++ [M]) ++ ys)) := by
  rw [adjacentMergeAfter_tensorMap_right_unit xs u f hunit]
  simp [tensorModuleListWhiskerRight]

/-- The head/contraction input in last/first-factor coordinates. -/
theorem headContractionSource_decompose
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    (ρ_ (factorModule d 0)).inv ≫
        (positiveHeadSummandMap d ⊗ₘ
          singletonContractingElementMap (intermediate 0)) ≫
        ((summandLastFactorIso
          (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0))).hom ⊗ₘ
          (summandFirstFactorIso
            (singletonContractingDegreeProfile (intermediate 0))).hom) =
      (ρ_ (factorModule d 0)).inv ≫
        ((eqToHom (factorModule_zero_succ d) ≫
            (ρ_ (factorModule
              (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)) 0)).inv) ⊗ₘ
          ((λ_ (𝟙_ (ModuleCat.{0} ℤ))).inv ≫
            (singletonContractingFirstIdentityMap (intermediate 0) ⊗ₘ
              singletonContractingTailMap (intermediate 0)) ≫
            eqToHom (singletonFirstCoordinateEq (intermediate 0)))) := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom,
    positiveHeadSummandMap_comp_lastFactorIso,
    singletonContractingElementMap_comp_firstFactorIso]

/-- The merged nil/singleton factor list is the output first/suffix list. -/
def headContractionTargetListEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    compositionLeftPrefix
        (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)) ++
      compositionBoundaryModule
          (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0))
          (singletonContractingDegreeProfile (intermediate 0)) ::
        compositionRightSuffix (singletonContractingDegreeProfile (intermediate 0)) =
      factorModule
          ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
            (singletonContractingDegreeProfile (intermediate 0))) 0 ::
        compositionRightSuffix
          ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
            (singletonContractingDegreeProfile (intermediate 0))) :=
  (finFamilyList_factorModule_append_boundary
      (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0))
      (singletonContractingDegreeProfile (intermediate 0))).symm.trans
    (finFamilyList_factorModule_eq_first_suffix
      ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
        (singletonContractingDegreeProfile (intermediate 0))))

/-- The final summand transport followed by first-factor coordinates is one list transport. -/
theorem headContractionTarget_transport
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    eqToHom (congrArg tensorModuleList
        (finFamilyList_factorModule_append_boundary
          (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0))
          (singletonContractingDegreeProfile (intermediate 0))).symm) ≫
        (summandFirstFactorIso
          ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
            (singletonContractingDegreeProfile (intermediate 0)))).hom =
      eqToHom (congrArg tensorModuleList (headContractionTargetListEq d)) := by
  unfold summandFirstFactorIso headContractionTargetListEq
  simp only [eqToIso.hom, eqToHom_trans]

/-- Appending a tensor list to a singleton removes only the inserted tensor unit. -/
theorem tensorModuleListAppendIso_singleton_apply
    (M : ModuleCat.{0} ℤ) (Ns : List (ModuleCat.{0} ℤ))
    (m : M) (n : tensorModuleList Ns) :
    (tensorModuleListAppendIso [M] Ns).hom.hom
        ((ρ_ M).inv.hom m ⊗ₜ[ℤ] n) = m ⊗ₜ[ℤ] n := by
  simp [tensorModuleListAppendIso, tensorModuleListOver]

/-- A head adjacent merge acts on the first two pure tensor factors. -/
theorem adjacentMergeAfter_nil_apply
    {M N P : ModuleCat.{0} ℤ} (ys : List (ModuleCat.{0} ℤ))
    (f : M ⊗ N ⟶ P) (m : M) (n : N) (t : tensorModuleList ys) :
    (adjacentMergeAfter ([] : List (ModuleCat.{0} ℤ))
      (ys := ys) f).tensorMap.hom (m ⊗ₜ[ℤ] (n ⊗ₜ[ℤ] t)) =
      f.hom (m ⊗ₜ[ℤ] n) ⊗ₜ[ℤ] t := by
  change ((α_ M N (tensorModuleList ys)).inv ≫
      (f ⊗ₘ 𝟙 (tensorModuleList ys))).hom
        (m ⊗ₜ[ℤ] (n ⊗ₜ[ℤ] t)) = _
  rw [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.associator_inv_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul,
    CategoryTheory.id_apply]

set_option maxHeartbeats 12000000 in
-- The dependent tensor reassociation below elaborates several large transported module terms.
/-- Composing the zero-word head with the formal contraction is the direct head/identity map. -/
theorem headContractionCompositionMap
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    headContractionInputMap d ≫
        summandCompositionMap
          (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0))
          (singletonContractingDegreeProfile (intermediate 0)) =
      headContractionDirectMap d := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  unfold headContractionInputMap headContractionDirectMap
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul]
  rw [singletonContractingElementMap_apply_one,
    headContractionIdentityTailMap_apply_one]
  apply_fun (summandFirstFactorIso
    ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
      (singletonContractingDegreeProfile (intermediate 0)))).hom.hom
  case inj =>
    exact (summandFirstFactorIso
      ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
        (singletonContractingDegreeProfile (intermediate 0)))).toLinearEquiv.injective
  simp only [Iso.inv_hom_id_apply]
  change ((summandCompositionMap
      (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0))
      (singletonContractingDegreeProfile (intermediate 0)) ≫
    (summandFirstFactorIso
      ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
        (singletonContractingDegreeProfile (intermediate 0)))).hom).hom
      ((positiveHeadSummandMap d).hom x ⊗ₜ[ℤ]
        singletonContractingElement (intermediate 0))) = _
  rw [summandCompositionMap_eq_boundary_decomposition]
  simp only [Category.assoc]
  rw [headContractionTarget_transport]
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul]
  have hhead := ConcreteCategory.congr_hom
    (positiveHeadSummandMap_comp_lastFactorIso d) x
  simp only [ModuleCat.comp_apply] at hhead
  rw [hhead, singletonFirstFactorIso_contractingElement]
  simp only [Int.reduceNeg, eqToHom_refl, ModuleCat.hom_id,
    ModuleCat.MonoidalCategory.rightUnitor_inv_apply]
  have hunitx := ConcreteCategory.congr_hom
    (headActualBoundaryMap_unit d)
    ((eqToHom (factorModule_zero_succ d)).hom x)
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul,
    CategoryTheory.id_apply] at hunitx
  let h := nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)
  let c := singletonContractingDegreeProfile (intermediate 0)
  change (adjacentMergeAfter ([] : List (ModuleCat.{0} ℤ))
      (ys := compositionRightSuffix c) (compositionBoundaryMap h c)).tensorMap.hom
        ((tensorModuleListAppendIso [factorModule h 0]
          (factorModule c 0 :: compositionRightSuffix c)).hom.hom
          ((ρ_ (factorModule h 0)).inv.hom
              ((eqToHom (factorModule_zero_succ d)).hom x) ⊗ₜ[ℤ]
            ((eqToHom (singletonContractingFactor_zero (intermediate 0)).symm).hom
                (identityCochain (intermediate 0).obj) ⊗ₜ[ℤ]
              (ρ_ (factorModule c 1)).inv.hom
                ((eqToHom
                  (singletonContractingFactor_one (intermediate 0)).symm).hom
                    (identityCochain (intermediate 0).obj))))) =
    (eqToHom (headContractionFactor_zero d).symm).hom x ⊗ₜ[ℤ]
      headContractionIdentityTail d
  rw [tensorModuleListAppendIso_singleton_apply]
  rw [adjacentMergeAfter_nil_apply]
  let hdom : factorModule d 0 = factorModule h 0 :=
    (factorModule_zero_succ d).trans
      (factorModule_nilDegreeProfile X (intermediate 0).obj
        (d.arrowDegree 0)).symm
  let hboundary : compositionBoundaryModule h c =
      factorModule (h.append c) 0 :=
    (headActualBoundaryModule_eq d).trans
      (hdom.symm.trans (headContractionFactor_zero d).symm)
  change (eqToHom hboundary).hom
        ((compositionBoundaryMap h c).hom
          ((eqToHom (headActualBoundarySource_eq d)).hom
            ((eqToHom (factorModule_zero_succ d)).hom x ⊗ₜ[ℤ]
              (eqToHom
                (singletonContractingFactor_zero (intermediate 0)).symm).hom
                  (identityCochain (intermediate 0).obj)))) ⊗ₜ[ℤ]
      (ρ_ (factorModule c 1)).inv.hom
        ((eqToHom
          (singletonContractingFactor_one (intermediate 0)).symm).hom
            (identityCochain (intermediate 0).obj)) =
    (eqToHom (headContractionFactor_zero d).symm).hom x ⊗ₜ[ℤ]
      headContractionIdentityTail d
  have hfirst :
      (eqToHom hboundary).hom
          ((compositionBoundaryMap h c).hom
            ((eqToHom (headActualBoundarySource_eq d)).hom
              ((eqToHom (factorModule_zero_succ d)).hom x ⊗ₜ[ℤ]
                (eqToHom
                  (singletonContractingFactor_zero (intermediate 0)).symm).hom
                    (identityCochain (intermediate 0).obj)))) =
        (eqToHom (headContractionFactor_zero d).symm).hom x := by
    have hboundaryMap : eqToHom hboundary =
        eqToHom (headActualBoundaryModule_eq d) ≫
          eqToHom (hdom.symm.trans (headContractionFactor_zero d).symm) := by
      change eqToHom ((headActualBoundaryModule_eq d).trans
          (hdom.symm.trans (headContractionFactor_zero d).symm)) = _
      rw [eqToHom_trans]
    rw [hboundaryMap]
    simp only [ModuleCat.comp_apply]
    rw [← singletonContractingFirstIdentityMap_apply_one]
    rw [hunitx]
    have hcancel :
        eqToHom (factorModule_zero_succ d) ≫
            eqToHom (hdom.symm.trans (headContractionFactor_zero d).symm) =
          eqToHom (headContractionFactor_zero d).symm := by
      rw [eqToHom_trans]
    calc
      _ = (eqToHom (factorModule_zero_succ d) ≫
          eqToHom (hdom.symm.trans (headContractionFactor_zero d).symm)).hom x := by
            rfl
      _ = _ := congrArg (fun f ↦ f.hom x) hcancel
  have htail :
      (ρ_ (factorModule c 1)).inv.hom
          ((eqToHom
            (singletonContractingFactor_one (intermediate 0)).symm).hom
              (identityCochain (intermediate 0).obj)) =
        headContractionIdentityTail d := by
    unfold headContractionIdentityTail
    rfl
  rw [hfirst, htail]

set_option maxHeartbeats 4000000 in
-- Expanding the map-level equality still requires the preceding transported composition proof.
/-- Composing the zero-word head with the formal contraction leaves the second identity factor. -/
theorem headContractionComposition_apply
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d 0) :
    (summandCompositionMap
        (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0))
        (singletonContractingDegreeProfile (intermediate 0))).hom
      (positiveHeadSummandElement d x ⊗ₜ[ℤ]
        singletonContractingElement (intermediate 0)) =
      headContractionDirectSummand d x := by
  have h := ConcreteCategory.congr_hom (headContractionCompositionMap d) x
  simp only [headContractionInputMap, headContractionDirectMap,
    positiveHeadSummandMap, ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul] at h
  rw [singletonContractingElementMap_apply_one,
    headContractionIdentityTailMap_apply_one] at h
  simpa only [positiveHeadSummandElement, headContractionDirectSummand] using h

end AnnihilatingEnrichedFunctorData
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
