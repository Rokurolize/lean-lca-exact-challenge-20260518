/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientPairCoherence

/-! # Transporting coherent contraction pairs to contracted DG factors -/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge.Infinity.MetrizableBoundedComplexes.DrinfeldWord

open CategoryTheory CategoryTheory.MonoidalCategory

theorem test_tensor_comp_transport_of_heq
    {A A' B B' C C' : ModuleCat.{0} ℤ}
    (hA : A = A') (hB : B = B') (hC : C = C')
    (f : A ⊗ B ⟶ C) (f' : A' ⊗ B' ⟶ C')
    (hf : HEq f' f) :
    (eqToHom hA ⊗ₘ eqToHom hB) ≫ f' = f ≫ eqToHom hC := by
  subst A'
  subst B'
  subst C'
  rw [eq_of_heq hf]
  simp

theorem test_eqToIso_symm_inv_eqToHom
    {A B : ModuleCat.{0} ℤ} (h : A = B) :
    (eqToIso h.symm).inv = eqToHom h := by
  subst B
  rfl

theorem test_recursiveMergedFactorMap_heq_id : {k : ℕ} →
    (M N : Fin (k + 1) → ModuleCat.{0} ℤ) → (i : Fin k) →
    (P P' : ModuleCat.{0} ℤ) →
    (a : (j : Fin (k + 1)) → M j ⟶ N j) → (g : P ⟶ P') →
    ((j : Fin (k + 1)) → HEq (a j) (𝟙 (M j))) →
    HEq g (𝟙 P) → (j : Fin k) →
    HEq (recursiveMergedFactorMap M N i P P' a g j)
      (𝟙 (recursiveMergedFactor M i P j))
  | 0, _, _, i, _, _, _, _, _, _ => Fin.elim0 i
  | k + 1, M, N, i, P, P', a, g, ha, hg => by
      cases i using Fin.cases with
      | zero =>
          intro j
          cases j using Fin.cases with
          | zero => simpa [recursiveMergedFactorMap, recursiveMergedFactor] using hg
          | succ j =>
              simpa [recursiveMergedFactorMap, recursiveMergedFactor] using
                ha j.succ.succ
      | succ q =>
          intro j
          cases j using Fin.cases with
          | zero =>
              simpa [recursiveMergedFactorMap, recursiveMergedFactor] using ha 0
          | succ j =>
              simpa [recursiveMergedFactorMap, recursiveMergedFactor] using
                test_recursiveMergedFactorMap_heq_id
                  (fun r : Fin (k + 1) ↦ M r.succ)
                  (fun r : Fin (k + 1) ↦ N r.succ) q P P'
                  (fun r ↦ a r.succ) g (fun r ↦ ha r.succ) hg j

theorem test_recursiveMergedFactorMap_eqToHom : {k : ℕ} →
    (M N : Fin (k + 1) → ModuleCat.{0} ℤ) → (i : Fin k) →
    (P P' : ModuleCat.{0} ℤ) →
    (a : (j : Fin (k + 1)) → M j ⟶ N j) → (g : P ⟶ P') →
    ((j : Fin (k + 1)) → ∃ h : M j = N j, a j = eqToHom h) →
    (∃ h : P = P', g = eqToHom h) → (j : Fin k) →
    ∃ h : recursiveMergedFactor M i P j = recursiveMergedFactor N i P' j,
      recursiveMergedFactorMap M N i P P' a g j = eqToHom h
  | 0, _, _, i, _, _, _, _, _, _ => Fin.elim0 i
  | k + 1, M, N, i, P, P', a, g, ha, hg => by
      cases i using Fin.cases with
      | zero =>
          intro j
          cases j using Fin.cases with
          | zero => simpa [recursiveMergedFactorMap, recursiveMergedFactor] using hg
          | succ j =>
              simpa [recursiveMergedFactorMap, recursiveMergedFactor] using
                ha j.succ.succ
      | succ q =>
          intro j
          cases j using Fin.cases with
          | zero =>
              simpa [recursiveMergedFactorMap, recursiveMergedFactor] using ha 0
          | succ j =>
              simpa [recursiveMergedFactorMap, recursiveMergedFactor] using
                test_recursiveMergedFactorMap_eqToHom
                  (fun r : Fin (k + 1) ↦ M r.succ)
                  (fun r : Fin (k + 1) ↦ N r.succ) q P P'
                  (fun r ↦ a r.succ) g (fun r ↦ ha r.succ) hg j

theorem test_comp_eqToHom
    {A B C : ModuleCat.{0} ℤ} (f : A ⟶ B) (g : B ⟶ C)
    (hf : ∃ h : A = B, f = eqToHom h)
    (hg : ∃ h : B = C, g = eqToHom h) :
    ∃ h : A = C, f ≫ g = eqToHom h := by
  obtain ⟨hAB, rfl⟩ := hf
  obtain ⟨hBC, rfl⟩ := hg
  exact ⟨hAB.trans hBC, by simp⟩

theorem test_comp_eqToHom_heq
    {A B C : ModuleCat.{0} ℤ} (f : A ⟶ B) (h : B = C) :
    HEq (f ≫ eqToHom h) f := by
  subst C
  simp

def test_rawContractionMergedFactorMap
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i j : Fin w.length) :
    Quiver.Hom
      (recursiveMergedFactor (factorModule d) i (rawContractionFactor d i) j)
      (recursiveMergedFactor (factorModule d) i
        (contractedFactorAtOldIndex d i i) j) :=
  recursiveMergedFactorMap (factorModule d) (factorModule d) i
    (rawContractionFactor d i) (contractedFactorAtOldIndex d i i)
    (fun q => 𝟙 (factorModule d q)) (contractFactorAtOldIndexIso d i).inv j

theorem test_contractFactorAtOldIndexIso_inv_eqToHom
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    ∃ h : rawContractionFactor d i = contractedFactorAtOldIndex d i i,
      (contractFactorAtOldIndexIso d i).inv = eqToHom h := by
  unfold contractFactorAtOldIndexIso contractFactorModuleAtIso
  refine ⟨?_, rfl⟩
  unfold rawContractionFactor contractedFactorAtOldIndex factorModule
  rw [uneraseFactorIndex_self, eraseIntermediate_arrowSource_at w i,
    eraseIntermediate_arrowTarget_at w i, contract_arrowDegree_at d i]

theorem test_rawContractionMergedFactorMap_eqToHom
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i q : Fin w.length) :
  ∃ h : recursiveMergedFactor (factorModule d) i
        (rawContractionFactor d i) q =
      recursiveMergedFactor (factorModule d) i
        (contractedFactorAtOldIndex d i i) q,
      test_rawContractionMergedFactorMap d i q = eqToHom h := by
  apply test_recursiveMergedFactorMap_eqToHom
  · intro r
    exact ⟨rfl, rfl⟩
  · exact test_contractFactorAtOldIndexIso_inv_eqToHom d i

theorem test_recursiveContractionMergedFactorMap_eqToHom
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i q : Fin w.length) :
    ∃ h : recursiveMergedFactor (factorModule d) i
        (contractedFactorAtOldIndex d i i) q =
      contractedFactorAtOldIndex d i q,
      recursiveContractionMergedFactorMap d i q = eqToHom h := by
  exact ⟨recursiveContractionMergedFactor_eq d i q, rfl⟩

theorem test_rawContractionAdjacentMerge_naturality
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    AdjacentMergeNaturality
      (rawContractionAdjacentMergeData d i)
      (recursiveContractionAdjacentMergeData d i)
      (TensorMapData.ofFn (factorModule d) (factorModule d)
        (fun q => 𝟙 (factorModule d q)))
      (TensorMapData.ofFn
        (recursiveMergedFactor (factorModule d) i (rawContractionFactor d i))
        (recursiveMergedFactor (factorModule d) i
          (contractedFactorAtOldIndex d i i))
        (test_rawContractionMergedFactorMap d i)) := by
  apply recursiveAdjacentMergeDataOfFn_naturality
  simp [contractionMergeAtOldIndex]

theorem test_rawSecondContractionFactor_eq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    rawSecondContractionFactor d i j =
      rawContractionFactor (d.contract i) j := by
  let w : DrinfeldWord X Y :=
    { length := k + 2, intermediate := intermediate }
  change DegreeProfile w n at d
  by_cases hleft : i = j.castSucc
  · subst i
    have hpos : erasePosition w j.castSucc = j.castSucc := rfl
    have hs : (eraseIntermediate w j.castSucc).arrowSource j.castSucc =
        w.arrowSource j.castSucc.castSucc := by
      calc
        _ = (eraseIntermediate w j.castSucc).arrowSource
            (erasePosition w j.castSucc) :=
          congrArg ((eraseIntermediate w j.castSucc).arrowSource ·) hpos.symm
        _ = _ := eraseIntermediate_arrowSource_at w j.castSucc
    have hafter : j.castSucc < eraseFactorIndex w j.castSucc j.succ := by
      change j.val < j.val + 1
      omega
    have hindex₁ : eraseFactorIndex w j.castSucc j.succ = j.succ := rfl
    have ht : (eraseIntermediate w j.castSucc).arrowTarget j.succ =
        w.arrowTarget j.succ.succ := by
      simpa [hindex₁] using eraseIntermediate_arrowTarget_of_after
        w j.castSucc j.succ hafter
    have hd₀ : (d.contract j.castSucc).arrowDegree j.castSucc =
        d.arrowDegree j.castSucc.castSucc + d.arrowDegree j.castSucc.succ := by
      calc
        _ = (d.contract j.castSucc).arrowDegree
            (erasePosition w j.castSucc) :=
          congrArg ((d.contract j.castSucc).arrowDegree ·) hpos.symm
        _ = _ := contract_arrowDegree_at d j.castSucc
    have hd₁ : (d.contract j.castSucc).arrowDegree j.succ =
        d.arrowDegree j.succ.succ := by
      simpa [hindex₁] using contract_arrowDegree_of_after
        d j.castSucc j.succ hafter
    unfold rawSecondContractionFactor rawTripleContractionFactor
      rawContractionFactor
    simp only [true_or, if_true]
    rw [hs, ht, hd₀, hd₁]
  · by_cases hright : i = j.succ
    · subst i
      have hpos : erasePosition w j.succ = j.succ := rfl
      have hbefore : eraseFactorIndex w j.succ j.castSucc < j.succ := by
        change j.val < j.val + 1
        omega
      have hindex₀ : eraseFactorIndex w j.succ j.castSucc = j.castSucc := rfl
      have hs : (eraseIntermediate w j.succ).arrowSource j.castSucc =
          w.arrowSource j.castSucc.castSucc := by
        simpa [hindex₀] using eraseIntermediate_arrowSource_of_before
          w j.succ j.castSucc hbefore
      have ht : (eraseIntermediate w j.succ).arrowTarget j.succ =
          w.arrowTarget j.succ.succ := by
        calc
          _ = (eraseIntermediate w j.succ).arrowTarget
              (erasePosition w j.succ) :=
            congrArg ((eraseIntermediate w j.succ).arrowTarget ·) hpos.symm
          _ = _ := eraseIntermediate_arrowTarget_at w j.succ
      have hd₀ : (d.contract j.succ).arrowDegree j.castSucc =
          d.arrowDegree j.castSucc.castSucc := by
        simpa [hindex₀] using contract_arrowDegree_of_before
          d j.succ j.castSucc hbefore
      have hd₁ : (d.contract j.succ).arrowDegree j.succ =
          d.arrowDegree j.castSucc.succ + d.arrowDegree j.succ.succ := by
        calc
          _ = (d.contract j.succ).arrowDegree (erasePosition w j.succ) :=
            congrArg ((d.contract j.succ).arrowDegree ·) hpos.symm
          _ = _ := contract_arrowDegree_at d j.succ
      unfold rawSecondContractionFactor rawTripleContractionFactor
        rawContractionFactor
      simp only [or_true, if_true]
      rw [hs, ht, hd₀, hd₁]
      simp [w, add_assoc]
    · by_cases hbefore : j.castSucc < i
      · have hjnext : j.succ < i := by
          have hval : j.val < i.val := hbefore
          have hneval : i.val ≠ j.val + 1 := by
            intro h
            apply hright
            apply Fin.ext
            simpa using h
          change j.val + 1 < i.val
          omega
        have hindex₀ : eraseFactorIndex w i j.castSucc = j.castSucc := rfl
        have hindex₁ : eraseFactorIndex w i j.succ = j.succ := rfl
        have hs : (eraseIntermediate w i).arrowSource j.castSucc =
            w.arrowSource j.castSucc.castSucc := by
          simpa [hindex₀] using
            eraseIntermediate_arrowSource_of_before w i j.castSucc hbefore
        have ht : (eraseIntermediate w i).arrowTarget j.succ =
            w.arrowTarget j.castSucc.succ := by
          simpa [hindex₁] using
            eraseIntermediate_arrowTarget_of_before w i j.succ hjnext
        have hd₀ : (d.contract i).arrowDegree j.castSucc =
            d.arrowDegree j.castSucc.castSucc := by
          simpa [hindex₀] using
            contract_arrowDegree_of_before d i j.castSucc hbefore
        have hd₁ : (d.contract i).arrowDegree j.succ =
            d.arrowDegree j.castSucc.succ := by
          simpa [hindex₁] using
            contract_arrowDegree_of_before d i j.succ hjnext
        unfold rawSecondContractionFactor rawContractionFactor
        simp only [hleft, hright, or_false, if_false]
        rw [Fin.succAbove_of_castSucc_lt i j hbefore]
        rw [hs, ht, hd₀, hd₁]
      · have hafter : i < j.castSucc :=
          lt_of_le_of_ne (Fin.not_lt.mp hbefore) hleft
        have hafter' : i < j.succ := lt_trans hafter Fin.castSucc_lt_succ
        have hindex₀ : eraseFactorIndex w i j.castSucc = j.castSucc := rfl
        have hindex₁ : eraseFactorIndex w i j.succ = j.succ := rfl
        have hs : (eraseIntermediate w i).arrowSource j.castSucc =
            w.arrowSource j.succ.castSucc := by
          simpa [hindex₀] using
            eraseIntermediate_arrowSource_of_after w i j.castSucc hafter
        have ht : (eraseIntermediate w i).arrowTarget j.succ =
            w.arrowTarget j.succ.succ := by
          simpa [hindex₁] using
            eraseIntermediate_arrowTarget_of_after w i j.succ hafter'
        have hd₀ : (d.contract i).arrowDegree j.castSucc =
            d.arrowDegree j.succ.castSucc := by
          simpa [hindex₀] using
            contract_arrowDegree_of_after d i j.castSucc hafter
        have hd₁ : (d.contract i).arrowDegree j.succ =
            d.arrowDegree j.succ.succ := by
          simpa [hindex₁] using
            contract_arrowDegree_of_after d i j.succ hafter'
        unfold rawSecondContractionFactor rawContractionFactor
        simp only [hleft, hright, or_false, if_false]
        rw [Fin.succAbove_of_le_castSucc i j hafter.le]
        rw [hs, ht, hd₀, hd₁]

def test_rawSecondContractionFactorIso
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    contractedFactorAtOldIndex (d.contract i) j j ≅
      rawSecondContractionFactor d i j :=
  contractFactorAtOldIndexIso (d.contract i) j ≪≫
    eqToIso (test_rawSecondContractionFactor_eq d i j).symm

def test_rawSecondContractionTargetFactorMap
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j q : Fin (k + 1)) :
    Quiver.Hom
      (recursiveMergedFactor
        (recursiveMergedFactor (factorModule d) i (rawContractionFactor d i)) j
        (rawSecondContractionFactor d i j) q)
      (recursiveMergedFactor
        (recursiveMergedFactor (factorModule d) i
          (contractedFactorAtOldIndex d i i)) j
        (contractedFactorAtOldIndex (d.contract i) j j) q) :=
  recursiveMergedFactorMap
    (recursiveMergedFactor (factorModule d) i (rawContractionFactor d i))
    (recursiveMergedFactor (factorModule d) i
      (contractedFactorAtOldIndex d i i)) j
    (rawSecondContractionFactor d i j)
    (contractedFactorAtOldIndex (d.contract i) j j)
    (test_rawContractionMergedFactorMap d i)
    (test_rawSecondContractionFactorIso d i j).inv q

def test_rawToContractedFactorMap
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i q : Fin w.length) :
    Quiver.Hom
      (recursiveMergedFactor (factorModule d) i (rawContractionFactor d i) q)
      (contractedFactorAtOldIndex d i q) :=
  test_rawContractionMergedFactorMap d i q ≫
    recursiveContractionMergedFactorMap d i q

theorem test_rawToContractedFactor_eq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i q : Fin w.length) :
    recursiveMergedFactor (factorModule d) i (rawContractionFactor d i) q =
      contractedFactorAtOldIndex d i q := by
  rw [recursiveMergedFactor_eq_mergedFactor]
  by_cases hlt : q < i
  · have hbefore :
        eraseFactorIndex w i (uneraseFactorIndex w i q) < i := by
      simpa using hlt
    simp only [mergedFactor, hlt, if_true, contractedFactorAtOldIndex,
      factorModule]
    rw [eraseIntermediate_arrowSource_of_before w i
        (uneraseFactorIndex w i q) hbefore,
      eraseIntermediate_arrowTarget_of_before w i
        (uneraseFactorIndex w i q) hbefore,
      contract_arrowDegree_of_before d i
        (uneraseFactorIndex w i q) hbefore,
      eraseFactorIndex_uneraseFactorIndex]
  · by_cases heq : q = i
    · subst q
      simp only [mergedFactor, Fin.lt_irrefl, if_false, if_true,
        contractedFactorAtOldIndex, rawContractionFactor, factorModule,
        uneraseFactorIndex_self]
      rw [eraseIntermediate_arrowSource_at w i,
        eraseIntermediate_arrowTarget_at w i,
        contract_arrowDegree_at d i]
    · have hafter :
          i < eraseFactorIndex w i (uneraseFactorIndex w i q) := by
        rw [eraseFactorIndex_uneraseFactorIndex]
        exact lt_of_le_of_ne (Fin.not_lt.mp hlt) (Ne.symm heq)
      simp only [mergedFactor, hlt, heq, if_false,
        contractedFactorAtOldIndex, factorModule]
      rw [eraseIntermediate_arrowSource_of_after w i
          (uneraseFactorIndex w i q) hafter,
        eraseIntermediate_arrowTarget_of_after w i
          (uneraseFactorIndex w i q) hafter,
        contract_arrowDegree_of_after d i
          (uneraseFactorIndex w i q) hafter,
        eraseFactorIndex_uneraseFactorIndex]

theorem test_rawToContractedFactorMap_eqToHom
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i q : Fin w.length) :
    test_rawToContractedFactorMap d i q =
      eqToHom (test_rawToContractedFactor_eq d i q) := by
  obtain ⟨h₁, hh₁⟩ := test_rawContractionMergedFactorMap_eqToHom d i q
  obtain ⟨h₂, hh₂⟩ := test_recursiveContractionMergedFactorMap_eqToHom d i q
  obtain ⟨h, hh⟩ := test_comp_eqToHom _ _ ⟨h₁, hh₁⟩ ⟨h₂, hh₂⟩
  unfold test_rawToContractedFactorMap
  rw [hh]

theorem test_rawSecondContractionMerge_actual_heq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    HEq (adjacentFactorComposition (d.contract i) j)
      (rawSecondContractionMerge d i j) := by
  by_cases hleft : i = j.castSucc
  · subst i
    apply HEq.trans _ (rawSecondContractionMerge_left_heq d j).symm
    unfold adjacentFactorComposition factorModule
    apply dgCochainCompTensorOfEq_heq
    · change (eraseIntermediate
          (({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord X Y)) j.castSucc).arrowSource
            (erasePosition
              (({ length := k + 2, intermediate := intermediate } :
                DrinfeldWord X Y)) j.castSucc) = _
      exact eraseIntermediate_arrowSource_at
        (({ length := k + 2, intermediate := intermediate } :
          DrinfeldWord X Y)) j.castSucc
    · change (eraseIntermediate
          (({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord X Y)) j.castSucc).arrowTarget
            (erasePosition
              (({ length := k + 2, intermediate := intermediate } :
                DrinfeldWord X Y)) j.castSucc) = _
      exact eraseIntermediate_arrowTarget_at
        (({ length := k + 2, intermediate := intermediate } :
          DrinfeldWord X Y)) j.castSucc
    · have hafter : j.castSucc < eraseFactorIndex
          (({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord X Y)) j.castSucc j.succ := by
        change j.val < j.val + 1
        omega
      change (eraseIntermediate
          (({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord X Y)) j.castSucc).arrowSource j.succ = _
      have hindex : eraseFactorIndex
          (({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord X Y)) j.castSucc j.succ = j.succ := rfl
      simpa only [hindex] using eraseIntermediate_arrowSource_of_after
        (({ length := k + 2, intermediate := intermediate } :
          DrinfeldWord X Y)) j.castSucc j.succ hafter
    · have hafter : j.castSucc < eraseFactorIndex
          (({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord X Y)) j.castSucc j.succ := by
        change j.val < j.val + 1
        omega
      change (eraseIntermediate
          (({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord X Y)) j.castSucc).arrowTarget j.succ = _
      have hindex : eraseFactorIndex
          (({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord X Y)) j.castSucc j.succ = j.succ := rfl
      simpa only [hindex] using eraseIntermediate_arrowTarget_of_after
        (({ length := k + 2, intermediate := intermediate } :
          DrinfeldWord X Y)) j.castSucc j.succ hafter
    · change (d.contract j.castSucc).arrowDegree
          (erasePosition
            (({ length := k + 2, intermediate := intermediate } :
              DrinfeldWord X Y)) j.castSucc) = _
      rw [contract_arrowDegree_at]
    · have hafter : j.castSucc < eraseFactorIndex
          (({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord X Y)) j.castSucc j.succ := by
        change j.val < j.val + 1
        omega
      change (d.contract j.castSucc).arrowDegree j.succ = _
      have hindex : eraseFactorIndex
          (({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord X Y)) j.castSucc j.succ = j.succ := rfl
      simpa only [hindex] using
        contract_arrowDegree_of_after d j.castSucc j.succ hafter
    · change (d.contract j.castSucc).arrowDegree
          (erasePosition
            (({ length := k + 2, intermediate := intermediate } :
              DrinfeldWord X Y)) j.castSucc) +
          (d.contract j.castSucc).arrowDegree j.succ = _
      have hp := contract_arrowDegree_at d j.castSucc
      have hafter : j.castSucc < eraseFactorIndex
          (({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord X Y)) j.castSucc j.succ := by
        change j.val < j.val + 1
        omega
      have hq := contract_arrowDegree_of_after d j.castSucc j.succ hafter
      have hindex : eraseFactorIndex
          (({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord X Y)) j.castSucc j.succ = j.succ := rfl
      rw [hindex] at hq
      omega
  · by_cases hright : i = j.succ
    · subst i
      apply HEq.trans _ (rawSecondContractionMerge_right_heq d j).symm
      unfold adjacentFactorComposition factorModule
      apply dgCochainCompTensorOfEq_heq
      · have hbefore : eraseFactorIndex
            (({ length := k + 2, intermediate := intermediate } :
              DrinfeldWord X Y)) j.succ j.castSucc < j.succ := by
          change j.val < j.val + 1
          omega
        change (eraseIntermediate
            (({ length := k + 2, intermediate := intermediate } :
              DrinfeldWord X Y)) j.succ).arrowSource j.castSucc = _
        have hindex : eraseFactorIndex
            (({ length := k + 2, intermediate := intermediate } :
              DrinfeldWord X Y)) j.succ j.castSucc = j.castSucc := rfl
        simpa only [hindex] using eraseIntermediate_arrowSource_of_before
          (({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord X Y)) j.succ j.castSucc hbefore
      · have hbefore : eraseFactorIndex
            (({ length := k + 2, intermediate := intermediate } :
              DrinfeldWord X Y)) j.succ j.castSucc < j.succ := by
          change j.val < j.val + 1
          omega
        change (eraseIntermediate
            (({ length := k + 2, intermediate := intermediate } :
              DrinfeldWord X Y)) j.succ).arrowTarget j.castSucc = _
        have hindex : eraseFactorIndex
            (({ length := k + 2, intermediate := intermediate } :
              DrinfeldWord X Y)) j.succ j.castSucc = j.castSucc := rfl
        simpa only [hindex] using eraseIntermediate_arrowTarget_of_before
          (({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord X Y)) j.succ j.castSucc hbefore
      · change (eraseIntermediate
            (({ length := k + 2, intermediate := intermediate } :
              DrinfeldWord X Y)) j.succ).arrowSource
              (erasePosition
                (({ length := k + 2, intermediate := intermediate } :
                  DrinfeldWord X Y)) j.succ) = _
        exact eraseIntermediate_arrowSource_at
          (({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord X Y)) j.succ
      · change (eraseIntermediate
            (({ length := k + 2, intermediate := intermediate } :
              DrinfeldWord X Y)) j.succ).arrowTarget
              (erasePosition
                (({ length := k + 2, intermediate := intermediate } :
                  DrinfeldWord X Y)) j.succ) = _
        exact eraseIntermediate_arrowTarget_at
          (({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord X Y)) j.succ
      · have hbefore : eraseFactorIndex
            (({ length := k + 2, intermediate := intermediate } :
              DrinfeldWord X Y)) j.succ j.castSucc < j.succ := by
          change j.val < j.val + 1
          omega
        change (d.contract j.succ).arrowDegree j.castSucc = _
        have hindex : eraseFactorIndex
            (({ length := k + 2, intermediate := intermediate } :
              DrinfeldWord X Y)) j.succ j.castSucc = j.castSucc := rfl
        simpa only [hindex] using
          contract_arrowDegree_of_before d j.succ j.castSucc hbefore
      · change (d.contract j.succ).arrowDegree
            (erasePosition
              (({ length := k + 2, intermediate := intermediate } :
                DrinfeldWord X Y)) j.succ) = _
        rw [contract_arrowDegree_at]
        have hmiddle : j.succ.castSucc = j.castSucc.succ := by
          apply Fin.ext
          rfl
        rw [hmiddle]
      · change (d.contract j.succ).arrowDegree j.castSucc +
            (d.contract j.succ).arrowDegree
              (erasePosition
                (({ length := k + 2, intermediate := intermediate } :
                  DrinfeldWord X Y)) j.succ) = _
        have hbefore : eraseFactorIndex
            (({ length := k + 2, intermediate := intermediate } :
              DrinfeldWord X Y)) j.succ j.castSucc < j.succ := by
          change j.val < j.val + 1
          omega
        have hp := contract_arrowDegree_of_before d j.succ j.castSucc hbefore
        have hindex : eraseFactorIndex
            (({ length := k + 2, intermediate := intermediate } :
              DrinfeldWord X Y)) j.succ j.castSucc = j.castSucc := rfl
        rw [hindex] at hp
        have hq := contract_arrowDegree_at d j.succ
        have hmiddle : j.succ.castSucc = j.castSucc.succ := by
          apply Fin.ext
          rfl
        rw [hmiddle] at hq
        omega
    · by_cases hbefore : j.castSucc < i
      · have hjnext : j.succ < i := by
          have hval : j.val < i.val := hbefore
          have hneval : i.val ≠ j.val + 1 := by
            intro h
            apply hright
            apply Fin.ext
            simpa using h
          change j.val + 1 < i.val
          omega
        have hraw : HEq (rawSecondContractionMerge d i j)
            (adjacentFactorComposition d j.castSucc) := by
          unfold rawSecondContractionMerge
          simp [rawSecondContractionFactor, hleft, hright, hbefore]
        apply HEq.trans _ hraw.symm
        unfold adjacentFactorComposition factorModule
        apply dgCochainCompTensorOfEq_heq
        · have hindex : eraseFactorIndex
              (({ length := k + 2, intermediate := intermediate } :
                DrinfeldWord X Y)) i j.castSucc = j.castSucc := rfl
          simpa only [hindex] using eraseIntermediate_arrowSource_of_before
            (({ length := k + 2, intermediate := intermediate } :
              DrinfeldWord X Y)) i j.castSucc hbefore
        · have hindex : eraseFactorIndex
              (({ length := k + 2, intermediate := intermediate } :
                DrinfeldWord X Y)) i j.castSucc = j.castSucc := rfl
          simpa only [hindex] using eraseIntermediate_arrowTarget_of_before
            (({ length := k + 2, intermediate := intermediate } :
              DrinfeldWord X Y)) i j.castSucc hbefore
        · have hindex : eraseFactorIndex
              (({ length := k + 2, intermediate := intermediate } :
                DrinfeldWord X Y)) i j.succ = j.succ := rfl
          have hmiddle : j.succ.castSucc = j.castSucc.succ := by
            apply Fin.ext
            rfl
          simpa only [hindex, hmiddle] using
            eraseIntermediate_arrowSource_of_before
              (({ length := k + 2, intermediate := intermediate } :
                DrinfeldWord X Y)) i j.succ hjnext
        · have hindex : eraseFactorIndex
              (({ length := k + 2, intermediate := intermediate } :
                DrinfeldWord X Y)) i j.succ = j.succ := rfl
          have hmiddle : j.succ.castSucc = j.castSucc.succ := by
            apply Fin.ext
            rfl
          simpa only [hindex, hmiddle] using
            eraseIntermediate_arrowTarget_of_before
              (({ length := k + 2, intermediate := intermediate } :
                DrinfeldWord X Y)) i j.succ hjnext
        · have hindex : eraseFactorIndex
              (({ length := k + 2, intermediate := intermediate } :
                DrinfeldWord X Y)) i j.castSucc = j.castSucc := rfl
          simpa only [hindex] using
            contract_arrowDegree_of_before d i j.castSucc hbefore
        · have hindex : eraseFactorIndex
              (({ length := k + 2, intermediate := intermediate } :
                DrinfeldWord X Y)) i j.succ = j.succ := rfl
          have hmiddle : j.succ.castSucc = j.castSucc.succ := by
            apply Fin.ext
            rfl
          simpa only [hindex, hmiddle] using
            contract_arrowDegree_of_before d i j.succ hjnext
        · have hp := contract_arrowDegree_of_before d i j.castSucc hbefore
          have hq := contract_arrowDegree_of_before d i j.succ hjnext
          have hindex₀ : eraseFactorIndex
              (({ length := k + 2, intermediate := intermediate } :
                DrinfeldWord X Y)) i j.castSucc = j.castSucc := rfl
          have hindex₁ : eraseFactorIndex
              (({ length := k + 2, intermediate := intermediate } :
                DrinfeldWord X Y)) i j.succ = j.succ := rfl
          have hmiddle : j.succ.castSucc = j.castSucc.succ := by
            apply Fin.ext
            rfl
          rw [hindex₀] at hp
          rw [hindex₁, hmiddle] at hq
          omega
      · have hafter : i < j.castSucc :=
          lt_of_le_of_ne (Fin.not_lt.mp hbefore) hleft
        have hafter' : i < j.succ := lt_trans hafter Fin.castSucc_lt_succ
        have hraw : HEq (rawSecondContractionMerge d i j)
            (adjacentFactorComposition d j.succ) := by
          unfold rawSecondContractionMerge
          simp [rawSecondContractionFactor, hleft, hright, hbefore]
        apply HEq.trans _ hraw.symm
        unfold adjacentFactorComposition factorModule
        apply dgCochainCompTensorOfEq_heq
        · have hindex : eraseFactorIndex
              (({ length := k + 2, intermediate := intermediate } :
                DrinfeldWord X Y)) i j.castSucc = j.castSucc := rfl
          have hmiddle : j.castSucc.succ = j.succ.castSucc := by
            apply Fin.ext
            rfl
          simpa only [hindex, hmiddle] using eraseIntermediate_arrowSource_of_after
            (({ length := k + 2, intermediate := intermediate } :
              DrinfeldWord X Y)) i j.castSucc hafter
        · have hindex : eraseFactorIndex
              (({ length := k + 2, intermediate := intermediate } :
                DrinfeldWord X Y)) i j.castSucc = j.castSucc := rfl
          have hmiddle : j.castSucc.succ = j.succ.castSucc := by
            apply Fin.ext
            rfl
          simpa only [hindex, hmiddle] using eraseIntermediate_arrowTarget_of_after
            (({ length := k + 2, intermediate := intermediate } :
              DrinfeldWord X Y)) i j.castSucc hafter
        · have hindex : eraseFactorIndex
              (({ length := k + 2, intermediate := intermediate } :
                DrinfeldWord X Y)) i j.succ = j.succ := rfl
          simpa only [hindex] using eraseIntermediate_arrowSource_of_after
            (({ length := k + 2, intermediate := intermediate } :
              DrinfeldWord X Y)) i j.succ hafter'
        · have hindex : eraseFactorIndex
              (({ length := k + 2, intermediate := intermediate } :
                DrinfeldWord X Y)) i j.succ = j.succ := rfl
          simpa only [hindex] using eraseIntermediate_arrowTarget_of_after
            (({ length := k + 2, intermediate := intermediate } :
              DrinfeldWord X Y)) i j.succ hafter'
        · have hindex : eraseFactorIndex
              (({ length := k + 2, intermediate := intermediate } :
                DrinfeldWord X Y)) i j.castSucc = j.castSucc := rfl
          have hmiddle : j.castSucc.succ = j.succ.castSucc := by
            apply Fin.ext
            rfl
          simpa only [hindex, hmiddle] using
            contract_arrowDegree_of_after d i j.castSucc hafter
        · have hindex : eraseFactorIndex
              (({ length := k + 2, intermediate := intermediate } :
                DrinfeldWord X Y)) i j.succ = j.succ := rfl
          simpa only [hindex] using
            contract_arrowDegree_of_after d i j.succ hafter'
        · have hp := contract_arrowDegree_of_after d i j.castSucc hafter
          have hq := contract_arrowDegree_of_after d i j.succ hafter'
          have hindex₀ : eraseFactorIndex
              (({ length := k + 2, intermediate := intermediate } :
                DrinfeldWord X Y)) i j.castSucc = j.castSucc := rfl
          have hindex₁ : eraseFactorIndex
              (({ length := k + 2, intermediate := intermediate } :
                DrinfeldWord X Y)) i j.succ = j.succ := rfl
          have hmiddle : j.castSucc.succ = j.succ.castSucc := by
            apply Fin.ext
            rfl
          rw [hindex₀, hmiddle] at hp
          rw [hindex₁] at hq
          omega

theorem test_rawSecondContractionMerge_naturality
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    AdjacentMergeNaturality
      (rawSecondContractionMergeData d i j)
      (transportedSecondContractionMergeData d i j)
      (TensorMapData.ofFn
        (recursiveMergedFactor (factorModule d) i (rawContractionFactor d i))
        (recursiveMergedFactor (factorModule d) i
          (contractedFactorAtOldIndex d i i))
        (test_rawContractionMergedFactorMap d i))
      (TensorMapData.ofFn
        (recursiveMergedFactor
          (recursiveMergedFactor (factorModule d) i (rawContractionFactor d i)) j
          (rawSecondContractionFactor d i j))
        (recursiveMergedFactor
          (recursiveMergedFactor (factorModule d) i
            (contractedFactorAtOldIndex d i i)) j
          (contractedFactorAtOldIndex (d.contract i) j j))
        (test_rawSecondContractionTargetFactorMap d i j)) := by
  apply recursiveAdjacentMergeDataOfFn_naturality
  unfold transportedSecondContractionMergeAtCanonical
  rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
  change
    ((test_rawToContractedFactorMap d i j.castSucc ⊗ₘ
        test_rawToContractedFactorMap d i j.succ) ≫
      contractionMergeAtOldIndex (d.contract i) j) =
      rawSecondContractionMerge d i j ≫
        (test_rawSecondContractionFactorIso d i j).inv
  rw [test_rawToContractedFactorMap_eqToHom,
    test_rawToContractedFactorMap_eqToHom]
  unfold contractionMergeAtOldIndex test_rawSecondContractionFactorIso
  simp only [Iso.trans_inv]
  rw [← Category.assoc, ← Category.assoc]
  refine (cancel_mono (contractFactorAtOldIndexIso (d.contract i) j).inv).2 ?_
  rw [test_eqToIso_symm_inv_eqToHom]
  simpa only [rawContractionFactor, Category.assoc] using
    test_tensor_comp_transport_of_heq
      (test_rawToContractedFactor_eq d i j.castSucc)
      (test_rawToContractedFactor_eq d i j.succ)
      (test_rawSecondContractionFactor_eq d i j)
      (rawSecondContractionMerge d i j)
      (adjacentFactorComposition (d.contract i) j)
      (test_rawSecondContractionMerge_actual_heq d i j)

theorem test_tensorMapData_ofFn_eqToHom
    {k : ℕ} (M N : Fin k → ModuleCat.{0} ℤ) (h : M = N)
    (f : (q : Fin k) → M q ⟶ N q)
    (hf : ∀ q, f q = eqToHom (congrFun h q)) :
    (TensorMapData.ofFn M N f).tensorMap =
      eqToHom (congrArg tensorModuleList (congrArg finFamilyList h)) := by
  cases h
  have hfun : f = fun q ↦ 𝟙 (M q) := by
    funext q
    simpa using hf q
  subst f
  simp

noncomputable def test_rawContractionTarget_eq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    (fun q ↦ recursiveMergedFactor
      (factorModule d) i (rawContractionFactor d i) q) =
      contractedFactorAtOldIndex d i :=
  funext (test_rawToContractedFactor_eq d i)

def test_rawContractionTargetTensorMap
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :=
  (TensorMapData.ofFn
    (fun q ↦ recursiveMergedFactor
      (factorModule d) i (rawContractionFactor d i) q)
    (contractedFactorAtOldIndex d i)
    (test_rawToContractedFactorMap d i)).tensorMap

theorem test_rawContractionTargetTensorMap_eqToHom
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    test_rawContractionTargetTensorMap d i =
      eqToHom (congrArg tensorModuleList
        (congrArg finFamilyList (test_rawContractionTarget_eq d i))) := by
  exact test_tensorMapData_ofFn_eqToHom _ _
    (test_rawContractionTarget_eq d i) _
    (test_rawToContractedFactorMap_eqToHom d i)

theorem test_contractionTensorMap_normal_form
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    contractionTensorMap d i =
      (rawContractionAdjacentMergeData d i).tensorMap ≫
        test_rawContractionTargetTensorMap d i ≫
        (contractedFactorsOldIndexIso d i).hom := by
  have hfirst := (test_rawContractionAdjacentMerge_naturality d i).tensorMap_comm
  simp only [TensorMapData.ofFn_id_tensorMap, Category.id_comp] at hfirst
  unfold contractionTensorMap contractionTensorMapAtOldIndex
    recursiveContractionTensorMapAtOldIndex
    recursiveContractionMergedFactorsTensorMap
  rw [hfirst]
  simp only [test_rawContractionTargetTensorMap,
    TensorMapData.ofFn_tensorMap_comp, Category.assoc]
  rfl

theorem test_rawContractionTargetTransport_eqToHom
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    ∃ h : tensorModuleList
          (finFamilyList fun q ↦ recursiveMergedFactor
            (factorModule d) i (rawContractionFactor d i) q) =
        summandModule (d.contract i),
      test_rawContractionTargetTensorMap d i ≫
          (contractedFactorsOldIndexIso d i).hom = eqToHom h := by
  apply test_comp_eqToHom
  · exact ⟨congrArg tensorModuleList
        (congrArg finFamilyList (test_rawContractionTarget_eq d i)),
      test_rawContractionTargetTensorMap_eqToHom d i⟩
  · exact ⟨congrArg tensorModuleList
        (contractedFactorsOldIndex_eq d i), rfl⟩

theorem test_contractionTensorMap_raw_heq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    HEq (contractionTensorMap d i)
      (rawContractionAdjacentMergeData d i).tensorMap := by
  rw [test_contractionTensorMap_normal_form]
  obtain ⟨h, hh⟩ := test_rawContractionTargetTransport_eqToHom d i
  rw [hh]
  exact test_comp_eqToHom_heq
    (rawContractionAdjacentMergeData d i).tensorMap h

theorem test_rawSecondContractionFactorIso_inv_eqToHom
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    ∃ h : rawSecondContractionFactor d i j =
        contractedFactorAtOldIndex (d.contract i) j j,
      (test_rawSecondContractionFactorIso d i j).inv = eqToHom h := by
  unfold test_rawSecondContractionFactorIso
  simp only [Iso.trans_inv]
  apply test_comp_eqToHom
  · exact ⟨test_rawSecondContractionFactor_eq d i j,
      test_eqToIso_symm_inv_eqToHom
        (test_rawSecondContractionFactor_eq d i j)⟩
  · exact test_contractFactorAtOldIndexIso_inv_eqToHom (d.contract i) j

theorem test_rawSecondContractionTargetFactorMap_eqToHom
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j q : Fin (k + 1)) :
    ∃ h : recursiveMergedFactor
          (recursiveMergedFactor (factorModule d) i (rawContractionFactor d i)) j
          (rawSecondContractionFactor d i j) q =
        recursiveMergedFactor
          (recursiveMergedFactor (factorModule d) i
            (contractedFactorAtOldIndex d i i)) j
          (contractedFactorAtOldIndex (d.contract i) j j) q,
      test_rawSecondContractionTargetFactorMap d i j q = eqToHom h := by
  apply test_recursiveMergedFactorMap_eqToHom
  · exact fun r ↦ test_rawContractionMergedFactorMap_eqToHom d i r
  · exact test_rawSecondContractionFactorIso_inv_eqToHom d i j

def test_transportedSecondContractionTargetFactorMap
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j q : Fin (k + 1)) :
    Quiver.Hom
      (recursiveMergedFactor
        (recursiveMergedFactor (factorModule d) i
          (contractedFactorAtOldIndex d i i)) j
        (contractedFactorAtOldIndex (d.contract i) j j) q)
      (recursiveMergedFactor (factorModule (d.contract i)) j
        (contractedFactorAtOldIndex (d.contract i) j j) q) :=
  recursiveMergedFactorMap
    (recursiveMergedFactor (factorModule d) i
      (contractedFactorAtOldIndex d i i))
    (factorModule (d.contract i)) j
    (contractedFactorAtOldIndex (d.contract i) j j)
    (contractedFactorAtOldIndex (d.contract i) j j)
    (recursiveContractionMergedFactorMap d i)
    (𝟙 (contractedFactorAtOldIndex (d.contract i) j j)) q

theorem test_transportedSecondContractionTargetFactorMap_eqToHom
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j q : Fin (k + 1)) :
    ∃ h : recursiveMergedFactor
          (recursiveMergedFactor (factorModule d) i
            (contractedFactorAtOldIndex d i i)) j
          (contractedFactorAtOldIndex (d.contract i) j j) q =
        recursiveMergedFactor (factorModule (d.contract i)) j
          (contractedFactorAtOldIndex (d.contract i) j j) q,
      test_transportedSecondContractionTargetFactorMap d i j q = eqToHom h := by
  apply test_recursiveMergedFactorMap_eqToHom
  · exact fun r ↦ test_recursiveContractionMergedFactorMap_eqToHom d i r
  · exact ⟨rfl, rfl⟩

def test_rawContractionPairTargetFactorMap
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j q : Fin (k + 1)) :
    Quiver.Hom
      (recursiveMergedFactor
        (recursiveMergedFactor (factorModule d) i (rawContractionFactor d i)) j
        (rawSecondContractionFactor d i j) q)
      (contractedFactorAtOldIndex (d.contract i) j q) :=
  test_rawSecondContractionTargetFactorMap d i j q ≫
    test_transportedSecondContractionTargetFactorMap d i j q ≫
    recursiveContractionMergedFactorMap (d.contract i) j q

theorem test_rawContractionPairTargetFactorMap_eqToHom
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j q : Fin (k + 1)) :
    ∃ h : recursiveMergedFactor
          (recursiveMergedFactor (factorModule d) i (rawContractionFactor d i)) j
          (rawSecondContractionFactor d i j) q =
        contractedFactorAtOldIndex (d.contract i) j q,
      test_rawContractionPairTargetFactorMap d i j q = eqToHom h := by
  apply test_comp_eqToHom
  · exact test_rawSecondContractionTargetFactorMap_eqToHom d i j q
  · apply test_comp_eqToHom
    · exact test_transportedSecondContractionTargetFactorMap_eqToHom d i j q
    · exact test_recursiveContractionMergedFactorMap_eqToHom (d.contract i) j q

noncomputable def test_rawContractionPairTarget_eq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    (fun q ↦ recursiveMergedFactor
      (recursiveMergedFactor (factorModule d) i (rawContractionFactor d i)) j
      (rawSecondContractionFactor d i j) q) =
      contractedFactorAtOldIndex (d.contract i) j :=
  funext fun q ↦ Classical.choose
    (test_rawContractionPairTargetFactorMap_eqToHom d i j q)

theorem test_rawContractionPairTargetFactorMap_eqToHom_canonical
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j q : Fin (k + 1)) :
    test_rawContractionPairTargetFactorMap d i j q =
      eqToHom (congrFun (test_rawContractionPairTarget_eq d i j) q) := by
  obtain ⟨h, hh⟩ := test_rawContractionPairTargetFactorMap_eqToHom d i j q
  simpa only [Subsingleton.elim h
    (congrFun (test_rawContractionPairTarget_eq d i j) q)] using hh

def test_rawContractionPairTargetTensorMap
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j : Fin (k + 1)) :=
  (TensorMapData.ofFn
    (fun q ↦ recursiveMergedFactor
      (recursiveMergedFactor (factorModule d) i (rawContractionFactor d i)) j
      (rawSecondContractionFactor d i j) q)
    (contractedFactorAtOldIndex (d.contract i) j)
    (test_rawContractionPairTargetFactorMap d i j)).tensorMap

theorem test_rawContractionPairTargetTensorMap_eqToHom
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    test_rawContractionPairTargetTensorMap d i j =
      eqToHom (congrArg tensorModuleList
        (congrArg finFamilyList (test_rawContractionPairTarget_eq d i j))) := by
  exact test_tensorMapData_ofFn_eqToHom _ _
    (test_rawContractionPairTarget_eq d i j) _
    (test_rawContractionPairTargetFactorMap_eqToHom_canonical d i j)

theorem test_contractionPairTensorMap_normal_form
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    contractionTensorMap d i ≫ contractionTensorMap (d.contract i) j =
      (rawContractionAdjacentMergeData d i).tensorMap ≫
        (rawSecondContractionMergeData d i j).tensorMap ≫
        test_rawContractionPairTargetTensorMap d i j ≫
        (contractedFactorsOldIndexIso (d.contract i) j).hom := by
  have hfirst := (test_rawContractionAdjacentMerge_naturality d i).tensorMap_comm
  simp only [TensorMapData.ofFn_id_tensorMap, Category.id_comp] at hfirst
  unfold contractionTensorMap contractionTensorMapAtOldIndex
    recursiveContractionTensorMapAtOldIndex
    recursiveContractionMergedFactorsTensorMap
  simp only [Category.assoc]
  rw [hfirst]
  rw [show (contractedFactorsOldIndexIso d i).hom = 𝟙 _ from rfl]
  simp only [Category.id_comp]
  have hsource :
      (TensorMapData.ofFn
        (recursiveMergedFactor (factorModule d) i
          (contractedFactorAtOldIndex d i i))
        (contractedFactorAtOldIndex d i)
        (recursiveContractionMergedFactorMap d i)).tensorMap =
      (TensorMapData.ofFn
        (recursiveMergedFactor (factorModule d) i
          (contractedFactorAtOldIndex d i i))
        (factorModule (d.contract i))
        (recursiveContractionMergedFactorMap d i)).tensorMap := rfl
  rw [hsource]
  slice_lhs 3 4 =>
    rw [(transportedSecondContractionMerge_naturality d i j).tensorMap_comm]
  slice_lhs 2 3 =>
    rw [(test_rawSecondContractionMerge_naturality d i j).tensorMap_comm]
  simp only [test_rawContractionPairTargetTensorMap,
    TensorMapData.ofFn_tensorMap_comp, Category.assoc]
  rfl

theorem test_eqToHom_heq_id {A B : ModuleCat.{0} ℤ} (h : A = B) :
    HEq (eqToHom h) (𝟙 A) := by
  subst B
  rfl

theorem test_rawContractionPairTargetTransport_eqToHom
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    ∃ h : tensorModuleList
          (finFamilyList fun q ↦ recursiveMergedFactor
            (recursiveMergedFactor (factorModule d) i (rawContractionFactor d i)) j
            (rawSecondContractionFactor d i j) q) =
        summandModule ((d.contract i).contract j),
      test_rawContractionPairTargetTensorMap d i j ≫
          (contractedFactorsOldIndexIso (d.contract i) j).hom = eqToHom h := by
  apply test_comp_eqToHom
  · exact ⟨congrArg tensorModuleList
        (congrArg finFamilyList (test_rawContractionPairTarget_eq d i j)),
      test_rawContractionPairTargetTensorMap_eqToHom d i j⟩
  · exact ⟨congrArg tensorModuleList
        (contractedFactorsOldIndex_eq (d.contract i) j), rfl⟩

theorem test_contractionPairTensorMap_raw_heq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    HEq (contractionTensorMap d i ≫ contractionTensorMap (d.contract i) j)
      ((rawContractionAdjacentMergeData d i).tensorMap ≫
        (rawSecondContractionMergeData d i j).tensorMap) := by
  rw [test_contractionPairTensorMap_normal_form]
  obtain ⟨h, hh⟩ := test_rawContractionPairTargetTransport_eqToHom d i j
  rw [hh]
  simpa only [Category.assoc] using test_comp_eqToHom_heq
    ((rawContractionAdjacentMergeData d i).tensorMap ≫
      (rawSecondContractionMergeData d i j).tensorMap)
    h

theorem test_summandModuleCastWordIso_hom_eqToHom
    {X Y : ComplexCategory} {w v : DrinfeldWord X Y} {n : ℤ}
    (h : w = v) (d : DegreeProfile w n) :
    ∃ hM : summandModule d = summandModule (d.castWord h),
      (summandModuleCastWordIso h d).hom = eqToHom hM := by
  subst v
  exact ⟨rfl, rfl⟩

def test_contractionPairTargetIso
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    summandModule ((d.contract i).contract j) ≅
      summandModule ((d.contract (i.succAbove j)).contract (j.predAbove i)) :=
  summandModuleCastWordIso (eraseIntermediate_twice_swap intermediate i j)
      ((d.contract i).contract j) ≪≫
    eqToIso (congrArg summandModule
      (DegreeProfile.contract_contract_swap intermediate d i j))

theorem test_contractionPairTargetIso_hom_eqToHom
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    ∃ h : summandModule ((d.contract i).contract j) =
        summandModule ((d.contract (i.succAbove j)).contract (j.predAbove i)),
      (test_contractionPairTargetIso d i j).hom = eqToHom h := by
  unfold test_contractionPairTargetIso
  simp only [Iso.trans_hom]
  obtain ⟨h₁, hh₁⟩ := test_summandModuleCastWordIso_hom_eqToHom
    (eraseIntermediate_twice_swap intermediate i j) ((d.contract i).contract j)
  exact test_comp_eqToHom _ _ ⟨h₁, hh₁⟩
    ⟨congrArg summandModule
      (DegreeProfile.contract_contract_swap intermediate d i j), rfl⟩

theorem test_contractionPairTargetIso_hom_heq_id
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    HEq (test_contractionPairTargetIso d i j).hom
      (𝟙 (summandModule ((d.contract i).contract j))) := by
  obtain ⟨h, hh⟩ := test_contractionPairTargetIso_hom_eqToHom d i j
  rw [hh]
  exact test_eqToHom_heq_id h

theorem test_contractionPairTensorMap_swap
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    contractionTensorMap d i ≫ contractionTensorMap (d.contract i) j ≫
        (test_contractionPairTargetIso d i j).hom =
      contractionTensorMap d (i.succAbove j) ≫
        contractionTensorMap (d.contract (i.succAbove j)) (j.predAbove i) := by
  obtain ⟨h, hh⟩ := test_contractionPairTargetIso_hom_eqToHom d i j
  rw [hh]
  apply eq_of_heq
  exact (test_comp_eqToHom_heq
      (contractionTensorMap d i ≫ contractionTensorMap (d.contract i) j)
      h).trans
    ((test_contractionPairTensorMap_raw_heq d i j).trans
      ((rawContractionPair_tensorMap_heq d i j).trans
        (test_contractionPairTensorMap_raw_heq d (i.succAbove j)
          (j.predAbove i)).symm))

theorem test_contractionPairTensorMap_heq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    HEq (contractionTensorMap d i ≫ contractionTensorMap (d.contract i) j)
      (contractionTensorMap d (i.succAbove j) ≫
        contractionTensorMap (d.contract (i.succAbove j)) (j.predAbove i)) :=
  (test_contractionPairTensorMap_raw_heq d i j).trans
    ((rawContractionPair_tensorMap_heq d i j).trans
      (test_contractionPairTensorMap_raw_heq d (i.succAbove j)
        (j.predAbove i)).symm)

end LeanLCAExactChallenge.Infinity.MetrizableBoundedComplexes.DrinfeldWord
