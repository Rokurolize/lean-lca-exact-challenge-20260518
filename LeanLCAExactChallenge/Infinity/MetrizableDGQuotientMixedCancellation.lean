/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientPairCancellation

/-! # Mixed internal and contraction differential cancellation -/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge.Infinity.MetrizableBoundedComplexes.DrinfeldWord

open CategoryTheory CategoryTheory.MonoidalCategory

theorem factorDifferential_eqToHom_of_ne
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (q r : Fin (w.length + 1)) (h : q ≠ r) :
    ∃ hM : factorModule d r = factorModule (d.raise q) r,
      factorDifferential d q r = eqToHom hM := by
  have hM : factorModule d r = factorModule (d.raise q) r := by
    simp [factorModule, DegreeProfile.raise, Ne.symm h]
  have hfd : HEq (factorDifferential d q r) (𝟙 (factorModule d r)) := by
    simpa [factorDifferential, DegreeProfile.raise, factorModule, Ne.symm h] using
      (eqToHom_heq_id_dom (factorModule d r) (factorModule (d.raise q) r) hM)
  exact ⟨hM, eq_of_heq (hfd.trans (test_eqToHom_heq_id hM).symm)⟩

theorem recursiveMergedFactorMap_heq_mergedFactorMap : {k : ℕ} →
    (M N : Fin (k + 1) → ModuleCat.{0} ℤ) → (i : Fin k) →
    (P P' : ModuleCat.{0} ℤ) →
    (a : (j : Fin (k + 1)) → M j ⟶ N j) → (g : P ⟶ P') →
    (j : Fin k) →
    HEq (recursiveMergedFactorMap M N i P P' a g j)
      (mergedFactorMap M N i P P' a g j)
  | 0, _, _, i, _, _, _, _, _ => Fin.elim0 i
  | k + 1, M, N, i, P, P', a, g, j => by
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero => simp [recursiveMergedFactorMap, mergedFactorMap, mergedFactor]
          | succ j => simp [recursiveMergedFactorMap, mergedFactorMap, mergedFactor]
      | succ q =>
          cases j using Fin.cases with
          | zero =>
              simp [recursiveMergedFactorMap, mergedFactorMap, mergedFactor]
          | succ j =>
              apply (recursiveMergedFactorMap_heq_mergedFactorMap
                (fun r : Fin (k + 1) ↦ M r.succ)
                (fun r : Fin (k + 1) ↦ N r.succ) q P P'
                (fun r ↦ a r.succ) g j).trans
              by_cases hlt : j < q
              · simp [mergedFactorMap, mergedFactor, hlt]
              · by_cases heq : j = q
                · subst j
                  simp [mergedFactorMap, mergedFactor]
                · simp [mergedFactorMap, mergedFactor, hlt, heq]

theorem rawContractionFactor_raise_of_ne
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) (q : Fin (w.length + 1))
    (hleft : q ≠ i.castSucc) (hright : q ≠ i.succ) :
    rawContractionFactor d i = rawContractionFactor (d.raise q) i := by
  unfold rawContractionFactor
  simp [DegreeProfile.raise, Ne.symm hleft, Ne.symm hright]

def rawContractionRaisedFactorMap
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) (q : Fin (w.length + 1))
    (hleft : q ≠ i.castSucc) (hright : q ≠ i.succ) :
    Quiver.Hom (rawContractionFactor d i) (rawContractionFactor (d.raise q) i) :=
  eqToHom (rawContractionFactor_raise_of_ne d i q hleft hright)

def rawContractionMergedFactorDifferential
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) (q : Fin (w.length + 1))
    (hleft : q ≠ i.castSucc) (hright : q ≠ i.succ) :
    (r : Fin w.length) → Quiver.Hom
      (recursiveMergedFactor (factorModule d) i (rawContractionFactor d i) r)
      (recursiveMergedFactor (factorModule (d.raise q)) i
        (rawContractionFactor (d.raise q) i) r) :=
  recursiveMergedFactorMap
    (factorModule d) (factorModule (d.raise q)) i
    (rawContractionFactor d i) (rawContractionFactor (d.raise q) i)
    (factorDifferential d q)
    (rawContractionRaisedFactorMap d i q hleft hright)

theorem rawContractionAdjacentMerge_naturality_of_ne
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) (q : Fin (w.length + 1))
    (hleft : q ≠ i.castSucc) (hright : q ≠ i.succ) :
    AdjacentMergeNaturality
      (rawContractionAdjacentMergeData d i)
      (rawContractionAdjacentMergeData (d.raise q) i)
      (TensorMapData.ofFn (factorModule d) (factorModule (d.raise q))
        (factorDifferential d q))
      (TensorMapData.ofFn
        (recursiveMergedFactor (factorModule d) i (rawContractionFactor d i))
        (recursiveMergedFactor (factorModule (d.raise q)) i
          (rawContractionFactor (d.raise q) i))
      (rawContractionMergedFactorDifferential d i q hleft hright)) := by
  apply recursiveAdjacentMergeDataOfFn_naturality
  obtain ⟨hA, hhA⟩ := factorDifferential_eqToHom_of_ne d q i.castSucc hleft
  obtain ⟨hB, hhB⟩ := factorDifferential_eqToHom_of_ne d q i.succ hright
  rw [hhA, hhB]
  unfold rawContractionRaisedFactorMap
  exact test_tensor_comp_transport_of_heq
    hA hB
    (rawContractionFactor_raise_of_ne d i q hleft hright)
    (adjacentFactorComposition d i)
    (adjacentFactorComposition (d.raise q) i)
    (by
      unfold adjacentFactorComposition factorModule
      apply dgCochainCompTensorOfEq_heq
      · rfl
      · rfl
      · rfl
      · rfl
      · simp [DegreeProfile.raise, Ne.symm hleft]
      · simp [DegreeProfile.raise, Ne.symm hright]
      · simp [DegreeProfile.raise, Ne.symm hleft, Ne.symm hright])

theorem dgHomDifferential_heq
    {K₁ L₁ K₂ L₂ : ComplexCategory} {p₁ q₁ p₂ q₂ : ℤ}
    (hK : K₁ = K₂) (hL : L₁ = L₂) (hp : p₁ = p₂) (hq : q₁ = q₂) :
    HEq ((dgHomZModuleCochainComplex K₁ L₁).d p₁ q₁)
      ((dgHomZModuleCochainComplex K₂ L₂).d p₂ q₂) := by
  subst K₂
  subst L₂
  subst p₂
  subst q₂
  rfl

theorem factorDifferential_contract_before_heq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length)
    (j : Fin ((eraseIntermediate w i).length + 1))
    (h : eraseFactorIndex w i j < i) :
    HEq (factorDifferential d (eraseFactorIndex w i j).castSucc
        (eraseFactorIndex w i j).castSucc)
      (factorDifferential (d.contract i) j j) := by
  unfold factorDifferential
  simp only [eq_self, dif_pos]
  apply dgHomDifferential_heq
  · exact (eraseIntermediate_arrowSource_of_before w i j h).symm
  · exact (eraseIntermediate_arrowTarget_of_before w i j h).symm
  · exact (contract_arrowDegree_of_before d i j h).symm
  · simp [DegreeProfile.raise, contract_arrowDegree_of_before d i j h]

theorem factorDifferential_contract_after_heq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length)
    (j : Fin ((eraseIntermediate w i).length + 1))
    (h : i < eraseFactorIndex w i j) :
    HEq (factorDifferential d (eraseFactorIndex w i j).succ
        (eraseFactorIndex w i j).succ)
      (factorDifferential (d.contract i) j j) := by
  unfold factorDifferential
  simp only [eq_self, dif_pos]
  apply dgHomDifferential_heq
  · exact (eraseIntermediate_arrowSource_of_after w i j h).symm
  · exact (eraseIntermediate_arrowTarget_of_after w i j h).symm
  · exact (contract_arrowDegree_of_after d i j h).symm
  · simp [DegreeProfile.raise, contract_arrowDegree_of_after d i j h]

theorem equalityTransport_heq_of_source_eq
    {A B C D : ModuleCat.{0} ℤ} (hAB : A = B) (hCD : C = D) (hAC : A = C) :
    HEq (eqToHom hAB) (eqToHom hCD) :=
  (test_eqToHom_heq_id hAB).trans
    ((congr_arg_heq (fun M : ModuleCat.{0} ℤ ↦ 𝟙 M) hAC).trans
      (test_eqToHom_heq_id hCD).symm)

theorem factorModule_contract_before_eq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length)
    (j : Fin ((eraseIntermediate w i).length + 1))
    (h : eraseFactorIndex w i j < i) :
    factorModule d (eraseFactorIndex w i j).castSucc =
      factorModule (d.contract i) j := by
  unfold factorModule
  rw [eraseIntermediate_arrowSource_of_before w i j h,
    eraseIntermediate_arrowTarget_of_before w i j h,
    contract_arrowDegree_of_before d i j h]

theorem factorModule_contract_after_eq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length)
    (j : Fin ((eraseIntermediate w i).length + 1))
    (h : i < eraseFactorIndex w i j) :
    factorModule d (eraseFactorIndex w i j).succ =
      factorModule (d.contract i) j := by
  unfold factorModule
  rw [eraseIntermediate_arrowSource_of_after w i j h,
    eraseIntermediate_arrowTarget_of_after w i j h,
    contract_arrowDegree_of_after d i j h]

theorem rawContractionFactor_eq_contractPosition
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    rawContractionFactor d i =
      factorModule (d.contract i) (erasePosition w i) := by
  unfold rawContractionFactor factorModule
  rw [eraseIntermediate_arrowSource_at w i,
    eraseIntermediate_arrowTarget_at w i, contract_arrowDegree_at d i]

theorem mergedFactorMap_before_heq
    {k : ℕ} (M N : Fin (k + 1) → ModuleCat.{0} ℤ) (i : Fin k)
    (P P' : ModuleCat.{0} ℤ) (a : (j : Fin (k + 1)) → M j ⟶ N j)
    (g : P ⟶ P') (j : Fin k) (h : j < i) :
    HEq (mergedFactorMap M N i P P' a g j) (a j.castSucc) := by
  simp [mergedFactorMap, h]

theorem mergedFactorMap_at_heq
    {k : ℕ} (M N : Fin (k + 1) → ModuleCat.{0} ℤ) (i : Fin k)
    (P P' : ModuleCat.{0} ℤ) (a : (j : Fin (k + 1)) → M j ⟶ N j)
    (g : P ⟶ P') :
    HEq (mergedFactorMap M N i P P' a g i) g := by
  simp [mergedFactorMap]

theorem mergedFactorMap_after_heq
    {k : ℕ} (M N : Fin (k + 1) → ModuleCat.{0} ℤ) (i : Fin k)
    (P P' : ModuleCat.{0} ℤ) (a : (j : Fin (k + 1)) → M j ⟶ N j)
    (g : P ⟶ P') (j : Fin k) (hlt : ¬j < i) (heq : j ≠ i) :
    HEq (mergedFactorMap M N i P P' a g j) (a j.succ) := by
  simp [mergedFactorMap, hlt, heq]

theorem rawContractionMergedFactorDifferential_surviving_heq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length)
    (j r : Fin ((eraseIntermediate w i).length + 1))
    (hj : j ≠ erasePosition w i) :
    HEq
      (rawContractionMergedFactorDifferential d i
        (survivingOldFactorIndex w i j)
        (survivingOldFactorIndex_ne_left w i j)
        (fun h ↦ hj ((survivingOldFactorIndex_eq_right_iff w i j).mp h))
        (eraseFactorIndex w i r))
      (factorDifferential (d.contract i) j r) := by
  let q := survivingOldFactorIndex w i j
  have hleft : q ≠ i.castSucc := survivingOldFactorIndex_ne_left w i j
  have hright : q ≠ i.succ :=
    fun h ↦ hj ((survivingOldFactorIndex_eq_right_iff w i j).mp h)
  apply (recursiveMergedFactorMap_heq_mergedFactorMap
    (factorModule d) (factorModule (d.raise q)) i
    (rawContractionFactor d i) (rawContractionFactor (d.raise q) i)
    (factorDifferential d q)
    (rawContractionRaisedFactorMap d i q hleft hright)
    (eraseFactorIndex w i r)).trans
  by_cases hbefore : eraseFactorIndex w i r < i
  · have hrindex := survivingOldFactorIndex_of_before w i r hbefore
    apply (mergedFactorMap_before_heq
      (factorModule d) (factorModule (d.raise q)) i
      (rawContractionFactor d i) (rawContractionFactor (d.raise q) i)
      (factorDifferential d q)
      (rawContractionRaisedFactorMap d i q hleft hright)
      (eraseFactorIndex w i r) hbefore).trans
    by_cases hrj : r = j
    · subst r
      have hqeq : q = (eraseFactorIndex w i j).castSucc := by
        exact survivingOldFactorIndex_of_before w i j hbefore
      exact (congr_arg_heq
        (fun q' ↦ factorDifferential d q' (eraseFactorIndex w i j).castSucc)
        hqeq).trans (factorDifferential_contract_before_heq d i j hbefore)
    · have hq : q ≠ (eraseFactorIndex w i r).castSucc := by
        rw [← hrindex]
        intro h
        exact hrj ((survivingOldFactorIndex_injective w i) h.symm)
      obtain ⟨hAB, hmap⟩ := factorDifferential_eqToHom_of_ne d q
        (eraseFactorIndex w i r).castSucc hq
      obtain ⟨hCD, htarget⟩ := factorDifferential_eqToHom_of_ne
        (d.contract i) j r (Ne.symm hrj)
      rw [hmap, htarget]
      exact
        equalityTransport_heq_of_source_eq hAB hCD
          (factorModule_contract_before_eq d i r hbefore)
  · by_cases hat : eraseFactorIndex w i r = i
    · have hr : r = erasePosition w i := by
        apply Fin.ext
        exact congrArg (fun x : Fin w.length ↦ x.val) hat
      subst r
      apply (mergedFactorMap_at_heq
        (factorModule d) (factorModule (d.raise q)) i
        (rawContractionFactor d i) (rawContractionFactor (d.raise q) i)
        (factorDifferential d q)
        (rawContractionRaisedFactorMap d i q hleft hright)).trans
      obtain ⟨hCD, htarget⟩ := factorDifferential_eqToHom_of_ne
        (d.contract i) j (erasePosition w i) hj
      rw [htarget]
      unfold rawContractionRaisedFactorMap
      exact equalityTransport_heq_of_source_eq
          (rawContractionFactor_raise_of_ne d i q hleft hright) hCD
          (rawContractionFactor_eq_contractPosition d i)
    · have hafter : i < eraseFactorIndex w i r := by omega
      have hrindex := survivingOldFactorIndex_of_after w i r hafter
      apply (mergedFactorMap_after_heq
        (factorModule d) (factorModule (d.raise q)) i
        (rawContractionFactor d i) (rawContractionFactor (d.raise q) i)
        (factorDifferential d q)
        (rawContractionRaisedFactorMap d i q hleft hright)
        (eraseFactorIndex w i r) hbefore hat).trans
      by_cases hrj : r = j
      · subst r
        have hqeq : q = (eraseFactorIndex w i j).succ := by
          exact survivingOldFactorIndex_of_after w i j hafter
        exact (congr_arg_heq
          (fun q' ↦ factorDifferential d q' (eraseFactorIndex w i j).succ)
          hqeq).trans (factorDifferential_contract_after_heq d i j hafter)
      · have hq : q ≠ (eraseFactorIndex w i r).succ := by
          rw [← hrindex]
          intro h
          exact hrj ((survivingOldFactorIndex_injective w i) h.symm)
        obtain ⟨hAB, hmap⟩ := factorDifferential_eqToHom_of_ne d q
          (eraseFactorIndex w i r).succ hq
        obtain ⟨hCD, htarget⟩ := factorDifferential_eqToHom_of_ne
          (d.contract i) j r (Ne.symm hrj)
        rw [hmap, htarget]
        exact
          equalityTransport_heq_of_source_eq hAB hCD
            (factorModule_contract_after_eq d i r hafter)

theorem TensorMapData.ofFn_tensorMap_heq_of_pointwise
    {k : ℕ} (M₁ N₁ M₂ N₂ : Fin k → ModuleCat.{0} ℤ)
    (f₁ : (i : Fin k) → M₁ i ⟶ N₁ i)
    (f₂ : (i : Fin k) → M₂ i ⟶ N₂ i)
    (hM : M₁ = M₂) (hN : N₁ = N₂)
    (h : ∀ i, HEq (f₁ i) (f₂ i)) :
    HEq (TensorMapData.ofFn M₁ N₁ f₁).tensorMap
      (TensorMapData.ofFn M₂ N₂ f₂).tensorMap := by
  subst M₂
  subst N₂
  have hf : f₁ = f₂ := by
    funext i
    exact eq_of_heq (h i)
  subst f₂
  rfl

theorem tensorHom_heq
    {A B C D A' B' C' D' : ModuleCat.{0} ℤ}
    {f : A ⟶ B} {g : C ⟶ D} {f' : A' ⟶ B'} {g' : C' ⟶ D'}
    (hA : A = A') (hB : B = B') (hC : C = C') (hD : D = D')
    (hf : HEq f f') (hg : HEq g g') : HEq (f ⊗ₘ g) (f' ⊗ₘ g') := by
  subst A'
  subst B'
  subst C'
  subst D'
  rw [eq_of_heq hf, eq_of_heq hg]

def contractedInternalTensorMapAtOldIndex
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length)
    (j : Fin ((eraseIntermediate w i).length + 1)) :
    Quiver.Hom
      (tensorModuleList (finFamilyList (contractedFactorAtOldIndex d i)))
      (tensorModuleList (finFamilyList
        (fun r ↦ factorModule ((d.contract i).raise j)
          (uneraseFactorIndex w i r)))) :=
  (TensorMapData.ofFn
    (contractedFactorAtOldIndex d i)
    (fun r ↦ factorModule ((d.contract i).raise j)
      (uneraseFactorIndex w i r))
    (fun r ↦ factorDifferential (d.contract i) j
      (uneraseFactorIndex w i r))).tensorMap

theorem rawContractionMergedDifferentialTensorMap_heq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length)
    (j : Fin ((eraseIntermediate w i).length + 1))
    (hj : j ≠ erasePosition w i) :
    let q := survivingOldFactorIndex w i j
    let hleft := survivingOldFactorIndex_ne_left w i j
    let hright : q ≠ i.succ :=
      fun h ↦ hj ((survivingOldFactorIndex_eq_right_iff w i j).mp h)
    HEq
      (TensorMapData.ofFn
        (recursiveMergedFactor (factorModule d) i (rawContractionFactor d i))
        (recursiveMergedFactor (factorModule (d.raise q)) i
          (rawContractionFactor (d.raise q) i))
        (rawContractionMergedFactorDifferential d i q hleft hright)).tensorMap
      (contractedInternalTensorMapAtOldIndex d i j) := by
  dsimp only
  apply TensorMapData.ofFn_tensorMap_heq_of_pointwise
  · exact test_rawContractionTarget_eq d i
  · exact (test_rawContractionTarget_eq
      (d.raise (survivingOldFactorIndex w i j)) i).trans
      (congrArg
        (fun e ↦ fun r ↦ factorModule e (uneraseFactorIndex w i r))
        (DegreeProfile.raise_surviving_contract d i j))
  · intro r
    have h := rawContractionMergedFactorDifferential_surviving_heq
      d i j (uneraseFactorIndex w i r) hj
    rw [eraseFactorIndex_uneraseFactorIndex] at h
    exact h

theorem contractedInternalTensorMapAtOldIndex_heq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length)
    (j : Fin ((eraseIntermediate w i).length + 1)) :
    HEq (contractedInternalTensorMapAtOldIndex d i j)
      (internalDifferentialTensorMap (d.contract i) j) := by
  cases w with
  | mk k intermediate =>
      cases k with
      | zero => exact Fin.elim0 i
      | succ k =>
          cases k with
          | zero =>
              fin_cases i
              fin_cases j
              rfl
          | succ k => rfl

theorem rawContractionSummand_eq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    tensorModuleList (finFamilyList
      (recursiveMergedFactor (factorModule d) i (rawContractionFactor d i))) =
      summandModule (d.contract i) :=
  (congrArg tensorModuleList
    (congrArg finFamilyList (test_rawContractionTarget_eq d i))).trans
    (congrArg tensorModuleList (contractedFactorsOldIndex_eq d i))

def rawContractionMergedDifferentialTensorMap
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length)
    (j : Fin ((eraseIntermediate w i).length + 1))
    (hj : j ≠ erasePosition w i) :=
  let q := survivingOldFactorIndex w i j
  let hleft := survivingOldFactorIndex_ne_left w i j
  let hright : q ≠ i.succ :=
    fun h ↦ hj ((survivingOldFactorIndex_eq_right_iff w i j).mp h)
  (TensorMapData.ofFn
    (recursiveMergedFactor (factorModule d) i (rawContractionFactor d i))
    (recursiveMergedFactor (factorModule (d.raise q)) i
      (rawContractionFactor (d.raise q) i))
    (rawContractionMergedFactorDifferential d i q hleft hright)).tensorMap

theorem rawContractionMergedDifferentialTensorMap_internal_heq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length)
    (j : Fin ((eraseIntermediate w i).length + 1))
    (hj : j ≠ erasePosition w i) :
    HEq (rawContractionMergedDifferentialTensorMap d i j hj)
      (internalDifferentialTensorMap (d.contract i) j) :=
  (rawContractionMergedDifferentialTensorMap_heq d i j hj).trans
    (contractedInternalTensorMapAtOldIndex_heq d i j)

theorem internalContractionTensorMap_comm_heq_of_surviving
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length)
    (j : Fin ((eraseIntermediate w i).length + 1))
    (hj : j ≠ erasePosition w i) :
    let q := survivingOldFactorIndex w i j
    HEq
      (internalDifferentialTensorMap d q ≫
        contractionTensorMap (d.raise q) i)
      (contractionTensorMap d i ≫
        internalDifferentialTensorMap (d.contract i) j) := by
  dsimp only
  let q := survivingOldFactorIndex w i j
  have hleft : q ≠ i.castSucc := survivingOldFactorIndex_ne_left w i j
  have hright : q ≠ i.succ :=
    fun h ↦ hj ((survivingOldFactorIndex_eq_right_iff w i j).mp h)
  have htarget :
      summandModule ((d.raise q).contract i) =
        summandModule ((d.contract i).raise j) :=
    congrArg summandModule (DegreeProfile.raise_surviving_contract d i j)
  have hrawTarget :
      tensorModuleList (finFamilyList
        (recursiveMergedFactor (factorModule (d.raise q)) i
          (rawContractionFactor (d.raise q) i))) =
        summandModule ((d.contract i).raise j) :=
    (rawContractionSummand_eq (d.raise q) i).trans htarget
  have hleftRaw : HEq
      (internalDifferentialTensorMap d q ≫
        contractionTensorMap (d.raise q) i)
      (internalDifferentialTensorMap d q ≫
        (rawContractionAdjacentMergeData (d.raise q) i).tensorMap) := by
    exact CategoryTheory.heq_comp rfl rfl
      (rawContractionSummand_eq (d.raise q) i).symm
      (by rfl)
      (test_contractionTensorMap_raw_heq (d.raise q) i)
  have hnatural :=
    (rawContractionAdjacentMerge_naturality_of_ne d i q hleft hright).tensorMap_comm
  have hrightRaw : HEq
      ((rawContractionAdjacentMergeData d i).tensorMap ≫
        rawContractionMergedDifferentialTensorMap d i j hj)
      (contractionTensorMap d i ≫
        internalDifferentialTensorMap (d.contract i) j) := by
    exact CategoryTheory.heq_comp rfl (rawContractionSummand_eq d i) hrawTarget
      (test_contractionTensorMap_raw_heq d i).symm
      (rawContractionMergedDifferentialTensorMap_internal_heq d i j hj)
  exact hleftRaw.trans (heq_of_eq hnatural) |>.trans hrightRaw

theorem DegreeProfile.mixedCoefficient_surviving
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length)
    (j : Fin ((eraseIntermediate w i).length + 1))
    (hj : j ≠ erasePosition w i) :
    d.internalSign (survivingOldFactorIndex w i j) *
        (d.raise (survivingOldFactorIndex w i j)).contractionSign i =
      -(d.contractionSign i * (d.contract i).internalSign j) := by
  by_cases hbefore : eraseFactorIndex w i j < i
  · rw [survivingOldFactorIndex_of_before w i j hbefore,
      ← uneraseFactorIndex_eraseFactorIndex w i j]
    exact DegreeProfile.mixedCoefficient_of_lt d i
      (eraseFactorIndex w i j) hbefore
  · have hne : eraseFactorIndex w i j ≠ i := by
      intro h
      apply hj
      apply Fin.ext
      exact congrArg (fun q : Fin w.length ↦ q.val) h
    have hafter : i < eraseFactorIndex w i j := by omega
    rw [survivingOldFactorIndex_of_after w i j hafter,
      ← uneraseFactorIndex_eraseFactorIndex w i j]
    exact DegreeProfile.mixedCoefficient_of_gt d i
      (eraseFactorIndex w i j) hafter

theorem DegreeProfile.raise_right_contract
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    (d.raise i.succ).contract i =
      (d.contract i).raise (erasePosition w i) := by
  have hq : survivingOldFactorIndex w i (erasePosition w i) = i.succ :=
    (survivingOldFactorIndex_eq_right_iff w i (erasePosition w i)).mpr rfl
  rw [← hq]
  exact DegreeProfile.raise_surviving_contract d i (erasePosition w i)

def rightInternalContractionToMergedTarget
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    Quiver.Hom (summandModule d)
      (summandModule ((d.contract i).raise (erasePosition w i))) :=
  internalDifferentialTensorMap d i.succ ≫
    contractionTensorMap (d.raise i.succ) i ≫
    eqToHom (congrArg summandModule (DegreeProfile.raise_right_contract d i))

def leftInternalContractionToMergedTarget
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    Quiver.Hom (summandModule d)
      (summandModule ((d.contract i).raise (erasePosition w i))) :=
  internalDifferentialTensorMap d i.castSucc ≫
    contractionTensorMap (d.raise i.castSucc) i ≫
    eqToHom (congrArg summandModule (DegreeProfile.raise_left_contract d i))

theorem AdjacentMergeData.head_tensorMap_add
    {M N P : ModuleCat.{0} ℤ} {Ms : List (ModuleCat.{0} ℤ)}
    (f g : Quiver.Hom (M ⊗ N) P) :
    (@AdjacentMergeData.head M N P Ms (f + g)).tensorMap =
      (@AdjacentMergeData.head M N P Ms f).tensorMap +
        (@AdjacentMergeData.head M N P Ms g).tensorMap := by
  simp [AdjacentMergeData.tensorMap, Preadditive.comp_add]

theorem AdjacentMergeData.head_tensorMap_zsmul
    {M N P : ModuleCat.{0} ℤ} {Ms : List (ModuleCat.{0} ℤ)}
    (c : ℤ) (f : Quiver.Hom (M ⊗ N) P) :
    (@AdjacentMergeData.head M N P Ms (c • f)).tensorMap =
      c • (@AdjacentMergeData.head M N P Ms f).tensorMap := by
  change (α_ M N (tensorModuleList Ms)).inv ≫
      ((tensoringRight (ModuleCat.{0} ℤ)).obj (tensorModuleList Ms)).map (c • f) = _
  rw [Functor.map_zsmul, Preadditive.comp_zsmul]
  rfl

def TensorMapData.identity : (Ms : List (ModuleCat.{0} ℤ)) → TensorMapData Ms Ms
  | [] => .nil
  | M :: Ms => .cons (𝟙 M) (TensorMapData.identity Ms)

@[simp]
theorem TensorMapData.identity_tensorMap : (Ms : List (ModuleCat.{0} ℤ)) →
    (TensorMapData.identity Ms).tensorMap = 𝟙 (tensorModuleList Ms)
  | [] => rfl
  | M :: Ms => by
      simp only [TensorMapData.identity, TensorMapData.tensorMap,
        TensorMapData.identity_tensorMap Ms]
      exact MonoidalCategory.id_tensorHom_id
        (C := ModuleCat.{0} ℤ) M (tensorModuleList Ms)

theorem AdjacentMergeData.head_tensorMap_leibniz
    {M N M' N' P P' : ModuleCat.{0} ℤ}
    {Ms : List (ModuleCat.{0} ℤ)}
    (f : M ⊗ N ⟶ P) (fR : M ⊗ N' ⟶ P') (fL : M' ⊗ N ⟶ P')
    (a : M ⟶ M') (b : N ⟶ N') (g : P ⟶ P') (c : ℤ)
    (h : f ≫ g = (𝟙 M ⊗ₘ b) ≫ fR + c • ((a ⊗ₘ 𝟙 N) ≫ fL)) :
    (@AdjacentMergeData.head M N P Ms f).tensorMap ≫
        (TensorMapData.cons g (TensorMapData.identity Ms)).tensorMap =
      (TensorMapData.cons (𝟙 M)
          (TensorMapData.cons b (TensorMapData.identity Ms))).tensorMap ≫
          (@AdjacentMergeData.head M N' P' Ms fR).tensorMap +
        c • ((TensorMapData.cons a
          (TensorMapData.cons (𝟙 N) (TensorMapData.identity Ms))).tensorMap ≫
          (@AdjacentMergeData.head M' N P' Ms fL).tensorMap) := by
  have htarget := (AdjacentMergeNaturality.head f (f ≫ g)
    (𝟙 M) (𝟙 N) g (TensorMapData.identity Ms) (by simp)).tensorMap_comm
  have hright := (AdjacentMergeNaturality.head ((𝟙 M ⊗ₘ b) ≫ fR) fR
    (𝟙 M) b (𝟙 P') (TensorMapData.identity Ms) (by simp)).tensorMap_comm
  have hleft := (AdjacentMergeNaturality.head ((a ⊗ₘ 𝟙 N) ≫ fL) fL
    a (𝟙 N) (𝟙 P') (TensorMapData.identity Ms) (by simp)).tensorMap_comm
  change (TensorMapData.identity (M :: N :: Ms)).tensorMap ≫
      (@AdjacentMergeData.head M N P' Ms (f ≫ g)).tensorMap = _ at htarget
  rw [TensorMapData.identity_tensorMap, Category.id_comp] at htarget
  change _ = (@AdjacentMergeData.head M N P' Ms
      ((𝟙 M ⊗ₘ b) ≫ fR)).tensorMap ≫
        (TensorMapData.identity (P' :: Ms)).tensorMap at hright
  rw [TensorMapData.identity_tensorMap, Category.comp_id] at hright
  change _ = (@AdjacentMergeData.head M N P' Ms
      ((a ⊗ₘ 𝟙 N) ≫ fL)).tensorMap ≫
        (TensorMapData.identity (P' :: Ms)).tensorMap at hleft
  rw [TensorMapData.identity_tensorMap, Category.comp_id] at hleft
  have htarget' :
      (@AdjacentMergeData.head M N P' Ms (f ≫ g)).tensorMap =
        (@AdjacentMergeData.head M N P Ms f).tensorMap ≫
          (TensorMapData.cons g (TensorMapData.identity Ms)).tensorMap := by
    exact htarget
  have hright' :
      (TensorMapData.cons (𝟙 M)
          (TensorMapData.cons b (TensorMapData.identity Ms))).tensorMap ≫
          (@AdjacentMergeData.head M N' P' Ms fR).tensorMap =
        (@AdjacentMergeData.head M N P' Ms ((𝟙 M ⊗ₘ b) ≫ fR)).tensorMap := by
    exact hright
  have hleft' :
      (TensorMapData.cons a
          (TensorMapData.cons (𝟙 N) (TensorMapData.identity Ms))).tensorMap ≫
          (@AdjacentMergeData.head M' N P' Ms fL).tensorMap =
        (@AdjacentMergeData.head M N P' Ms ((a ⊗ₘ 𝟙 N) ≫ fL)).tensorMap := by
    exact hleft
  have hhead := congrArg
    (fun z : M ⊗ N ⟶ P' ↦
      (@AdjacentMergeData.head M N P' Ms z).tensorMap) h
  rw [AdjacentMergeData.head_tensorMap_add,
    AdjacentMergeData.head_tensorMap_zsmul] at hhead
  exact htarget'.symm.trans (hhead.trans
    (congrArg₂ (· + ·) hright'.symm (congrArg (c • ·) hleft'.symm)))

theorem factorModule_raise_of_ne
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (q r : Fin (w.length + 1)) (h : q ≠ r) :
    factorModule d r = factorModule (d.raise q) r := by
  simp [factorModule, DegreeProfile.raise, Ne.symm h]

theorem rawContractionFactor_raiseRight_eq_mergedTarget
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    rawContractionFactor (d.raise i.succ) i =
      factorModule ((d.contract i).raise (erasePosition w i))
        (erasePosition w i) :=
  (rawContractionFactor_eq_contractPosition (d.raise i.succ) i).trans
    (congrArg (fun e ↦ factorModule e (erasePosition w i))
      (DegreeProfile.raise_right_contract d i))

theorem rawContractionFactor_raiseLeft_eq_mergedTarget
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    rawContractionFactor (d.raise i.castSucc) i =
      factorModule ((d.contract i).raise (erasePosition w i))
        (erasePosition w i) :=
  (rawContractionFactor_eq_contractPosition (d.raise i.castSucc) i).trans
    (congrArg (fun e ↦ factorModule e (erasePosition w i))
      (DegreeProfile.raise_left_contract d i))

def mergedRawFactorDifferential
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    rawContractionFactor d i ⟶
      factorModule ((d.contract i).raise (erasePosition w i))
        (erasePosition w i) :=
  eqToHom (rawContractionFactor_eq_contractPosition d i) ≫
    factorDifferential (d.contract i) (erasePosition w i) (erasePosition w i)

def rightAdjacentCompositionToMergedTarget
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    factorModule d i.castSucc ⊗ factorModule (d.raise i.succ) i.succ ⟶
      factorModule ((d.contract i).raise (erasePosition w i))
        (erasePosition w i) :=
  (eqToHom (factorModule_raise_of_ne d i.succ i.castSucc
      (Fin.ne_of_gt i.castSucc_lt_succ)) ⊗ₘ
      𝟙 (factorModule (d.raise i.succ) i.succ)) ≫
    adjacentFactorComposition (d.raise i.succ) i ≫
    eqToHom (rawContractionFactor_raiseRight_eq_mergedTarget d i)

def leftAdjacentCompositionToMergedTarget
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    factorModule (d.raise i.castSucc) i.castSucc ⊗ factorModule d i.succ ⟶
      factorModule ((d.contract i).raise (erasePosition w i))
        (erasePosition w i) :=
  (𝟙 (factorModule (d.raise i.castSucc) i.castSucc) ⊗ₘ
      eqToHom (factorModule_raise_of_ne d i.castSucc i.succ
        (Fin.ne_of_lt i.castSucc_lt_succ))) ≫
    adjacentFactorComposition (d.raise i.castSucc) i ≫
    eqToHom (rawContractionFactor_raiseLeft_eq_mergedTarget d i)

theorem adjacentDifferentialTarget_eq_mergedTarget
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    (dgHomZModuleCochainComplex
      (w.arrowSource i.castSucc) (w.arrowTarget i.succ)).X
        ((d.arrowDegree i.castSucc + d.arrowDegree i.succ) + 1) =
      factorModule ((d.contract i).raise (erasePosition w i))
        (erasePosition w i) := by
  unfold factorModule
  rw [eraseIntermediate_arrowSource_at w i,
    eraseIntermediate_arrowTarget_at w i]
  simp [DegreeProfile.raise, contract_arrowDegree_at]

def adjacentRightDifferentialPathToMergedTarget
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    factorModule d i.castSucc ⊗ factorModule d i.succ ⟶
      factorModule ((d.contract i).raise (erasePosition w i))
        (erasePosition w i) :=
  adjacentRightDifferentialPath d i ≫
    eqToHom (adjacentDifferentialTarget_eq_mergedTarget d i)

def adjacentLeftDifferentialPathToMergedTarget
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    factorModule d i.castSucc ⊗ factorModule d i.succ ⟶
      factorModule ((d.contract i).raise (erasePosition w i))
        (erasePosition w i) :=
  adjacentLeftDifferentialPath d i ≫
    eqToHom (adjacentDifferentialTarget_eq_mergedTarget d i)

theorem mergedRawFactorDifferential_heq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    HEq (mergedRawFactorDifferential d i)
      ((dgHomZModuleCochainComplex
        (w.arrowSource i.castSucc) (w.arrowTarget i.succ)).d
          (d.arrowDegree i.castSucc + d.arrowDegree i.succ)
          ((d.arrowDegree i.castSucc + d.arrowDegree i.succ) + 1)) := by
  unfold mergedRawFactorDifferential
  apply (CategoryTheory.eqToHom_comp_heq _ _).trans
  unfold factorDifferential
  simp only [eq_self, dif_pos]
  apply dgHomDifferential_heq
  · exact eraseIntermediate_arrowSource_at w i
  · exact eraseIntermediate_arrowTarget_at w i
  · exact contract_arrowDegree_at d i
  · simp [DegreeProfile.raise, contract_arrowDegree_at]

def adjacentRightRaisedComposition
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    factorModule d i.castSucc ⊗ factorModule (d.raise i.succ) i.succ ⟶
      (dgHomZModuleCochainComplex
        (w.arrowSource i.castSucc) (w.arrowTarget i.succ)).X
          ((d.arrowDegree i.castSucc + d.arrowDegree i.succ) + 1) := by
  simp only [factorModule]
  exact dgCochainCompTensorOfEq
    (w.arrowSource i.castSucc) (w.arrowTarget i.castSucc)
    (w.arrowSource i.succ) (w.arrowTarget i.succ)
    (arrowTarget_castSucc_eq_arrowSource_succ w i) (by
      simp [DegreeProfile.raise]
      omega)

def adjacentLeftRaisedComposition
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    factorModule (d.raise i.castSucc) i.castSucc ⊗ factorModule d i.succ ⟶
      (dgHomZModuleCochainComplex
        (w.arrowSource i.castSucc) (w.arrowTarget i.succ)).X
          ((d.arrowDegree i.castSucc + d.arrowDegree i.succ) + 1) := by
  simp only [factorModule]
  exact dgCochainCompTensorOfEq
    (w.arrowSource i.castSucc) (w.arrowTarget i.castSucc)
    (w.arrowSource i.succ) (w.arrowTarget i.succ)
    (arrowTarget_castSucc_eq_arrowSource_succ w i) (by
      simp [DegreeProfile.raise]
      omega)

theorem adjacentFactorComposition_raiseRight_heq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    HEq (adjacentFactorComposition (d.raise i.succ) i)
      (adjacentRightRaisedComposition d i) := by
  have hne : i.castSucc ≠ i.succ := Fin.ne_of_lt i.castSucc_lt_succ
  unfold adjacentFactorComposition adjacentRightRaisedComposition factorModule
  apply dgCochainCompTensorOfEq_heq
  all_goals simp [DegreeProfile.raise, hne] <;> ring

theorem adjacentFactorComposition_raiseLeft_heq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    HEq (adjacentFactorComposition (d.raise i.castSucc) i)
      (adjacentLeftRaisedComposition d i) := by
  have hne : i.castSucc ≠ i.succ := Fin.ne_of_lt i.castSucc_lt_succ
  unfold adjacentFactorComposition adjacentLeftRaisedComposition factorModule
  apply dgCochainCompTensorOfEq_heq
  all_goals simp [DegreeProfile.raise, hne.symm] <;> ring

def adjacentRightPathComposition
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    (dgHomZModuleCochainComplex
        (w.arrowSource i.castSucc) (w.arrowTarget i.castSucc)).X
          (d.arrowDegree i.castSucc) ⊗
      (dgHomZModuleCochainComplex
        (w.arrowSource i.succ) (w.arrowTarget i.succ)).X
          (d.arrowDegree i.succ + 1) ⟶
      (dgHomZModuleCochainComplex
        (w.arrowSource i.castSucc) (w.arrowTarget i.succ)).X
          ((d.arrowDegree i.castSucc + d.arrowDegree i.succ) + 1) :=
  dgCochainCompTensorOfEq
    (w.arrowSource i.castSucc) (w.arrowTarget i.castSucc)
    (w.arrowSource i.succ) (w.arrowTarget i.succ)
    (arrowTarget_castSucc_eq_arrowSource_succ w i) (by omega)

def adjacentLeftPathComposition
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    (dgHomZModuleCochainComplex
        (w.arrowSource i.castSucc) (w.arrowTarget i.castSucc)).X
          (d.arrowDegree i.castSucc + 1) ⊗
      (dgHomZModuleCochainComplex
        (w.arrowSource i.succ) (w.arrowTarget i.succ)).X
          (d.arrowDegree i.succ) ⟶
      (dgHomZModuleCochainComplex
        (w.arrowSource i.castSucc) (w.arrowTarget i.succ)).X
          ((d.arrowDegree i.castSucc + d.arrowDegree i.succ) + 1) :=
  dgCochainCompTensorOfEq
    (w.arrowSource i.castSucc) (w.arrowTarget i.castSucc)
    (w.arrowSource i.succ) (w.arrowTarget i.succ)
    (arrowTarget_castSucc_eq_arrowSource_succ w i) (by omega)

theorem adjacentRightRaisedComposition_heq_pathComposition
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    HEq (adjacentRightRaisedComposition d i)
      (adjacentRightPathComposition d i) := by
  unfold adjacentRightRaisedComposition adjacentRightPathComposition factorModule
  apply dgCochainCompTensorOfEq_heq
  all_goals simp [DegreeProfile.raise]

theorem adjacentLeftRaisedComposition_heq_pathComposition
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    HEq (adjacentLeftRaisedComposition d i)
      (adjacentLeftPathComposition d i) := by
  unfold adjacentLeftRaisedComposition adjacentLeftPathComposition factorModule
  apply dgCochainCompTensorOfEq_heq
  all_goals simp [DegreeProfile.raise]

theorem rightAdjacentCompositionToMergedTarget_eq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    rightAdjacentCompositionToMergedTarget d i =
      adjacentRightRaisedComposition d i ≫
        eqToHom (adjacentDifferentialTarget_eq_mergedTarget d i) := by
  let hA := factorModule_raise_of_ne d i.succ i.castSucc
    (Fin.ne_of_gt i.castSucc_lt_succ)
  let hC := (adjacentDifferentialTarget_eq_mergedTarget d i).trans
    (rawContractionFactor_raiseRight_eq_mergedTarget d i).symm
  have hbase := test_tensor_comp_transport_of_heq hA rfl hC
    (adjacentRightRaisedComposition d i)
    (adjacentFactorComposition (d.raise i.succ) i)
    (adjacentFactorComposition_raiseRight_heq d i)
  have hbase' :
      (eqToHom hA ⊗ₘ 𝟙 (factorModule (d.raise i.succ) i.succ)) ≫
          adjacentFactorComposition (d.raise i.succ) i =
        adjacentRightRaisedComposition d i ≫ eqToHom hC := by
    simpa using hbase
  unfold rightAdjacentCompositionToMergedTarget
  rw [← Category.assoc, hbase', Category.assoc]
  simp

theorem leftAdjacentCompositionToMergedTarget_eq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    leftAdjacentCompositionToMergedTarget d i =
      adjacentLeftRaisedComposition d i ≫
        eqToHom (adjacentDifferentialTarget_eq_mergedTarget d i) := by
  let hB := factorModule_raise_of_ne d i.castSucc i.succ
    (Fin.ne_of_lt i.castSucc_lt_succ)
  let hC := (adjacentDifferentialTarget_eq_mergedTarget d i).trans
    (rawContractionFactor_raiseLeft_eq_mergedTarget d i).symm
  have hbase := test_tensor_comp_transport_of_heq rfl hB hC
    (adjacentLeftRaisedComposition d i)
    (adjacentFactorComposition (d.raise i.castSucc) i)
    (adjacentFactorComposition_raiseLeft_heq d i)
  have hbase' :
      (𝟙 (factorModule (d.raise i.castSucc) i.castSucc) ⊗ₘ eqToHom hB) ≫
          adjacentFactorComposition (d.raise i.castSucc) i =
        adjacentLeftRaisedComposition d i ≫ eqToHom hC := by
    simpa using hbase
  unfold leftAdjacentCompositionToMergedTarget
  rw [← Category.assoc, hbase', Category.assoc]
  simp

theorem rightAdjacentDifferentialPathToMergedTarget_eq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    (𝟙 (factorModule d i.castSucc) ⊗ₘ
        factorDifferential d i.succ i.succ) ≫
        rightAdjacentCompositionToMergedTarget d i =
      adjacentRightDifferentialPathToMergedTarget d i := by
  rw [rightAdjacentCompositionToMergedTarget_eq]
  unfold adjacentRightDifferentialPathToMergedTarget
  rw [← Category.assoc]
  congr 1
  apply eq_of_heq
  have hfd : HEq (factorDifferential d i.succ i.succ)
      ((dgHomZModuleCochainComplex
        (w.arrowSource i.succ) (w.arrowTarget i.succ)).d
          (d.arrowDegree i.succ) (d.arrowDegree i.succ + 1)) := by
    unfold factorDifferential
    simp only [eq_self, dif_pos]
    apply dgHomDifferential_heq <;> simp [DegreeProfile.raise]
  have htarget : factorModule (d.raise i.succ) i.succ =
      (dgHomZModuleCochainComplex
        (w.arrowSource i.succ) (w.arrowTarget i.succ)).X
          (d.arrowDegree i.succ + 1) := by
    unfold factorModule
    simp [DegreeProfile.raise]
  have htensor := tensorHom_heq rfl rfl rfl htarget
    (by rfl : HEq (𝟙 (factorModule d i.castSucc))
      (𝟙 ((dgHomZModuleCochainComplex
        (w.arrowSource i.castSucc) (w.arrowTarget i.castSucc)).X
          (d.arrowDegree i.castSucc)))) hfd
  have hsource : factorModule d i.castSucc ⊗ factorModule d i.succ =
      (dgHomZModuleCochainComplex
          (w.arrowSource i.castSucc) (w.arrowTarget i.castSucc)).X
            (d.arrowDegree i.castSucc) ⊗
        (dgHomZModuleCochainComplex
          (w.arrowSource i.succ) (w.arrowTarget i.succ)).X
            (d.arrowDegree i.succ) := rfl
  have hmiddle :
      factorModule d i.castSucc ⊗ factorModule (d.raise i.succ) i.succ =
        (dgHomZModuleCochainComplex
            (w.arrowSource i.castSucc) (w.arrowTarget i.castSucc)).X
              (d.arrowDegree i.castSucc) ⊗
          (dgHomZModuleCochainComplex
            (w.arrowSource i.succ) (w.arrowTarget i.succ)).X
              (d.arrowDegree i.succ + 1) :=
    congrArg₂ (· ⊗ ·) rfl htarget
  have hcomp := CategoryTheory.heq_comp hsource hmiddle rfl htensor
    (adjacentRightRaisedComposition_heq_pathComposition d i)
  simpa only [adjacentRightDifferentialPath, adjacentRightRaisedComposition,
    adjacentRightPathComposition, factorModule, id_eq] using hcomp

theorem leftAdjacentDifferentialPathToMergedTarget_eq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    (factorDifferential d i.castSucc i.castSucc ⊗ₘ
        𝟙 (factorModule d i.succ)) ≫
        leftAdjacentCompositionToMergedTarget d i =
      adjacentLeftDifferentialPathToMergedTarget d i := by
  rw [leftAdjacentCompositionToMergedTarget_eq]
  unfold adjacentLeftDifferentialPathToMergedTarget
  rw [← Category.assoc]
  congr 1
  apply eq_of_heq
  have hfd : HEq (factorDifferential d i.castSucc i.castSucc)
      ((dgHomZModuleCochainComplex
        (w.arrowSource i.castSucc) (w.arrowTarget i.castSucc)).d
          (d.arrowDegree i.castSucc) (d.arrowDegree i.castSucc + 1)) := by
    unfold factorDifferential
    simp only [eq_self, dif_pos]
    apply dgHomDifferential_heq <;> simp [DegreeProfile.raise]
  have htarget : factorModule (d.raise i.castSucc) i.castSucc =
      (dgHomZModuleCochainComplex
        (w.arrowSource i.castSucc) (w.arrowTarget i.castSucc)).X
          (d.arrowDegree i.castSucc + 1) := by
    unfold factorModule
    simp [DegreeProfile.raise]
  have htensor := tensorHom_heq rfl htarget rfl rfl hfd
    (by rfl : HEq (𝟙 (factorModule d i.succ))
      (𝟙 ((dgHomZModuleCochainComplex
        (w.arrowSource i.succ) (w.arrowTarget i.succ)).X
          (d.arrowDegree i.succ))))
  have hsource : factorModule d i.castSucc ⊗ factorModule d i.succ =
      (dgHomZModuleCochainComplex
          (w.arrowSource i.castSucc) (w.arrowTarget i.castSucc)).X
            (d.arrowDegree i.castSucc) ⊗
        (dgHomZModuleCochainComplex
          (w.arrowSource i.succ) (w.arrowTarget i.succ)).X
            (d.arrowDegree i.succ) := rfl
  have hmiddle :
      factorModule (d.raise i.castSucc) i.castSucc ⊗ factorModule d i.succ =
        (dgHomZModuleCochainComplex
            (w.arrowSource i.castSucc) (w.arrowTarget i.castSucc)).X
              (d.arrowDegree i.castSucc + 1) ⊗
          (dgHomZModuleCochainComplex
            (w.arrowSource i.succ) (w.arrowTarget i.succ)).X
              (d.arrowDegree i.succ) :=
    congrArg₂ (· ⊗ ·) htarget rfl
  have hcomp := CategoryTheory.heq_comp hsource hmiddle rfl htensor
    (adjacentLeftRaisedComposition_heq_pathComposition d i)
  simpa only [adjacentLeftDifferentialPath, adjacentLeftRaisedComposition,
    adjacentLeftPathComposition, factorModule, id_eq] using hcomp

theorem adjacentFactorComposition_merged_leibniz
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    adjacentFactorComposition d i ≫ mergedRawFactorDifferential d i =
      (𝟙 (factorModule d i.castSucc) ⊗ₘ
          factorDifferential d i.succ i.succ) ≫
          rightAdjacentCompositionToMergedTarget d i +
        ((d.arrowDegree i.succ).negOnePow : ℤ) •
          ((factorDifferential d i.castSucc i.castSucc ⊗ₘ
            𝟙 (factorModule d i.succ)) ≫
            leftAdjacentCompositionToMergedTarget d i) := by
  rw [rightAdjacentDifferentialPathToMergedTarget_eq,
    leftAdjacentDifferentialPathToMergedTarget_eq]
  have hmerged : mergedRawFactorDifferential d i =
      (dgHomZModuleCochainComplex
          (w.arrowSource i.castSucc) (w.arrowTarget i.succ)).d
            (d.arrowDegree i.castSucc + d.arrowDegree i.succ)
            ((d.arrowDegree i.castSucc + d.arrowDegree i.succ) + 1) ≫
        eqToHom (adjacentDifferentialTarget_eq_mergedTarget d i) := by
    apply eq_of_heq
    exact (mergedRawFactorDifferential_heq d i).trans
      (CategoryTheory.comp_eqToHom_heq _ _).symm
  rw [hmerged, ← Category.assoc, adjacentFactorComposition_comp_d]
  unfold adjacentRightDifferentialPathToMergedTarget
    adjacentLeftDifferentialPathToMergedTarget
  rw [Preadditive.add_comp]
  congr 1
  exact Preadditive.zsmul_comp
    (f := adjacentLeftDifferentialPath d i)
    (g := eqToHom (adjacentDifferentialTarget_eq_mergedTarget d i)) _

theorem recursiveAdjacentMergeDataOfFn_tensorMap_add : {k : ℕ} →
    (M : Fin (k + 1) → ModuleCat.{0} ℤ) → (i : Fin k) →
    (P : ModuleCat.{0} ℤ) → (f g : M i.castSucc ⊗ M i.succ ⟶ P) →
    (recursiveAdjacentMergeDataOfFn M i P (f + g)).tensorMap =
      (recursiveAdjacentMergeDataOfFn M i P f).tensorMap +
        (recursiveAdjacentMergeDataOfFn M i P g).tensorMap
  | 0, _, i, _, _, _ => Fin.elim0 i
  | k + 1, M, i, P, f, g => by
      cases i using Fin.cases with
      | zero => exact AdjacentMergeData.head_tensorMap_add f g
      | succ i =>
          change 𝟙 (M 0) ⊗ₘ
              (recursiveAdjacentMergeDataOfFn
                (fun q : Fin (k + 1) ↦ M q.succ) i P (f + g)).tensorMap = _
          rw [recursiveAdjacentMergeDataOfFn_tensorMap_add]
          simp
          rfl

theorem recursiveAdjacentMergeDataOfFn_tensorMap_zsmul : {k : ℕ} →
    (M : Fin (k + 1) → ModuleCat.{0} ℤ) → (i : Fin k) →
    (P : ModuleCat.{0} ℤ) → (c : ℤ) → (f : M i.castSucc ⊗ M i.succ ⟶ P) →
    (recursiveAdjacentMergeDataOfFn M i P (c • f)).tensorMap =
      c • (recursiveAdjacentMergeDataOfFn M i P f).tensorMap
  | 0, _, i, _, _, _ => Fin.elim0 i
  | k + 1, M, i, P, c, f => by
      cases i using Fin.cases with
      | zero => exact AdjacentMergeData.head_tensorMap_zsmul c f
      | succ i =>
          change 𝟙 (M 0) ⊗ₘ
              (recursiveAdjacentMergeDataOfFn
                (fun q : Fin (k + 1) ↦ M q.succ) i P (c • f)).tensorMap = _
          rw [recursiveAdjacentMergeDataOfFn_tensorMap_zsmul]
          change ((tensoringLeft (ModuleCat.{0} ℤ)).obj (M 0)).map
              (c • (recursiveAdjacentMergeDataOfFn
                (fun q : Fin (k + 1) ↦ M q.succ) i P f).tensorMap) = _
          rw [Functor.map_zsmul]
          rfl

theorem recursiveAdjacentMergeDataOfFn_tensorMap_zsmul_comp
    {k : ℕ} (M : Fin (k + 1) → ModuleCat.{0} ℤ) (i : Fin k)
    (P Q : ModuleCat.{0} ℤ) (c : ℤ)
    (f : M i.castSucc ⊗ M i.succ ⟶ Q) (g : Q ⟶ P) :
    (recursiveAdjacentMergeDataOfFn M i P ((c • f) ≫ g)).tensorMap =
      c • (recursiveAdjacentMergeDataOfFn M i P (f ≫ g)).tensorMap := by
  rw [Preadditive.zsmul_comp,
    recursiveAdjacentMergeDataOfFn_tensorMap_zsmul]

def mergedTotalLocalTensorMap
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :=
  (recursiveAdjacentMergeDataOfFn (factorModule d) i
    (factorModule ((d.contract i).raise (erasePosition w i))
      (erasePosition w i))
    (adjacentFactorComposition d i ≫ mergedRawFactorDifferential d i)).tensorMap

def mergedRightLocalTensorMap
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :=
  (recursiveAdjacentMergeDataOfFn (factorModule d) i
    (factorModule ((d.contract i).raise (erasePosition w i))
      (erasePosition w i))
    ((𝟙 (factorModule d i.castSucc) ⊗ₘ
        factorDifferential d i.succ i.succ) ≫
      rightAdjacentCompositionToMergedTarget d i)).tensorMap

def mergedLeftLocalTensorMap
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :=
  (recursiveAdjacentMergeDataOfFn (factorModule d) i
    (factorModule ((d.contract i).raise (erasePosition w i))
      (erasePosition w i))
    ((factorDifferential d i.castSucc i.castSucc ⊗ₘ
        𝟙 (factorModule d i.succ)) ≫
      leftAdjacentCompositionToMergedTarget d i)).tensorMap

theorem mergedLocalTensorMap_leibniz
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    mergedTotalLocalTensorMap d i =
      mergedRightLocalTensorMap d i +
        ((d.arrowDegree i.succ).negOnePow : ℤ) • mergedLeftLocalTensorMap d i := by
  unfold mergedTotalLocalTensorMap mergedRightLocalTensorMap
    mergedLeftLocalTensorMap
  rw [adjacentFactorComposition_merged_leibniz,
    recursiveAdjacentMergeDataOfFn_tensorMap_add,
    recursiveAdjacentMergeDataOfFn_tensorMap_zsmul]

def mergedCanonicalFactor
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) : Fin w.length → ModuleCat.{0} ℤ :=
  recursiveMergedFactor (factorModule d) i
    (factorModule ((d.contract i).raise (erasePosition w i))
      (erasePosition w i))

theorem mergedCanonicalFactor_eq_oldIndexedRaisedContract
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    mergedCanonicalFactor d i =
      fun r ↦ factorModule ((d.contract i).raise (erasePosition w i))
        (uneraseFactorIndex w i r) := by
  unfold mergedCanonicalFactor
  rw [recursiveMergedFactor_eq_mergedFactor]
  funext r
  by_cases hbefore : r < i
  · have hindex : eraseFactorIndex w i (uneraseFactorIndex w i r) = r := by simp
    have hne : erasePosition w i ≠ uneraseFactorIndex w i r := by
      intro h
      apply (Fin.ne_of_lt hbefore)
      apply Fin.ext
      exact congrArg
        (fun q : Fin ((eraseIntermediate w i).length + 1) ↦ q.val) h.symm
    rw [mergedFactor]
    simp only [hbefore, ↓reduceIte]
    exact (factorModule_contract_before_eq d i (uneraseFactorIndex w i r)
      (by simpa [hindex] using hbefore)).trans
      (factorModule_raise_of_ne (d.contract i) (erasePosition w i)
        (uneraseFactorIndex w i r) hne)
  · by_cases hat : r = i
    · subst r
      simp [mergedFactor]
    · have hafter : i < r := by omega
      have hindex : eraseFactorIndex w i (uneraseFactorIndex w i r) = r := by simp
      have hne : erasePosition w i ≠ uneraseFactorIndex w i r := by
        intro h
        apply hat
        apply Fin.ext
        exact congrArg
          (fun q : Fin ((eraseIntermediate w i).length + 1) ↦ q.val) h.symm
      rw [mergedFactor]
      simp only [hbefore, hat, ↓reduceIte]
      exact (factorModule_contract_after_eq d i (uneraseFactorIndex w i r)
        (by simpa [hindex] using hafter)).trans
        (factorModule_raise_of_ne (d.contract i) (erasePosition w i)
          (uneraseFactorIndex w i r) hne)

def mergedCanonicalDifferentialFactorMap
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    (r : Fin w.length) →
      recursiveMergedFactor (factorModule d) i (rawContractionFactor d i) r ⟶
        mergedCanonicalFactor d i r :=
  recursiveMergedFactorMap (factorModule d) (factorModule d) i
    (rawContractionFactor d i)
    (factorModule ((d.contract i).raise (erasePosition w i))
      (erasePosition w i))
    (fun r ↦ 𝟙 (factorModule d r)) (mergedRawFactorDifferential d i)

def mergedCanonicalDifferentialTensorMap
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :=
  (TensorMapData.ofFn
    (recursiveMergedFactor (factorModule d) i (rawContractionFactor d i))
    (mergedCanonicalFactor d i)
    (mergedCanonicalDifferentialFactorMap d i)).tensorMap

theorem rawContractionAdjacentMerge_comp_mergedCanonicalDifferential
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    (rawContractionAdjacentMergeData d i).tensorMap ≫
        mergedCanonicalDifferentialTensorMap d i =
      mergedTotalLocalTensorMap d i := by
  have hnatural := (recursiveAdjacentMergeDataOfFn_naturality
    (factorModule d) (factorModule d) i
    (rawContractionFactor d i)
    (factorModule ((d.contract i).raise (erasePosition w i))
      (erasePosition w i))
    (adjacentFactorComposition d i)
    (adjacentFactorComposition d i ≫ mergedRawFactorDifferential d i)
    (fun r ↦ 𝟙 (factorModule d r))
    (mergedRawFactorDifferential d i) (by simp)).tensorMap_comm
  simpa only [rawContractionAdjacentMergeData,
    mergedCanonicalDifferentialTensorMap, mergedCanonicalDifferentialFactorMap,
    mergedCanonicalFactor, mergedTotalLocalTensorMap,
    TensorMapData.ofFn_id_tensorMap, Category.id_comp] using hnatural.symm

theorem mergedCanonicalDifferentialFactorMap_internal_heq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i r : Fin w.length) :
    HEq (mergedCanonicalDifferentialFactorMap d i r)
      (factorDifferential (d.contract i) (erasePosition w i)
        (uneraseFactorIndex w i r)) := by
  apply (recursiveMergedFactorMap_heq_mergedFactorMap
    (factorModule d) (factorModule d) i
    (rawContractionFactor d i)
    (factorModule ((d.contract i).raise (erasePosition w i))
      (erasePosition w i))
    (fun q ↦ 𝟙 (factorModule d q)) (mergedRawFactorDifferential d i) r).trans
  by_cases hbefore : r < i
  · apply (mergedFactorMap_before_heq
      (factorModule d) (factorModule d) i
      (rawContractionFactor d i)
      (factorModule ((d.contract i).raise (erasePosition w i))
        (erasePosition w i))
      (fun q ↦ 𝟙 (factorModule d q)) (mergedRawFactorDifferential d i)
      r hbefore).trans
    have hne : erasePosition w i ≠ uneraseFactorIndex w i r := by
      intro h
      exact (Fin.ne_of_lt hbefore) (by
        apply Fin.ext
        exact congrArg
          (fun q : Fin ((eraseIntermediate w i).length + 1) ↦ q.val) h.symm)
    obtain ⟨hCD, htarget⟩ := factorDifferential_eqToHom_of_ne
      (d.contract i) (erasePosition w i) (uneraseFactorIndex w i r) hne
    have hsource := factorModule_contract_before_eq d i
      (uneraseFactorIndex w i r) (by simpa using hbefore)
    rw [eraseFactorIndex_uneraseFactorIndex] at hsource
    rw [htarget]
    simpa using equalityTransport_heq_of_source_eq rfl hCD
      hsource
  · by_cases hat : r = i
    · subst r
      apply (mergedFactorMap_at_heq
        (factorModule d) (factorModule d) i
        (rawContractionFactor d i)
        (factorModule ((d.contract i).raise (erasePosition w i))
          (erasePosition w i))
        (fun q ↦ 𝟙 (factorModule d q))
        (mergedRawFactorDifferential d i)).trans
      unfold mergedRawFactorDifferential
      rw [uneraseFactorIndex_self]
      exact CategoryTheory.eqToHom_comp_heq
        (factorDifferential (d.contract i) (erasePosition w i)
          (erasePosition w i)) (rawContractionFactor_eq_contractPosition d i)
    · have hafter : i < r := by omega
      apply (mergedFactorMap_after_heq
        (factorModule d) (factorModule d) i
        (rawContractionFactor d i)
        (factorModule ((d.contract i).raise (erasePosition w i))
          (erasePosition w i))
        (fun q ↦ 𝟙 (factorModule d q)) (mergedRawFactorDifferential d i)
        r hbefore hat).trans
      have hne : erasePosition w i ≠ uneraseFactorIndex w i r := by
        intro h
        exact hat (by
          apply Fin.ext
          exact congrArg
            (fun q : Fin ((eraseIntermediate w i).length + 1) ↦ q.val) h.symm)
      obtain ⟨hCD, htarget⟩ := factorDifferential_eqToHom_of_ne
        (d.contract i) (erasePosition w i) (uneraseFactorIndex w i r) hne
      have hsource := factorModule_contract_after_eq d i
        (uneraseFactorIndex w i r) (by simpa using hafter)
      rw [eraseFactorIndex_uneraseFactorIndex] at hsource
      rw [htarget]
      simpa using equalityTransport_heq_of_source_eq rfl hCD
        hsource

theorem oldIndexedFactorList_eq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (i : Fin w.length) (d : DegreeProfile (eraseIntermediate w i) n) :
    finFamilyList (fun r : Fin w.length ↦
        factorModule d (uneraseFactorIndex w i r)) =
      finFamilyList (factorModule d) := by
  cases w with
  | mk k intermediate =>
      cases k with
      | zero => exact Fin.elim0 i
      | succ k =>
          cases k with
          | zero =>
              fin_cases i
              rfl
          | succ k => rfl

theorem mergedCanonicalSummand_eq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    tensorModuleList (finFamilyList (mergedCanonicalFactor d i)) =
      summandModule ((d.contract i).raise (erasePosition w i)) :=
  (congrArg tensorModuleList
    (congrArg finFamilyList
      (mergedCanonicalFactor_eq_oldIndexedRaisedContract d i))).trans
    (congrArg tensorModuleList
      (oldIndexedFactorList_eq i
        ((d.contract i).raise (erasePosition w i))))

theorem mergedCanonicalDifferentialTensorMap_internal_heq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    HEq (mergedCanonicalDifferentialTensorMap d i)
      (internalDifferentialTensorMap (d.contract i) (erasePosition w i)) := by
  apply (TensorMapData.ofFn_tensorMap_heq_of_pointwise
    (recursiveMergedFactor (factorModule d) i (rawContractionFactor d i))
    (mergedCanonicalFactor d i)
    (contractedFactorAtOldIndex d i)
    (fun r ↦ factorModule
      ((d.contract i).raise (erasePosition w i))
      (uneraseFactorIndex w i r))
    (mergedCanonicalDifferentialFactorMap d i)
    (fun r ↦ factorDifferential (d.contract i) (erasePosition w i)
      (uneraseFactorIndex w i r))
    (test_rawContractionTarget_eq d i)
    (mergedCanonicalFactor_eq_oldIndexedRaisedContract d i)
    (mergedCanonicalDifferentialFactorMap_internal_heq d i)).trans
  exact contractedInternalTensorMapAtOldIndex_heq d i (erasePosition w i)

theorem contractionInternalMergedTensorMap_heq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    HEq (contractionTensorMap d i ≫
        internalDifferentialTensorMap (d.contract i) (erasePosition w i))
      (mergedTotalLocalTensorMap d i) := by
  apply (CategoryTheory.heq_comp rfl
    (rawContractionSummand_eq d i).symm
    (mergedCanonicalSummand_eq d i).symm
    (test_contractionTensorMap_raw_heq d i)
    (mergedCanonicalDifferentialTensorMap_internal_heq d i).symm).trans
  exact heq_of_eq (rawContractionAdjacentMerge_comp_mergedCanonicalDifferential d i)

def rightMergedCanonicalTransportFactorMap
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    (r : Fin w.length) → mergedCanonicalFactor d i r ⟶
      recursiveMergedFactor (factorModule (d.raise i.succ)) i
        (rawContractionFactor (d.raise i.succ) i) r :=
  recursiveMergedFactorMap (factorModule d) (factorModule (d.raise i.succ)) i
    (factorModule ((d.contract i).raise (erasePosition w i))
      (erasePosition w i))
    (rawContractionFactor (d.raise i.succ) i)
    (factorDifferential d i.succ)
    (eqToHom (rawContractionFactor_raiseRight_eq_mergedTarget d i).symm)

def rightMergedCanonicalTransportTensorMap
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :=
  (TensorMapData.ofFn (mergedCanonicalFactor d i)
    (recursiveMergedFactor (factorModule (d.raise i.succ)) i
      (rawContractionFactor (d.raise i.succ) i))
    (rightMergedCanonicalTransportFactorMap d i)).tensorMap

theorem mergedRightLocal_naturality
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    AdjacentMergeNaturality
      (recursiveAdjacentMergeDataOfFn (factorModule d) i
        (factorModule ((d.contract i).raise (erasePosition w i))
          (erasePosition w i))
        ((𝟙 (factorModule d i.castSucc) ⊗ₘ
            factorDifferential d i.succ i.succ) ≫
          rightAdjacentCompositionToMergedTarget d i))
      (rawContractionAdjacentMergeData (d.raise i.succ) i)
      (TensorMapData.ofFn (factorModule d) (factorModule (d.raise i.succ))
        (factorDifferential d i.succ))
      (TensorMapData.ofFn (mergedCanonicalFactor d i)
        (recursiveMergedFactor (factorModule (d.raise i.succ)) i
          (rawContractionFactor (d.raise i.succ) i))
        (rightMergedCanonicalTransportFactorMap d i)) := by
  apply recursiveAdjacentMergeDataOfFn_naturality
  obtain ⟨hA, hhA⟩ := factorDifferential_eqToHom_of_ne d i.succ i.castSucc
    (Fin.ne_of_gt i.castSucc_lt_succ)
  rw [hhA]
  unfold rightAdjacentCompositionToMergedTarget
  simp only [Category.assoc]
  rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
  simp

theorem rightRawMergedFactor_eq_canonical
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    (fun r ↦ recursiveMergedFactor (factorModule (d.raise i.succ)) i
      (rawContractionFactor (d.raise i.succ) i) r) =
      mergedCanonicalFactor d i := by
  apply (test_rawContractionTarget_eq (d.raise i.succ) i).trans
  change contractedFactorAtOldIndex (d.raise i.succ) i = _
  apply Eq.trans _ (mergedCanonicalFactor_eq_oldIndexedRaisedContract d i).symm
  unfold contractedFactorAtOldIndex
  exact congrArg
    (fun e ↦ fun r ↦ factorModule e (uneraseFactorIndex w i r))
    (DegreeProfile.raise_right_contract d i)

theorem rightMergedCanonicalTransportFactorMap_eqToHom
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i r : Fin w.length) :
    rightMergedCanonicalTransportFactorMap d i r =
      eqToHom (congrFun (rightRawMergedFactor_eq_canonical d i).symm r) := by
  let hcanonical := congrFun (rightRawMergedFactor_eq_canonical d i).symm r
  have hbridge := recursiveMergedFactorMap_heq_mergedFactorMap
    (factorModule d) (factorModule (d.raise i.succ)) i
    (factorModule ((d.contract i).raise (erasePosition w i))
      (erasePosition w i))
    (rawContractionFactor (d.raise i.succ) i)
    (factorDifferential d i.succ)
    (eqToHom (rawContractionFactor_raiseRight_eq_mergedTarget d i).symm) r
  by_cases hbefore : r < i
  · have hstruct := hbridge.trans (mergedFactorMap_before_heq
      (factorModule d) (factorModule (d.raise i.succ)) i
      (factorModule ((d.contract i).raise (erasePosition w i))
        (erasePosition w i))
      (rawContractionFactor (d.raise i.succ) i)
      (factorDifferential d i.succ)
      (eqToHom (rawContractionFactor_raiseRight_eq_mergedTarget d i).symm)
      r hbefore)
    have hne : i.succ ≠ r.castSucc := by
      intro h
      have hval := congrArg Fin.val h
      change i.val + 1 = r.val at hval
      omega
    obtain ⟨hAB, hmap⟩ := factorDifferential_eqToHom_of_ne
      d i.succ r.castSucc hne
    have hsource : factorModule d r.castSucc = mergedCanonicalFactor d i r := by
      unfold mergedCanonicalFactor
      rw [recursiveMergedFactor_eq_mergedFactor]
      simp [mergedFactor, hbefore]
    exact eq_of_heq (hstruct.trans (heq_of_eq hmap) |>.trans
      (equalityTransport_heq_of_source_eq hAB hcanonical hsource))
  · by_cases hat : r = i
    · subst r
      have hstruct := hbridge.trans (mergedFactorMap_at_heq
        (factorModule d) (factorModule (d.raise i.succ)) i
        (factorModule ((d.contract i).raise (erasePosition w i))
          (erasePosition w i))
        (rawContractionFactor (d.raise i.succ) i)
        (factorDifferential d i.succ)
        (eqToHom (rawContractionFactor_raiseRight_eq_mergedTarget d i).symm))
      have hsource :
          factorModule ((d.contract i).raise (erasePosition w i))
              (erasePosition w i) = mergedCanonicalFactor d i i := by
        unfold mergedCanonicalFactor
        rw [recursiveMergedFactor_eq_mergedFactor]
        simp [mergedFactor]
      exact eq_of_heq (hstruct.trans
        (equalityTransport_heq_of_source_eq
          (rawContractionFactor_raiseRight_eq_mergedTarget d i).symm
          hcanonical hsource))
    · have hafter : i < r := by omega
      have hstruct := hbridge.trans (mergedFactorMap_after_heq
        (factorModule d) (factorModule (d.raise i.succ)) i
        (factorModule ((d.contract i).raise (erasePosition w i))
          (erasePosition w i))
        (rawContractionFactor (d.raise i.succ) i)
        (factorDifferential d i.succ)
        (eqToHom (rawContractionFactor_raiseRight_eq_mergedTarget d i).symm)
        r hbefore hat)
      have hne : i.succ ≠ r.succ := by
        exact fun h ↦ hat ((Fin.succ_injective _) h.symm)
      obtain ⟨hAB, hmap⟩ := factorDifferential_eqToHom_of_ne
        d i.succ r.succ hne
      have hsource : factorModule d r.succ = mergedCanonicalFactor d i r := by
        unfold mergedCanonicalFactor
        rw [recursiveMergedFactor_eq_mergedFactor]
        simp [mergedFactor, hbefore, hat]
      exact eq_of_heq (hstruct.trans (heq_of_eq hmap) |>.trans
        (equalityTransport_heq_of_source_eq hAB hcanonical hsource))

theorem rightMergedCanonicalTransportTensorMap_eqToHom
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    rightMergedCanonicalTransportTensorMap d i =
      eqToHom (congrArg tensorModuleList (congrArg finFamilyList
        (rightRawMergedFactor_eq_canonical d i).symm)) := by
  exact test_tensorMapData_ofFn_eqToHom _ _
    (rightRawMergedFactor_eq_canonical d i).symm _
    (rightMergedCanonicalTransportFactorMap_eqToHom d i)

theorem mergedRightLocal_comp_transport_heq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    HEq (mergedRightLocalTensorMap d i ≫
        rightMergedCanonicalTransportTensorMap d i)
      (mergedRightLocalTensorMap d i) := by
  rw [rightMergedCanonicalTransportTensorMap_eqToHom]
  exact CategoryTheory.comp_eqToHom_heq _ _

theorem internalRightRawContraction_heq_mergedRightLocal
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    HEq (internalDifferentialTensorMap d i.succ ≫
        (rawContractionAdjacentMergeData (d.raise i.succ) i).tensorMap)
      (mergedRightLocalTensorMap d i) := by
  have hnatural := (mergedRightLocal_naturality d i).tensorMap_comm
  apply (heq_of_eq (by
    simpa only [internalDifferentialTensorMap,
      rawContractionAdjacentMergeData, mergedRightLocalTensorMap,
      rightMergedCanonicalTransportTensorMap] using hnatural)).trans
  exact mergedRightLocal_comp_transport_heq d i

theorem rightInternalContractionToMergedTarget_heq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    HEq (rightInternalContractionToMergedTarget d i)
      (mergedRightLocalTensorMap d i) := by
  have hstrip : HEq (rightInternalContractionToMergedTarget d i)
      (internalDifferentialTensorMap d i.succ ≫
        contractionTensorMap (d.raise i.succ) i) := by
    unfold rightInternalContractionToMergedTarget
    simpa only [Category.assoc] using CategoryTheory.comp_eqToHom_heq
      (internalDifferentialTensorMap d i.succ ≫
        contractionTensorMap (d.raise i.succ) i)
      (congrArg summandModule (DegreeProfile.raise_right_contract d i))
  have hraw : HEq
      (internalDifferentialTensorMap d i.succ ≫
        contractionTensorMap (d.raise i.succ) i)
      (internalDifferentialTensorMap d i.succ ≫
        (rawContractionAdjacentMergeData (d.raise i.succ) i).tensorMap) := by
    exact CategoryTheory.heq_comp rfl rfl
      (rawContractionSummand_eq (d.raise i.succ) i).symm
      (by rfl) (test_contractionTensorMap_raw_heq (d.raise i.succ) i)
  exact hstrip.trans hraw |>.trans
    (internalRightRawContraction_heq_mergedRightLocal d i)

def leftMergedCanonicalTransportFactorMap
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    (r : Fin w.length) → mergedCanonicalFactor d i r ⟶
      recursiveMergedFactor (factorModule (d.raise i.castSucc)) i
        (rawContractionFactor (d.raise i.castSucc) i) r :=
  recursiveMergedFactorMap (factorModule d) (factorModule (d.raise i.castSucc)) i
    (factorModule ((d.contract i).raise (erasePosition w i))
      (erasePosition w i))
    (rawContractionFactor (d.raise i.castSucc) i)
    (factorDifferential d i.castSucc)
    (eqToHom (rawContractionFactor_raiseLeft_eq_mergedTarget d i).symm)

def leftMergedCanonicalTransportTensorMap
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :=
  (TensorMapData.ofFn (mergedCanonicalFactor d i)
    (recursiveMergedFactor (factorModule (d.raise i.castSucc)) i
      (rawContractionFactor (d.raise i.castSucc) i))
    (leftMergedCanonicalTransportFactorMap d i)).tensorMap

theorem mergedLeftLocal_naturality
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    AdjacentMergeNaturality
      (recursiveAdjacentMergeDataOfFn (factorModule d) i
        (factorModule ((d.contract i).raise (erasePosition w i))
          (erasePosition w i))
        ((factorDifferential d i.castSucc i.castSucc ⊗ₘ
            𝟙 (factorModule d i.succ)) ≫
          leftAdjacentCompositionToMergedTarget d i))
      (rawContractionAdjacentMergeData (d.raise i.castSucc) i)
      (TensorMapData.ofFn (factorModule d) (factorModule (d.raise i.castSucc))
        (factorDifferential d i.castSucc))
      (TensorMapData.ofFn (mergedCanonicalFactor d i)
        (recursiveMergedFactor (factorModule (d.raise i.castSucc)) i
          (rawContractionFactor (d.raise i.castSucc) i))
        (leftMergedCanonicalTransportFactorMap d i)) := by
  apply recursiveAdjacentMergeDataOfFn_naturality
  obtain ⟨hB, hhB⟩ := factorDifferential_eqToHom_of_ne d i.castSucc i.succ
    (Fin.ne_of_lt i.castSucc_lt_succ)
  rw [hhB]
  unfold leftAdjacentCompositionToMergedTarget
  simp only [Category.assoc]
  rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
  simp

theorem leftRawMergedFactor_eq_canonical
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    (fun r ↦ recursiveMergedFactor (factorModule (d.raise i.castSucc)) i
      (rawContractionFactor (d.raise i.castSucc) i) r) =
      mergedCanonicalFactor d i := by
  apply (test_rawContractionTarget_eq (d.raise i.castSucc) i).trans
  change contractedFactorAtOldIndex (d.raise i.castSucc) i = _
  apply Eq.trans _ (mergedCanonicalFactor_eq_oldIndexedRaisedContract d i).symm
  unfold contractedFactorAtOldIndex
  exact congrArg
    (fun e ↦ fun r ↦ factorModule e (uneraseFactorIndex w i r))
    (DegreeProfile.raise_left_contract d i)

theorem leftMergedCanonicalTransportFactorMap_eqToHom
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i r : Fin w.length) :
    leftMergedCanonicalTransportFactorMap d i r =
      eqToHom (congrFun (leftRawMergedFactor_eq_canonical d i).symm r) := by
  let hcanonical := congrFun (leftRawMergedFactor_eq_canonical d i).symm r
  have hbridge := recursiveMergedFactorMap_heq_mergedFactorMap
    (factorModule d) (factorModule (d.raise i.castSucc)) i
    (factorModule ((d.contract i).raise (erasePosition w i))
      (erasePosition w i))
    (rawContractionFactor (d.raise i.castSucc) i)
    (factorDifferential d i.castSucc)
    (eqToHom (rawContractionFactor_raiseLeft_eq_mergedTarget d i).symm) r
  by_cases hbefore : r < i
  · have hstruct := hbridge.trans (mergedFactorMap_before_heq
      (factorModule d) (factorModule (d.raise i.castSucc)) i
      (factorModule ((d.contract i).raise (erasePosition w i))
        (erasePosition w i))
      (rawContractionFactor (d.raise i.castSucc) i)
      (factorDifferential d i.castSucc)
      (eqToHom (rawContractionFactor_raiseLeft_eq_mergedTarget d i).symm)
      r hbefore)
    have hne : i.castSucc ≠ r.castSucc := by
      intro h
      have hval := congrArg Fin.val h
      change i.val = r.val at hval
      omega
    obtain ⟨hAB, hmap⟩ := factorDifferential_eqToHom_of_ne
      d i.castSucc r.castSucc hne
    have hsource : factorModule d r.castSucc = mergedCanonicalFactor d i r := by
      unfold mergedCanonicalFactor
      rw [recursiveMergedFactor_eq_mergedFactor]
      simp [mergedFactor, hbefore]
    exact eq_of_heq (hstruct.trans (heq_of_eq hmap) |>.trans
      (equalityTransport_heq_of_source_eq hAB hcanonical hsource))
  · by_cases hat : r = i
    · subst r
      have hstruct := hbridge.trans (mergedFactorMap_at_heq
        (factorModule d) (factorModule (d.raise i.castSucc)) i
        (factorModule ((d.contract i).raise (erasePosition w i))
          (erasePosition w i))
        (rawContractionFactor (d.raise i.castSucc) i)
        (factorDifferential d i.castSucc)
        (eqToHom (rawContractionFactor_raiseLeft_eq_mergedTarget d i).symm))
      have hsource :
          factorModule ((d.contract i).raise (erasePosition w i))
              (erasePosition w i) = mergedCanonicalFactor d i i := by
        unfold mergedCanonicalFactor
        rw [recursiveMergedFactor_eq_mergedFactor]
        simp [mergedFactor]
      exact eq_of_heq (hstruct.trans
        (equalityTransport_heq_of_source_eq
          (rawContractionFactor_raiseLeft_eq_mergedTarget d i).symm
          hcanonical hsource))
    · have hafter : i < r := by omega
      have hstruct := hbridge.trans (mergedFactorMap_after_heq
        (factorModule d) (factorModule (d.raise i.castSucc)) i
        (factorModule ((d.contract i).raise (erasePosition w i))
          (erasePosition w i))
        (rawContractionFactor (d.raise i.castSucc) i)
        (factorDifferential d i.castSucc)
        (eqToHom (rawContractionFactor_raiseLeft_eq_mergedTarget d i).symm)
        r hbefore hat)
      have hne : i.castSucc ≠ r.succ := by
        intro h
        have hval := congrArg Fin.val h
        change i.val = r.val + 1 at hval
        omega
      obtain ⟨hAB, hmap⟩ := factorDifferential_eqToHom_of_ne
        d i.castSucc r.succ hne
      have hsource : factorModule d r.succ = mergedCanonicalFactor d i r := by
        unfold mergedCanonicalFactor
        rw [recursiveMergedFactor_eq_mergedFactor]
        simp [mergedFactor, hbefore, hat]
      exact eq_of_heq (hstruct.trans (heq_of_eq hmap) |>.trans
        (equalityTransport_heq_of_source_eq hAB hcanonical hsource))

theorem leftMergedCanonicalTransportTensorMap_eqToHom
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    leftMergedCanonicalTransportTensorMap d i =
      eqToHom (congrArg tensorModuleList (congrArg finFamilyList
        (leftRawMergedFactor_eq_canonical d i).symm)) := by
  exact test_tensorMapData_ofFn_eqToHom _ _
    (leftRawMergedFactor_eq_canonical d i).symm _
    (leftMergedCanonicalTransportFactorMap_eqToHom d i)

theorem mergedLeftLocal_comp_transport_heq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    HEq (mergedLeftLocalTensorMap d i ≫
        leftMergedCanonicalTransportTensorMap d i)
      (mergedLeftLocalTensorMap d i) := by
  rw [leftMergedCanonicalTransportTensorMap_eqToHom]
  exact CategoryTheory.comp_eqToHom_heq _ _

theorem internalLeftRawContraction_heq_mergedLeftLocal
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    HEq (internalDifferentialTensorMap d i.castSucc ≫
        (rawContractionAdjacentMergeData (d.raise i.castSucc) i).tensorMap)
      (mergedLeftLocalTensorMap d i) := by
  have hnatural := (mergedLeftLocal_naturality d i).tensorMap_comm
  apply (heq_of_eq (by
    simpa only [internalDifferentialTensorMap,
      rawContractionAdjacentMergeData, mergedLeftLocalTensorMap,
      leftMergedCanonicalTransportTensorMap] using hnatural)).trans
  exact mergedLeftLocal_comp_transport_heq d i

theorem leftInternalContractionToMergedTarget_heq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    HEq (leftInternalContractionToMergedTarget d i)
      (mergedLeftLocalTensorMap d i) := by
  have hstrip : HEq (leftInternalContractionToMergedTarget d i)
      (internalDifferentialTensorMap d i.castSucc ≫
        contractionTensorMap (d.raise i.castSucc) i) := by
    unfold leftInternalContractionToMergedTarget
    simpa only [Category.assoc] using CategoryTheory.comp_eqToHom_heq
      (internalDifferentialTensorMap d i.castSucc ≫
        contractionTensorMap (d.raise i.castSucc) i)
      (congrArg summandModule (DegreeProfile.raise_left_contract d i))
  have hraw : HEq
      (internalDifferentialTensorMap d i.castSucc ≫
        contractionTensorMap (d.raise i.castSucc) i)
      (internalDifferentialTensorMap d i.castSucc ≫
        (rawContractionAdjacentMergeData (d.raise i.castSucc) i).tensorMap) := by
    exact CategoryTheory.heq_comp rfl rfl
      (rawContractionSummand_eq (d.raise i.castSucc) i).symm
      (by rfl) (test_contractionTensorMap_raw_heq (d.raise i.castSucc) i)
  exact hstrip.trans hraw |>.trans
    (internalLeftRawContraction_heq_mergedLeftLocal d i)

theorem mergedTensorMap_leibniz
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    contractionTensorMap d i ≫
        internalDifferentialTensorMap (d.contract i) (erasePosition w i) =
      rightInternalContractionToMergedTarget d i +
        ((d.arrowDegree i.succ).negOnePow : ℤ) •
          leftInternalContractionToMergedTarget d i := by
  let htarget := mergedCanonicalSummand_eq d i
  have htotal : contractionTensorMap d i ≫
      internalDifferentialTensorMap (d.contract i) (erasePosition w i) =
        mergedTotalLocalTensorMap d i ≫ eqToHom htarget :=
    eq_of_heq ((contractionInternalMergedTensorMap_heq d i).trans
      (CategoryTheory.comp_eqToHom_heq _ htarget).symm)
  have hright : rightInternalContractionToMergedTarget d i =
      mergedRightLocalTensorMap d i ≫ eqToHom htarget :=
    eq_of_heq ((rightInternalContractionToMergedTarget_heq d i).trans
      (CategoryTheory.comp_eqToHom_heq _ htarget).symm)
  have hleft : leftInternalContractionToMergedTarget d i =
      mergedLeftLocalTensorMap d i ≫ eqToHom htarget :=
    eq_of_heq ((leftInternalContractionToMergedTarget_heq d i).trans
      (CategoryTheory.comp_eqToHom_heq _ htarget).symm)
  rw [htotal, hright, hleft]
  rw [mergedLocalTensorMap_leibniz, Preadditive.add_comp]
  congr 1
  exact Preadditive.zsmul_comp
    (f := mergedLeftLocalTensorMap d i) (g := eqToHom htarget) _

end LeanLCAExactChallenge.Infinity.MetrizableBoundedComplexes.DrinfeldWord
