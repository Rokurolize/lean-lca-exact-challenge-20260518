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

end LeanLCAExactChallenge.Infinity.MetrizableBoundedComplexes.DrinfeldWord
