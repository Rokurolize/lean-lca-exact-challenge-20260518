import LeanLCAExactChallenge.Derived.ExactAcyclicWithCyclesClosure
import LeanLCAExactChallenge.LCA.IdempotentComplete

/-!
# Contractible complexes are exact-acyclic with cycle objects

This file proves that a cochain complex with a contracting homotopy is
acyclic for the corrected cycle-object exact-category predicate.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory
open CategoryTheory.Category
open HomologicalComplex

universe v u

namespace LeanLCAExactChallenge

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (K : CochainComplex C ℤ) (h : Homotopy (𝟙 K) (0 : K ⟶ K))

def contractibleCycleEnd (i : ℤ) : K.X i ⟶ K.X i :=
  h.hom i (i - 1) ≫ K.d (i - 1) i

def contractibleBoundaryEnd (i : ℤ) : K.X i ⟶ K.X i :=
  K.d i (i + 1) ≫ h.hom (i + 1) i

lemma contractibleCycleEnd_next (i : ℤ) :
    contractibleCycleEnd K h (i + 1) = h.hom (i + 1) i ≫ K.d i (i + 1) := by
  unfold contractibleCycleEnd
  congr <;> omega

lemma contractible_homotopy_id_eq (i : ℤ) :
    𝟙 (K.X i) = contractibleBoundaryEnd K h i + contractibleCycleEnd K h i := by
  have hc := h.comm i
  simp only [dNext, prevD, AddMonoidHom.mk'_apply] at hc
  rw [CochainComplex.next ℤ i, CochainComplex.prev ℤ i] at hc
  simpa only [contractibleBoundaryEnd, contractibleCycleEnd, HomologicalComplex.id_f,
    HomologicalComplex.zero_f, add_zero] using hc

lemma contractibleCycleEnd_comp_boundaryEnd (i : ℤ) :
    contractibleCycleEnd K h i ≫ contractibleBoundaryEnd K h i = 0 := by
  simp [contractibleCycleEnd, contractibleBoundaryEnd, Category.assoc]

@[reassoc]
lemma contractibleCycleEnd_comp_d (i : ℤ) :
    contractibleCycleEnd K h i ≫ K.d i (i + 1) = 0 := by
  simp [contractibleCycleEnd, Category.assoc]

@[reassoc]
lemma contractible_d_comp_cycleEnd_next (i : ℤ) :
    K.d i (i + 1) ≫ contractibleCycleEnd K h (i + 1) = K.d i (i + 1) := by
  symm
  calc
    K.d i (i + 1) =
        (contractibleBoundaryEnd K h i + contractibleCycleEnd K h i) ≫ K.d i (i + 1) := by
      rw [← contractible_homotopy_id_eq K h i, Category.id_comp]
    _ = contractibleBoundaryEnd K h i ≫ K.d i (i + 1) +
          contractibleCycleEnd K h i ≫ K.d i (i + 1) := by
      rw [Preadditive.add_comp]
    _ = contractibleBoundaryEnd K h i ≫ K.d i (i + 1) := by
      rw [contractibleCycleEnd_comp_d K h i, add_zero]
    _ = K.d i (i + 1) ≫ contractibleCycleEnd K h (i + 1) := by
      rw [contractibleCycleEnd_next]
      simp [contractibleBoundaryEnd, Category.assoc]

lemma contractibleCycleEnd_idempotent (i : ℤ) :
    contractibleCycleEnd K h i ≫ contractibleCycleEnd K h i =
      contractibleCycleEnd K h i := by
  symm
  calc
    contractibleCycleEnd K h i =
        contractibleCycleEnd K h i ≫
          (contractibleBoundaryEnd K h i + contractibleCycleEnd K h i) := by
      rw [← contractible_homotopy_id_eq K h i, Category.comp_id]
    _ = contractibleCycleEnd K h i ≫ contractibleBoundaryEnd K h i +
          contractibleCycleEnd K h i ≫ contractibleCycleEnd K h i := by
      rw [Preadditive.comp_add]
    _ = contractibleCycleEnd K h i ≫ contractibleCycleEnd K h i := by
      rw [contractibleCycleEnd_comp_boundaryEnd K h i, zero_add]

structure ContractibleCycleSplitting (i : ℤ) where
  Z : C
  incl : Z ⟶ K.X i
  retract : K.X i ⟶ Z
  incl_retract : incl ≫ retract = 𝟙 Z
  retract_incl : retract ≫ incl = contractibleCycleEnd K h i

noncomputable def contractibleCycleSplittingExists [IsIdempotentComplete C] (i : ℤ) :
    ∃ (Z : C) (incl : Z ⟶ K.X i) (retract : K.X i ⟶ Z),
      incl ≫ retract = 𝟙 Z ∧ retract ≫ incl = contractibleCycleEnd K h i :=
  IsIdempotentComplete.idempotents_split (K.X i) (contractibleCycleEnd K h i)
    (contractibleCycleEnd_idempotent K h i)

noncomputable def contractibleCycleSplitting [IsIdempotentComplete C] (i : ℤ) :
    ContractibleCycleSplitting K h i := by
  classical
  let e0 := contractibleCycleSplittingExists K h i
  let Z := Classical.choose e0
  let e1 := Classical.choose_spec e0
  let incl := Classical.choose e1
  let e2 := Classical.choose_spec e1
  let retract := Classical.choose e2
  let e3 := Classical.choose_spec e2
  exact
    { Z := Z
      incl := incl
      retract := retract
      incl_retract := e3.1
      retract_incl := e3.2 }

lemma contractibleCycleSplitting_incl_comp_d [IsIdempotentComplete C] (i : ℤ) :
    (contractibleCycleSplitting K h i).incl ≫ K.d i (i + 1) = 0 := by
  let s := contractibleCycleSplitting K h i
  calc
    s.incl ≫ K.d i (i + 1) = (𝟙 s.Z) ≫ s.incl ≫ K.d i (i + 1) := by
      rw [Category.id_comp]
    _ = (s.incl ≫ s.retract) ≫ s.incl ≫ K.d i (i + 1) := by
      rw [s.incl_retract]
    _ = s.incl ≫ (s.retract ≫ s.incl) ≫ K.d i (i + 1) := by
      simp only [Category.assoc]
    _ = s.incl ≫ contractibleCycleEnd K h i ≫ K.d i (i + 1) := by
      rw [s.retract_incl]
    _ = 0 := by
      rw [contractibleCycleEnd_comp_d K h i]
      simp

lemma contractible_cycle_splitting_section [IsIdempotentComplete C] (i : ℤ) :
    ((contractibleCycleSplitting K h (i + 1)).incl ≫ h.hom (i + 1) i) ≫
      (K.d i (i + 1) ≫ (contractibleCycleSplitting K h (i + 1)).retract) =
        𝟙 (contractibleCycleSplitting K h (i + 1)).Z := by
  let s := contractibleCycleSplitting K h (i + 1)
  calc
    (s.incl ≫ h.hom (i + 1) i) ≫ (K.d i (i + 1) ≫ s.retract) =
        s.incl ≫ (h.hom (i + 1) i ≫ K.d i (i + 1)) ≫ s.retract := by
      simp only [Category.assoc]
    _ = s.incl ≫ contractibleCycleEnd K h (i + 1) ≫ s.retract := by
      rw [contractibleCycleEnd_next]
    _ = s.incl ≫ (s.retract ≫ s.incl) ≫ s.retract := by
      rw [s.retract_incl]
    _ = (s.incl ≫ s.retract) ≫ (s.incl ≫ s.retract) := by
      simp only [Category.assoc]
    _ = 𝟙 s.Z := by
      rw [s.incl_retract, Category.id_comp]

lemma contractible_cycle_splitting_id [IsIdempotentComplete C] (i : ℤ) :
    (contractibleCycleSplitting K h i).retract ≫ (contractibleCycleSplitting K h i).incl +
        (K.d i (i + 1) ≫ (contractibleCycleSplitting K h (i + 1)).retract) ≫
          ((contractibleCycleSplitting K h (i + 1)).incl ≫ h.hom (i + 1) i) =
      𝟙 (K.X i) := by
  let s := contractibleCycleSplitting K h i
  let t := contractibleCycleSplitting K h (i + 1)
  calc
    s.retract ≫ s.incl + (K.d i (i + 1) ≫ t.retract) ≫
        (t.incl ≫ h.hom (i + 1) i) =
        contractibleCycleEnd K h i + K.d i (i + 1) ≫ (t.retract ≫ t.incl) ≫
          h.hom (i + 1) i := by
      rw [s.retract_incl]
      simp only [Category.assoc]
    _ = contractibleCycleEnd K h i + K.d i (i + 1) ≫
          contractibleCycleEnd K h (i + 1) ≫ h.hom (i + 1) i := by
      rw [t.retract_incl]
    _ = contractibleCycleEnd K h i + contractibleBoundaryEnd K h i := by
      rw [contractible_d_comp_cycleEnd_next_assoc K h i]
      rfl
    _ = contractibleBoundaryEnd K h i + contractibleCycleEnd K h i := by
      rw [add_comm]
    _ = 𝟙 (K.X i) := (contractible_homotopy_id_eq K h i).symm

noncomputable def exactAcyclicWithCyclesDataOfContractingHomotopy
    [QuillenExactCategory C] [IsIdempotentComplete C]
    (K : CochainComplex C ℤ) (h : Homotopy (𝟙 K) (0 : K ⟶ K)) :
    ExactAcyclicWithCyclesData C K where
  Z i := (contractibleCycleSplitting K h i).Z
  incl i := (contractibleCycleSplitting K h i).incl
  proj i := K.d i (i + 1) ≫ (contractibleCycleSplitting K h (i + 1)).retract
  zero i := by
    rw [← Category.assoc, contractibleCycleSplitting_incl_comp_d K h i]
    simp
  conflation i := by
    apply QuillenExactCategory.split_conflation
    refine
      { r := (contractibleCycleSplitting K h i).retract
        s := (contractibleCycleSplitting K h (i + 1)).incl ≫ h.hom (i + 1) i
        f_r := (contractibleCycleSplitting K h i).incl_retract
        s_g := contractible_cycle_splitting_section K h i
        id := contractible_cycle_splitting_id K h i }
  d_eq i := by
    calc
      (K.d i (i + 1) ≫ (contractibleCycleSplitting K h (i + 1)).retract) ≫
          (contractibleCycleSplitting K h (i + 1)).incl =
        K.d i (i + 1) ≫ contractibleCycleEnd K h (i + 1) := by
          rw [Category.assoc, (contractibleCycleSplitting K h (i + 1)).retract_incl]
      _ = K.d i (i + 1) := contractible_d_comp_cycleEnd_next K h i

theorem exactAcyclicWithCycles_of_contractingHomotopy
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [IsIdempotentComplete C]
    (K : CochainComplex C ℤ) (h : Homotopy (𝟙 K) (0 : K ⟶ K)) :
    exactAcyclicWithCycles C K :=
  exactAcyclicWithCycles_of_data C (exactAcyclicWithCyclesDataOfContractingHomotopy K h)

theorem MetrizableLCA.exactAcyclicWithCycles_of_contractingHomotopy
    (K : CochainComplex MetrizableLCA.{u} ℤ) (h : Homotopy (𝟙 K) (0 : K ⟶ K)) :
    exactAcyclicWithCycles MetrizableLCA K :=
  exactAcyclicWithCycles_of_data MetrizableLCA
    (exactAcyclicWithCyclesDataOfContractingHomotopy K h)

end LeanLCAExactChallenge
