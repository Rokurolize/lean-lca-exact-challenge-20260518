/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.JoyalRightFibration
import LeanLCAExactChallenge.Infinity.SimplicialOppositeHorns

/-!
# Left fibrations and simplicial reversal
-/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory CategoryTheory.MorphismProperty Simplicial

/-- Horn inclusions whose missing vertex is not the final vertex. -/
inductive leftHornInclusions : MorphismProperty SSet.{u} where
  | intro {n : ℕ} (i : Fin (n + 2)) (hn : i < Fin.last (n + 1)) :
      leftHornInclusions Λ[n + 1, i].ι

lemma horn_ι_mem_leftHornInclusions {n : ℕ} {i : Fin (n + 1)}
    (hn : i < Fin.last n) : leftHornInclusions (SSet.horn.{u} n i).ι := by
  obtain _ | n := n
  · omega
  · exact ⟨i, hn⟩

/-- Left fibrations lift all horns except those missing the final face. -/
def leftFibrations : MorphismProperty SSet.{u} := leftHornInclusions.rlp
deriving IsMultiplicative, RespectsIso, IsStableUnderBaseChange,
  IsStableUnderRetracts

class LeftFibration {X Y : SSet.{u}} (p : X ⟶ Y) : Prop where
  mem : leftFibrations p

lemma LeftFibration.hasLiftingProperty
    {X Y : SSet.{u}} (p : X ⟶ Y) [LeftFibration p]
    {n : ℕ} {i : Fin (n + 1)} (hn : i < Fin.last n) :
    HasLiftingProperty (SSet.horn n i).ι p :=
  LeftFibration.mem _ (horn_ι_mem_leftHornInclusions hn)

lemma innerHornInclusions_le_leftHornInclusions :
    SSet.innerHornInclusions.{u} ≤ leftHornInclusions.{u} := by
  intro A B f hf
  cases hf with
  | intro i _h0 hn => exact horn_ι_mem_leftHornInclusions hn

lemma leftFibrations_le_innerFibrations :
    leftFibrations.{u} ≤ SSet.innerFibrations.{u} :=
  antitone_rlp innerHornInclusions_le_leftHornInclusions

instance {X Y : SSet.{u}} (p : X ⟶ Y) [LeftFibration p] :
    SSet.InnerFibration p :=
  ⟨leftFibrations_le_innerFibrations _ LeftFibration.mem⟩

instance leftFibration_comp
    {X Y Z : SSet.{u}} (p : X ⟶ Y) (q : Y ⟶ Z)
    [LeftFibration p] [LeftFibration q] : LeftFibration (p ≫ q) :=
  ⟨leftFibrations.comp_mem p q LeftFibration.mem LeftFibration.mem⟩

instance leftFibration_pullback_snd
    {X Y Z : SSet.{u}} (p : X ⟶ Z) (q : Y ⟶ Z) [LeftFibration p] :
    LeftFibration (Limits.pullback.snd p q) := by
  refine ⟨?_⟩
  exact leftFibrations.pullback_snd _ _ LeftFibration.mem

/-- The total space of a left fibration over a quasicategory is a
quasicategory. -/
theorem quasicategory_of_leftFibration
    {X Y : SSet.{u}} (p : X ⟶ Y) [LeftFibration p] [SSet.Quasicategory Y] :
    SSet.Quasicategory X :=
  SSet.quasicategory_of_innerFibration p

/-- Reversal of a right fibration is a left fibration. -/
noncomputable instance leftFibration_op_of_rightFibration
    {X Y : SSet.{u}} (p : X ⟶ Y) [RightFibration p] :
    LeftFibration (SSet.opFunctor.map p) := by
  refine ⟨?_⟩
  intro A B i hi
  cases hi with
  | intro j hj =>
      apply (hasLiftingProperty_horn_op_iff p _ j).2
      apply RightFibration.hasLiftingProperty p
      simp only [Fin.lt_def, Fin.val_zero, Fin.val_rev, Fin.val_last] at hj ⊢
      omega

/-- Reversal of a left fibration is a right fibration. -/
noncomputable instance rightFibration_op_of_leftFibration
    {X Y : SSet.{u}} (p : X ⟶ Y) [LeftFibration p] :
    RightFibration (SSet.opFunctor.map p) := by
  refine ⟨?_⟩
  intro A B i hi
  cases hi with
  | intro j hj =>
      apply (hasLiftingProperty_horn_op_iff p _ j).2
      apply LeftFibration.hasLiftingProperty p
      simp only [Fin.lt_def, Fin.val_zero, Fin.val_rev, Fin.val_last] at hj ⊢
      omega

/-- Pointwise characterization of the right/left swap under reversal. -/
theorem rightFibration_iff_leftFibration_op {X Y : SSet.{u}} (p : X ⟶ Y) :
    RightFibration p ↔ LeftFibration (SSet.opFunctor.map p) := by
  constructor
  · intro hp
    letI := hp
    infer_instance
  · intro hp
    letI := hp
    haveI : RightFibration (SSet.opFunctor.map (SSet.opFunctor.map p)) := inferInstance
    exact ⟨fun A B i hi ↦ by
      have h := RightFibration.mem
        (p := SSet.opFunctor.map (SSet.opFunctor.map p)) i hi
      exact (HasLiftingProperty.iff_of_arrow_iso_right i (opOpArrowIso p)).1 h⟩

end LeanLCAExactChallenge.Infinity
