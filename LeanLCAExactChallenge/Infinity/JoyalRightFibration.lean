import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration

/-!
# Right fibrations for the Joyal extension argument

This file introduces the horn-lifting class used in Rezk's proof of the
Joyal extension theorem.  A right fibration lifts every horn whose missing
face is not the initial face.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty Simplicial

/-- Positive-index horn inclusions, including the last horn. -/
inductive rightHornInclusions : MorphismProperty SSet.{u} where
  | intro {n : ℕ} (i : Fin (n + 2)) (h0 : 0 < i) :
      rightHornInclusions Λ[n + 1, i].ι

lemma horn_ι_mem_rightHornInclusions {n : ℕ} {i : Fin (n + 1)}
    (h0 : 0 < i) : rightHornInclusions (SSet.horn.{u} n i).ι := by
  obtain _ | n := n
  · omega
  · exact ⟨i, h0⟩

/-- Right fibrations are maps with the RLP against every positive-index horn. -/
def rightFibrations : MorphismProperty SSet.{u} := rightHornInclusions.rlp
deriving IsMultiplicative, RespectsIso, IsStableUnderBaseChange,
  IsStableUnderRetracts

class RightFibration {X Y : SSet.{u}} (p : X ⟶ Y) : Prop where
  mem : rightFibrations p

lemma RightFibration.hasLiftingProperty
    {X Y : SSet.{u}} (p : X ⟶ Y) [RightFibration p]
    {n : ℕ} {i : Fin (n + 1)} (h0 : 0 < i) :
    HasLiftingProperty (SSet.horn n i).ι p :=
  RightFibration.mem _ (horn_ι_mem_rightHornInclusions h0)

lemma innerHornInclusions_le_rightHornInclusions :
    SSet.innerHornInclusions.{u} ≤ rightHornInclusions.{u} := by
  intro A B f hf
  obtain @⟨n, i, h0, _⟩ := hf
  exact horn_ι_mem_rightHornInclusions h0

lemma rightFibrations_le_innerFibrations :
    rightFibrations.{u} ≤ SSet.innerFibrations.{u} :=
  antitone_rlp innerHornInclusions_le_rightHornInclusions

instance {X Y : SSet.{u}} (p : X ⟶ Y) [RightFibration p] :
    SSet.InnerFibration p :=
  ⟨rightFibrations_le_innerFibrations _ RightFibration.mem⟩

instance rightFibration_comp
    {X Y Z : SSet.{u}} (p : X ⟶ Y) (q : Y ⟶ Z)
    [RightFibration p] [RightFibration q] : RightFibration (p ≫ q) :=
  ⟨rightFibrations.comp_mem p q RightFibration.mem RightFibration.mem⟩

instance rightFibration_pullback_snd
    {X Y Z : SSet.{u}} (p : X ⟶ Z) (q : Y ⟶ Z) [RightFibration p] :
    RightFibration (pullback.snd p q) := by
  refine ⟨?_⟩
  exact rightFibrations.pullback_snd _ _ RightFibration.mem

end LeanLCAExactChallenge.Infinity
