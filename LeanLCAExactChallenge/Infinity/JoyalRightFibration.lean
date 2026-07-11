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

/-- Two successive preinverses give a genuine inverse.  The second candidate
need not be strictly equal to the original arrow. -/
lemma isIso_of_preinverse_chain
    {C : Type u} [Category C] {x y : C}
    (e : x ⟶ y) (g : y ⟶ x) (e' : x ⟶ y)
    (hge : g ≫ e = 𝟙 y) (he'g : e' ≫ g = 𝟙 x) : IsIso e := by
  have hee' : e = e' := by
    calc
      e = 𝟙 x ≫ e := (Category.id_comp e).symm
      _ = (e' ≫ g) ≫ e := by rw [he'g]
      _ = e' ≫ (g ≫ e) := Category.assoc _ _ _
      _ = e' ≫ 𝟙 y := by rw [hge]
      _ = e' := Category.comp_id e'
  exact ⟨⟨g, hee' ▸ he'g, hge⟩⟩

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

/-- A right fibration lifts an edge once its target vertex has been lifted. -/
lemma RightFibration.hasLiftingProperty_edgeTarget
    {X Y : SSet.{u}} (p : X ⟶ Y) [RightFibration p] :
    HasLiftingProperty
      (SSet.horn 1 (1 : Fin 2)).ι p :=
  RightFibration.hasLiftingProperty p (by simp)

/-- The outer `2`-horn used to lift a chosen preinverse triangle. -/
lemma RightFibration.hasLiftingProperty_preinverseTriangle
    {X Y : SSet.{u}} (p : X ⟶ Y) [RightFibration p] :
    HasLiftingProperty
      (SSet.horn 2 (2 : Fin 3)).ι p :=
  RightFibration.hasLiftingProperty p (by simp)

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

/-- Map-level relative lifting of a right outer `2`-horn. -/
lemma RightFibration.liftHorn₂₂
    {X Y : SSet.{u}} (p : X ⟶ Y) [RightFibration p]
    (f₀₂ f₁₂ : (Δ[1] : SSet.{u}) ⟶ X)
    (hcompat : SSet.stdSimplex.δ 0 ≫ f₀₂ = SSet.stdSimplex.δ 0 ≫ f₁₂)
    (b : (Δ[2] : SSet.{u}) ⟶ Y)
    (hb₀₂ : f₀₂ ≫ p = SSet.stdSimplex.δ 1 ≫ b)
    (hb₁₂ : f₁₂ ≫ p = SSet.stdSimplex.δ 0 ≫ b) :
    ∃ σ : (Δ[2] : SSet.{u}) ⟶ X,
      SSet.stdSimplex.δ 1 ≫ σ = f₀₂ ∧
      SSet.stdSimplex.δ 0 ≫ σ = f₁₂ ∧ σ ≫ p = b := by
  let h : (Λ[2, 2] : SSet.{u}) ⟶ X :=
    SSet.horn₂₂.isPushout.desc f₀₂ f₁₂ hcompat
  have hsquare : h ≫ p = (SSet.horn 2 (2 : Fin 3)).ι ≫ b := by
    apply SSet.horn₂₂.isPushout.hom_ext
    · rw [← Category.assoc, SSet.horn₂₂.isPushout.inl_desc, hb₀₂]
      rfl
    · rw [← Category.assoc, SSet.horn₂₂.isPushout.inr_desc, hb₁₂]
      rfl
  let sq : CommSq h (SSet.horn 2 (2 : Fin 3)).ι p b := ⟨hsquare⟩
  letI : HasLiftingProperty (SSet.horn 2 (2 : Fin 3)).ι p :=
    RightFibration.hasLiftingProperty_preinverseTriangle p
  refine ⟨sq.lift, ?_, ?_, sq.fac_right⟩
  · calc
      SSet.stdSimplex.δ 1 ≫ sq.lift =
          SSet.horn₂₂.ι₀₂ ≫ (SSet.horn 2 (2 : Fin 3)).ι ≫ sq.lift := rfl
      _ = SSet.horn₂₂.ι₀₂ ≫ h := by rw [sq.fac_left]
      _ = f₀₂ := SSet.horn₂₂.isPushout.inl_desc _ _ _
  · calc
      SSet.stdSimplex.δ 0 ≫ sq.lift =
          SSet.horn₂₂.ι₁₂ ≫ (SSet.horn 2 (2 : Fin 3)).ι ≫ sq.lift := rfl
      _ = SSet.horn₂₂.ι₁₂ ≫ h := by rw [sq.fac_left]
      _ = f₁₂ := SSet.horn₂₂.isPushout.inr_desc _ _ _

end LeanLCAExactChallenge.Infinity
