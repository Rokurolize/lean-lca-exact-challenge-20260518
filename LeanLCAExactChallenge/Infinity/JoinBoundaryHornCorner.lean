import LeanLCAExactChallenge.Infinity.SimplicialJoin

/-! # Join boundary-horn corners -/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory Simplicial
open scoped CategoryTheory.MonoidalCategory.DayConvolution MonoidalCategory

/-- The left-block coface in an ordinal sum, with its target arithmetic
transport made explicit. -/
def leftJoinCoface (m n : ℕ) (i : Fin (m + 2)) :
    SimplexCategory.mk (m + n + 1) ⟶
      SimplexCategory.mk ((m + 1) + n + 1) :=
  SimplexCategory.δ (Fin.castLE (by omega) i : Fin (m + n + 3)) ≫
    eqToHom (by
      apply SimplexCategory.ext
      simp
      omega)

/-- Tensoring a left coface with an identity preserves its index in the
ordinal sum, up to the canonical arithmetic transport of the target. -/
lemma augmentedInclusion_leftCoface_tensor (m n : ℕ) (i : Fin (m + 2)) :
    AugmentedSimplexCategory.inclusion.map (SimplexCategory.δ i) ⊗ₘ
        AugmentedSimplexCategory.inclusion.map (𝟙 (SimplexCategory.mk n)) =
      leftJoinCoface m n i := by
  change AugmentedSimplexCategory.tensorHomOf (SimplexCategory.δ i)
      (𝟙 (SimplexCategory.mk n)) = _
  apply SimplexCategory.Hom.ext
  ext k
  change Fin (m + n + 2) at k
  by_cases hk : k.val ≤ m
  · let kl : Fin (m + 1) := ⟨k.val, by omega⟩
    let kc : Fin ((m + 1) + (n + 1)) := Fin.cast (by omega) k
    have hkc : kc.val = k.val := rfl
    have hklt : kc.val < m + 1 := by omega
    have hkl : kc.castLT hklt = kl := by
      ext
      exact hkc
    by_cases hki : kl.castSucc < i
    · have hc : k.castSucc < Fin.castLE (by omega) i := by
        simpa only [Fin.lt_def, Fin.val_castSucc, Fin.val_castLE] using hki
      have hcond : (⟨k.val, by omega⟩ : Fin (m + 2)) < i := by
        simpa [kl] using hki
      simp [leftJoinCoface, AugmentedSimplexCategory.tensorHomOf, SimplexCategory.δ,
        Fin.addCases, Fin.succAbove, hk, kc, kl, hkl, hcond, hc]
    · have hc : ¬ k.castSucc < Fin.castLE (by omega) i := by
        simpa only [Fin.lt_def, Fin.val_castSucc, Fin.val_castLE] using hki
      have hcond : ¬ (⟨k.val, by omega⟩ : Fin (m + 2)) < i := by
        simpa [kl] using hki
      simp [leftJoinCoface, AugmentedSimplexCategory.tensorHomOf, SimplexCategory.δ,
        Fin.addCases, Fin.succAbove, hk, kc, kl, hkl, hcond, hc]
  · have hc : ¬ k.castSucc < Fin.castLE (by omega) i := by
      simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_castLE]
      omega
    simp [leftJoinCoface, AugmentedSimplexCategory.tensorHomOf, SimplexCategory.δ,
      Fin.addCases, Fin.succAbove, hk, hc]
    omega

/-- Naturality of the standard-simplex join isomorphism for a coface in the
left block. -/
theorem simplicialJoinStdSimplexIsoNat_naturality_leftCoface
    (m n : ℕ) (i : Fin (m + 2)) :
    simplicialJoinMap (SSet.stdSimplex.map (SimplexCategory.δ i))
        (𝟙 (Δ[n] : SSet.{u})) ≫
        (simplicialJoinStdSimplexIsoNat (m + 1) n).hom =
      (simplicialJoinStdSimplexIsoNat m n).hom ≫
        SSet.stdSimplex.map (leftJoinCoface m n i) := by
  unfold simplicialJoinStdSimplexIsoNat simplicialJoinStdSimplexIso
  rw [Iso.trans_hom, Iso.trans_hom, ← Category.assoc]
  rw [← SSet.stdSimplex.map_id]
  have hid : (SimplexCategory.Hom.mk OrderHom.id :
      SimplexCategory.mk n ⟶ SimplexCategory.mk n) =
      𝟙 (SimplexCategory.mk n) := by
    apply SimplexCategory.Hom.ext
    rfl
  rw [hid]
  have hraw := simplicialJoinStdSimplexIsoRaw_naturality.{u}
    (SimplexCategory.δ i) (𝟙 (SimplexCategory.mk n))
  rw [hraw]
  rw [augmentedInclusion_leftCoface_tensor]
  rw [Category.assoc, Category.assoc]
  apply (cancel_epi (simplicialJoinStdSimplexIsoRaw.{u}
    (SimplexCategory.mk m) (SimplexCategory.mk n)).hom).2
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro x
  rcases x with ⟨x⟩
  rfl

end LeanLCAExactChallenge.Infinity
