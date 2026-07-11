import LeanLCAExactChallenge.Infinity.SimplicialJoin

/-!
# Positive horns under the right cone join

The right cone `K ⋆ Δ[0]` appends one vertex.  Thus a positive horn index of `K`
becomes an inner horn index in the cone.  This file records the representable coface
calculation used in the right-fibration proof for over-slices.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory Simplicial
open scoped CategoryTheory.MonoidalCategory.DayConvolution MonoidalCategory.ExternalProduct
  MonoidalCategory Simplicial Prod

/-- Tensoring a coface on the left with the identity of the terminal ordinal appends
one vertex and leaves the coface index unchanged. -/
lemma augmentedInclusion_leftCoface_tensor_point (n : ℕ) (i : Fin (n + 2)) :
    AugmentedSimplexCategory.inclusion.map (SimplexCategory.δ i) ⊗ₘ
        AugmentedSimplexCategory.inclusion.map (𝟙 (SimplexCategory.mk 0)) =
      (show AugmentedSimplexCategory.tensorObjOf (SimplexCategory.mk n)
          (SimplexCategory.mk 0) ⟶
          AugmentedSimplexCategory.tensorObjOf (SimplexCategory.mk (n + 1))
            (SimplexCategory.mk 0) from
        SimplexCategory.δ (Fin.castLE (by omega) i : Fin (n + 3))) := by
  change AugmentedSimplexCategory.tensorHomOf (SimplexCategory.δ i)
      (𝟙 (SimplexCategory.mk 0)) = _
  apply SimplexCategory.Hom.ext
  ext k
  change Fin (n + 2) at k
  by_cases hk : k.val ≤ n
  · by_cases hki : k < i
    · have hc : k.castSucc < Fin.castLE (by omega) i := by
        exact hki
      simp [AugmentedSimplexCategory.tensorHomOf, SimplexCategory.δ,
        Fin.addCases, Fin.succAbove, hk, hki, hc]
    · have hc : ¬k.castSucc < Fin.castLE (by omega) i := by
        simpa only [Fin.lt_def, Fin.val_castSucc, Fin.val_castLE] using hki
      simp [AugmentedSimplexCategory.tensorHomOf, SimplexCategory.δ,
        Fin.addCases, Fin.succAbove, hk, hki, hc]
  · have hkval : k.val = n + 1 := by omega
    have hc : ¬k.castSucc < Fin.castLE (by omega) i := by
      simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_castLE]
      omega
    simp [AugmentedSimplexCategory.tensorHomOf, SimplexCategory.δ,
      Fin.addCases, Fin.succAbove, hkval, hc]

/-- Under the standard-simplex join isomorphism, joining a left coface with the
identity of `Δ[0]` is the coface with the same index in the right cone. -/
theorem simplicialJoinStdSimplexIsoNat_naturality_leftCoface_point
    (n : ℕ) (i : Fin (n + 2)) :
    simplicialJoinMap (SSet.stdSimplex.map (SimplexCategory.δ i))
        (𝟙 (Δ[0] : SSet.{u})) ≫
        (simplicialJoinStdSimplexIsoNat (n + 1) 0).hom =
      (simplicialJoinStdSimplexIsoNat n 0).hom ≫
        SSet.stdSimplex.map
          (SimplexCategory.δ (Fin.castLE (by omega) i : Fin (n + 3))) := by
  unfold simplicialJoinStdSimplexIsoNat simplicialJoinStdSimplexIso
  rw [Iso.trans_hom, Iso.trans_hom, ← Category.assoc]
  rw [← SSet.stdSimplex.map_id]
  have hid : (SimplexCategory.Hom.mk OrderHom.id :
      SimplexCategory.mk 0 ⟶ SimplexCategory.mk 0) =
      𝟙 (SimplexCategory.mk 0) := by
    apply SimplexCategory.Hom.ext
    rfl
  rw [hid]
  have hraw := simplicialJoinStdSimplexIsoRaw_naturality.{u}
    (SimplexCategory.δ i) (𝟙 (SimplexCategory.mk 0))
  rw [hraw]
  rw [augmentedInclusion_leftCoface_tensor_point]
  rw [Category.assoc, Category.assoc]
  apply (cancel_epi (simplicialJoinStdSimplexIsoRaw.{u}
    (SimplexCategory.mk n) (SimplexCategory.mk 0)).hom).2
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro x
  rcases x with ⟨x⟩
  rfl

/-- A positive horn index remains nonzero and ceases to be the last index after the
right cone vertex is appended. -/
lemma rightCone_shiftedIndex_isInner {n : ℕ} (i : Fin (n + 2)) (hi : 0 < i) :
    0 < (Fin.castLE (by omega) i : Fin (n + 3)) ∧
      (Fin.castLE (by omega) i : Fin (n + 3)) < Fin.last (n + 2) := by
  constructor
  · exact hi
  · simp only [Fin.lt_def, Fin.val_castLE, Fin.val_last]
    omega

end LeanLCAExactChallenge.Infinity
