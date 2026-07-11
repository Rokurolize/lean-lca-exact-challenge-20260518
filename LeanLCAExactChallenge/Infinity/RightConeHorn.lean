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

open CategoryTheory CategoryTheory.Limits Simplicial
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

private theorem rightCone_rightInclusion_naturality
    (X : SSet.{u}) {Y Y' : SSet.{u}} (g : Y ⟶ Y') :
    g ≫ simplicialJoinRightInclusion X Y' =
      simplicialJoinRightInclusion X Y ≫ simplicialJoinMap (𝟙 X) g := by
  apply NatTrans.ext
  funext U
  let F := emptyAugmentation.{u}.obj X
  let G := emptyAugmentation.{u}.obj Y
  let G' := emptyAugmentation.{u}.obj Y'
  letI := augmentedDayConvolution F G
  letI := augmentedDayConvolution F G'
  letI : Unique (F.obj (Opposite.op WithInitial.star)) :=
    (Limits.Types.isTerminalEquivUnique _) (emptyAugmentationStarIsTerminal X)
  let s : G.obj (AugmentedSimplexCategory.inclusion.op.obj U) ⟶
      (F ⊠ G).obj (Opposite.op WithInitial.star,
        AugmentedSimplexCategory.inclusion.op.obj U) :=
    ConcreteCategory.ofHom (TypeCat.Fun.mk (fun y ↦ (default, y)))
  let s' : G'.obj (AugmentedSimplexCategory.inclusion.op.obj U) ⟶
      (F ⊠ G').obj (Opposite.op WithInitial.star,
        AugmentedSimplexCategory.inclusion.op.obj U) :=
    ConcreteCategory.ofHom (TypeCat.Fun.mk (fun y ↦ (default, y)))
  change (emptyAugmentation.map g).app
      (AugmentedSimplexCategory.inclusion.op.obj U) ≫ s' ≫
      (CategoryTheory.MonoidalCategory.DayConvolution.unit F G').app
        (Opposite.op WithInitial.star, AugmentedSimplexCategory.inclusion.op.obj U) =
    s ≫ (CategoryTheory.MonoidalCategory.DayConvolution.unit F G).app
        (Opposite.op WithInitial.star, AugmentedSimplexCategory.inclusion.op.obj U) ≫
      (CategoryTheory.MonoidalCategory.DayConvolution.map
        (emptyAugmentation.map (𝟙 X)) (emptyAugmentation.map g)).app _
  rw [emptyAugmentation.map_id]
  change _ = s ≫
    (CategoryTheory.MonoidalCategory.DayConvolution.unit F G).app
      (Opposite.op WithInitial.star, AugmentedSimplexCategory.inclusion.op.obj U) ≫
    (CategoryTheory.MonoidalCategory.DayConvolution.map
      (𝟙 F) (emptyAugmentation.map g)).app
        (Opposite.op WithInitial.star ⊗ AugmentedSimplexCategory.inclusion.op.obj U)
  have hmap := CategoryTheory.MonoidalCategory.DayConvolution.unit_app_map_app
    (F := F) (G := G) (F' := F) (G' := G')
    (𝟙 F) (emptyAugmentation.map g)
    (Opposite.op WithInitial.star) (AugmentedSimplexCategory.inclusion.op.obj U)
  rw [hmap]
  have hpref : (emptyAugmentation.map g).app
        (AugmentedSimplexCategory.inclusion.op.obj U) ≫ s' =
      s ≫ (NatTrans.app (𝟙 F) (Opposite.op WithInitial.star) ⊗ₘ
        (emptyAugmentation.map g).app
          (AugmentedSimplexCategory.inclusion.op.obj U)) := by
    apply ConcreteCategory.hom_ext
    intro y
    rfl
  rw [← Category.assoc, hpref]
  exact Category.assoc _ _ _

/-- The pushout-product corner obtained by coning a horn on the left and adjoining
the full base simplex.  Under the standard-simplex join isomorphism this is the
shifted horn inclusion. -/
noncomputable def leftConeHornCornerMap (n : ℕ) (i : Fin (n + 1)) :
    pushout (simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Λ[n, i])
        (SSet.horn n i).ι ⟶ simplicialJoin (Δ[0] : SSet.{u}) Δ[n] :=
  pushout.desc
    (simplicialJoinMap (𝟙 (Δ[0] : SSet.{u})) (SSet.horn n i).ι)
    (simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Δ[n]) (by
      simpa using (rightCone_rightInclusion_naturality
        (Δ[0] : SSet.{u}) (SSet.horn n i).ι).symm)

@[reassoc (attr := simp)]
lemma leftConeHornCornerMap_inl (n : ℕ) (i : Fin (n + 1)) :
    pushout.inl (simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Λ[n, i])
        (SSet.horn n i).ι ≫ leftConeHornCornerMap n i =
      simplicialJoinMap (𝟙 (Δ[0] : SSet.{u})) (SSet.horn n i).ι := by
  apply pushout.inl_desc

@[reassoc (attr := simp)]
lemma leftConeHornCornerMap_inr (n : ℕ) (i : Fin (n + 1)) :
    pushout.inr (simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Λ[n, i])
        (SSet.horn n i).ι ≫ leftConeHornCornerMap n i =
      simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Δ[n] := by
  apply pushout.inr_desc

end LeanLCAExactChallenge.Infinity
