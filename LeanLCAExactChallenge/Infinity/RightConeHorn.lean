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

/-- Naturality of the right-factor inclusion, exposed for slice-projection arguments. -/
theorem rightCone_rightInclusion_naturality
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

theorem rightCone_rightInclusion_stdSimplex (n : ℕ) :
    simplicialJoinRightInclusion (Δ[0] : SSet.{u}) (Δ[n] : SSet.{u}) ≫
        (simplicialJoinStdSimplexIsoNat 0 n).hom =
      SSet.stdSimplex.map (standardJoinRightOperator 0 n) := by
  let F := emptyAugmentation.{u}.obj (Δ[0] : SSet.{u})
  let G := emptyAugmentation.{u}.obj (Δ[n] : SSet.{u})
  let h := augmentedDayConvolution F G
  let h' : CategoryTheory.MonoidalCategory.DayConvolution F G :=
    standardSimplexDayConvolution.{u}
      (SimplexCategory.mk 0) (SimplexCategory.mk n)
  letI : Unique (F.obj (Opposite.op WithInitial.star)) :=
    (Limits.Types.isTerminalEquivUnique _) (emptyAugmentationStarIsTerminal (Δ[0] : SSet.{u}))
  let p : AugmentedSimplexCategoryᵒᵖ × AugmentedSimplexCategoryᵒᵖ :=
    (Opposite.op WithInitial.star,
    AugmentedSimplexCategory.inclusion.op.obj (Opposite.op (SimplexCategory.mk n)))
  let y : G.obj (AugmentedSimplexCategory.inclusion.op.obj
      (Opposite.op (SimplexCategory.mk n))) :=
    SSet.yonedaEquiv (𝟙 (Δ[n] : SSet.{u}))
  let input : (F ⊠ G).obj (Opposite.op WithInitial.star,
      AugmentedSimplexCategory.inclusion.op.obj
        (Opposite.op (SimplexCategory.mk n))) := by
    change F.obj (Opposite.op WithInitial.star) ×
      G.obj (AugmentedSimplexCategory.inclusion.op.obj
        (Opposite.op (SimplexCategory.mk n)))
    exact (default, y)
  let chosenValue := by
    exact ConcreteCategory.hom
      ((@CategoryTheory.MonoidalCategory.DayConvolution.unit
        _ _ _ _ _ _ F G h).app p) input
  let stdValue := by
    exact ConcreteCategory.hom
      ((@CategoryTheory.MonoidalCategory.DayConvolution.unit
        _ _ _ _ _ _ F G h').app p) input
  let isoValue := ConcreteCategory.hom ((h.uniqueUpToIso h').hom.app
    ((CategoryTheory.MonoidalCategory.tensor AugmentedSimplexCategoryᵒᵖ).obj p)) chosenValue
  have hvUnique : isoValue = stdValue := by
    let hu := CategoryTheory.MonoidalCategory.DayConvolution.unit_uniqueUpToIso_hom h h'
    have hu0 := congrArg (fun τ ↦ τ.app p) hu
    have hu1 := ConcreteCategory.congr_hom hu0 input
    exact hu1
  have hvStd : stdValue =
      SSet.yonedaEquiv
        (SSet.stdSimplex.map (standardJoinRightOperator 0 n)) := by
    dsimp [stdValue, h', standardSimplexDayConvolution, dayConvolutionOfInputIsos,
      input, y, F, G]
    rw [SSet.yonedaEquiv_map]
    apply ULift.ext
    change ((default : ULift.{u} (WithInitial.star ⟶
      AugmentedSimplexCategory.inclusion.obj (SimplexCategory.mk 0))).down ⊗ₘ
        AugmentedSimplexCategory.inclusion.map (𝟙 (SimplexCategory.mk n))) = _
    have hrhs : (SSet.stdSimplex.objEquiv.{u}.symm
        (standardJoinRightOperator 0 n)).down = standardJoinRightOperator 0 n := rfl
    rw [hrhs]
    apply SimplexCategory.Hom.ext
    ext j
    have ht : (default : ULift.{u} (WithInitial.star ⟶
        AugmentedSimplexCategory.inclusion.obj (SimplexCategory.mk 0))).down ⊗ₘ
          AugmentedSimplexCategory.inclusion.map (𝟙 (SimplexCategory.mk n)) =
        AugmentedSimplexCategory.inr' (SimplexCategory.mk 0)
          (SimplexCategory.mk n) := by rfl
    rw [ht, AugmentedSimplexCategory.inr'_eval]
    rfl
  apply SSet.yonedaEquiv.injective
  dsimp [simplicialJoinRightInclusion, simplicialJoinStdSimplexIsoNat,
    simplicialJoinStdSimplexIso, simplicialJoinStdSimplexIsoRaw]
  rw [SSet.yonedaEquiv_comp]
  change isoValue = SSet.yonedaEquiv
    (SSet.stdSimplex.map (standardJoinRightOperator 0 n))
  exact hvUnique.trans hvStd

lemma range_rightConeBaseLeg (n : ℕ) :
    SSet.Subcomplex.range
      (simplicialJoinRightInclusion (Δ[0] : SSet.{u}) (Δ[n] : SSet.{u}) ≫
        (simplicialJoinStdSimplexIsoNat 0 n).hom) =
      SSet.stdSimplex.face ({(0 : Fin (0 + n + 2))}ᶜ) := by
  rw [rightCone_rightInclusion_stdSimplex]
  let e : (Δ[0 + n] : SSet.{u}) ≅ Δ[n] :=
    SSet.stdSimplex.mapIso (eqToIso (congrArg SimplexCategory.mk (Nat.zero_add n)))
  have he : e.hom ≫ SSet.stdSimplex.map (standardJoinRightOperator 0 n) =
      SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin (0 + n + 2))) := by
    dsimp [e]
    change SSet.stdSimplex.map
        (eqToHom (congrArg SimplexCategory.mk (Nat.zero_add n))) ≫
          SSet.stdSimplex.map (standardJoinRightOperator 0 n) = _
    rw [← Functor.map_comp]
    congr 1
    apply SimplexCategory.Hom.ext
    simp only [SimplexCategory.comp_toOrderHom,
      SimplexCategory.eqToHom_toOrderHom]
    ext j
    simp only [OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe,
      OrderIso.coe_toOrderEmbedding]
    dsimp [e, standardJoinRightOperator, SimplexCategory.δ]
    change 1 + j.val = (Fin.succAboveOrderEmb 0 j).val
    simp [Nat.add_comm]
  rw [subcomplex_range_eq_of_precomp_iso e.hom _ _ he,
    stdSimplex_range_map_delta]

/-- The range of a map out of a pushout is the union of the ranges of its two legs. -/
lemma range_pushout_desc_eq_sup
    {A B C D : SSet.{u}} (f : A ⟶ B) (g : A ⟶ C)
    (h : B ⟶ D) (k : C ⟶ D) (w : f ≫ h = g ≫ k) :
    SSet.Subcomplex.range (pushout.desc h k w) =
      SSet.Subcomplex.range h ⊔ SSet.Subcomplex.range k := by
  let R := SSet.Subcomplex.range h ⊔ SSet.Subcomplex.range k
  let h' : B ⟶ (R : SSet.{u}) :=
    SSet.Subcomplex.toRange h ≫ SSet.Subcomplex.homOfLE le_sup_left
  let k' : C ⟶ (R : SSet.{u}) :=
    SSet.Subcomplex.toRange k ≫ SSet.Subcomplex.homOfLE le_sup_right
  have w' : f ≫ h' = g ≫ k' := by
    apply (cancel_mono R.ι).mp
    simpa [h', k', R, Category.assoc] using w
  let q : pushout f g ⟶ (R : SSet.{u}) := pushout.desc h' k' w'
  have hfac : q ≫ R.ι = pushout.desc h k w := by
    apply pushout.hom_ext
    · rw [← Category.assoc, pushout.inl_desc]
      dsimp only [q, h']
      rw [pushout.inl_desc, Category.assoc, SSet.Subcomplex.homOfLE_ι,
        SSet.Subcomplex.toRange_ι]
    · rw [← Category.assoc, pushout.inr_desc]
      dsimp only [q, k']
      rw [pushout.inr_desc, Category.assoc, SSet.Subcomplex.homOfLE_ι,
        SSet.Subcomplex.toRange_ι]
  apply le_antisymm
  · rw [← hfac, SSet.Subcomplex.range_comp]
    exact (SSet.Subcomplex.image_le_range _ _).trans (by simp [R])
  · apply sup_le
    · have heq : pushout.inl f g ≫ pushout.desc h k w = h := pushout.inl_desc _ _ _
      calc
        SSet.Subcomplex.range h =
            SSet.Subcomplex.range (pushout.inl f g ≫ pushout.desc h k w) :=
          congrArg SSet.Subcomplex.range heq.symm
        _ = (SSet.Subcomplex.range (pushout.inl f g)).image
            (pushout.desc h k w) := SSet.Subcomplex.range_comp _ _
        _ ≤ _ := SSet.Subcomplex.image_le_range _ _
    · have heq : pushout.inr f g ≫ pushout.desc h k w = k := pushout.inr_desc _ _ _
      calc
        SSet.Subcomplex.range k =
            SSet.Subcomplex.range (pushout.inr f g ≫ pushout.desc h k w) :=
          congrArg SSet.Subcomplex.range heq.symm
        _ = (SSet.Subcomplex.range (pushout.inr f g)).image
            (pushout.desc h k w) := SSet.Subcomplex.range_comp _ _
        _ ≤ _ := SSet.Subcomplex.image_le_range _ _

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

/-- The cone-horn corner transported to its standard ambient simplex. -/
noncomputable def leftConeHornCornerStdMap (n : ℕ) (i : Fin (n + 1)) :
    pushout (simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Λ[n, i])
        (SSet.horn n i).ι ⟶ Δ[0 + n + 1] :=
  leftConeHornCornerMap n i ≫ (simplicialJoinStdSimplexIsoNat 0 n).hom

lemma range_leftConeHornCornerStdMap_eq_sup (n : ℕ) (i : Fin (n + 1)) :
    SSet.Subcomplex.range (leftConeHornCornerStdMap.{u} n i) =
      representableJoinHornInitial 0 n i ⊔
        SSet.stdSimplex.face ({(0 : Fin (0 + n + 2))}ᶜ) := by
  let f := simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Λ[n, i]
  let g := (SSet.horn n i).ι
  let h := simplicialJoinMap (𝟙 (Δ[0] : SSet.{u})) g ≫
    (simplicialJoinStdSimplexIsoNat 0 n).hom
  let k := simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Δ[n] ≫
    (simplicialJoinStdSimplexIsoNat 0 n).hom
  have w : f ≫ h = g ≫ k := by
    dsimp only [f, g, h, k]
    rw [← Category.assoc, ← rightCone_rightInclusion_naturality]
    rw [Category.assoc]
  have hm : leftConeHornCornerStdMap n i = pushout.desc h k w := by
    apply pushout.hom_ext
    · rw [pushout.inl_desc]
      dsimp only [leftConeHornCornerStdMap]
      rw [← Category.assoc, leftConeHornCornerMap_inl]
    · rw [pushout.inr_desc]
      dsimp only [leftConeHornCornerStdMap]
      rw [← Category.assoc, leftConeHornCornerMap_inr]
  rw [hm, range_pushout_desc_eq_sup]
  change representableJoinHornInitial 0 n i ⊔ _ = _
  rw [range_rightConeBaseLeg]

set_option maxHeartbeats 800000 in
lemma representableJoinHornInitial_sup_baseFace_eq_shiftedHorn
    (r : ℕ) (i : Fin (r + 2)) :
    representableJoinHornInitial.{u} 0 (r + 1) i ⊔
        SSet.stdSimplex.face ({(0 : Fin (0 + (r + 1) + 2))}ᶜ) =
      SSet.horn (0 + (r + 1) + 1)
        (⟨i.val + 1, by omega⟩ : Fin (0 + (r + 1) + 2)) := by
  rw [representableJoinHornInitial_eq_iSup_shiftedRightFaces,
    SSet.horn_eq_iSup]
  apply le_antisymm
  · apply sup_le
    · apply iSup_le
      rintro ⟨j, hj⟩
      exact SSet.face_le_horn
        (⟨j.val + 1, by omega⟩ : Fin (0 + (r + 1) + 2))
        (⟨i.val + 1, by omega⟩ : Fin (0 + (r + 1) + 2)) (by
        intro h
        have : j = i := by
          apply Fin.ext
          simpa only [Fin.mk.injEq] using congrArg Fin.val h
        exact hj (by simpa using this))
    · exact SSet.face_le_horn
        (0 : Fin (0 + (r + 1) + 2))
        (⟨i.val + 1, by omega⟩ : Fin (0 + (r + 1) + 2)) (by
          intro h
          have := congrArg Fin.val h
          simp only [Fin.val_zero, Fin.val_mk] at this
          omega)
  · apply iSup_le
    rintro ⟨j, hj⟩
    revert hj
    refine Fin.cases ?_ (fun k hj => ?_) j
    · intro _
      exact le_sup_right
    · apply le_sup_of_le_left
      exact le_iSup (fun q : ({i}ᶜ : Set (Fin (r + 2))) =>
        SSet.stdSimplex.face
          ({(⟨0 + 1 + q.1.val, by omega⟩ :
            Fin (0 + (r + 1) + 2))}ᶜ)) ⟨k, by
          intro hki
          apply hj
          apply Fin.ext
          simp only [Fin.val_succ, Fin.val_mk]
          simpa using congrArg Fin.val hki⟩

lemma range_leftConeHornCornerStdMap_eq_shiftedHorn
    (n : ℕ) (i : Fin (n + 1)) (hi : i < Fin.last n) :
    SSet.Subcomplex.range (leftConeHornCornerStdMap.{u} n i) =
      SSet.horn (n + 1) i.succ := by
  cases n with
  | zero => omega
  | succ r =>
      rw [range_leftConeHornCornerStdMap_eq_sup]
      simpa only [Nat.zero_add, Nat.succ_eq_add_one, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using
        representableJoinHornInitial_sup_baseFace_eq_shiftedHorn (u := u) r i

lemma emptyJoinCell_zero_eq_baseFace (r : ℕ) :
    SSet.Subcomplex.ofSimplex
        (joinSigmaOneSimplex.{u} 0 (r + 1) (∅ : Finset (Fin 1))) =
      SSet.stdSimplex.face ({(0 : Fin (0 + (r + 1) + 2))}ᶜ) := by
  rw [← joinSigmaOneFace_eq_ofSimplex]
  congr 1
  ext x
  simp [joinSigmaOneVertices, joinFirstVertices, joinSecondVertices]

lemma range_horn_comp_rightConeBase_eq_emptyHornRange
    (r : ℕ) (i : Fin (r + 2)) :
    SSet.Subcomplex.range
        ((SSet.horn (r + 1) i).ι ≫
          simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Δ[r + 1] ≫
          (simplicialJoinStdSimplexIsoNat 0 (r + 1)).hom) =
      joinSigmaOneHornRange 0 (r + 1) (∅ : Finset (Fin 1)) i := by
  rw [← Category.assoc, rightCone_rightInclusion_stdSimplex]
  rw [SSet.Subcomplex.range_comp, SSet.horn_eq_iSup,
    SSet.Subcomplex.image_iSup]
  rw [joinSigmaOneHornRange_eq_iSup_erasedFaces]
  congr 1
  funext j
  rw [← stdSimplex_range_map_delta j.1, ← SSet.Subcomplex.range_comp]
  congr 1
  apply SimplexCategory.Hom.ext
  ext k
  simp [standardJoinRightOperator, SimplexCategory.δ,
    joinSigmaOne, joinSigmaOneVertices, joinFirstVertices,
    joinSecondVertices, joinSigmaOneDistinguishedIndex]

noncomputable def leftConeHornRangeBicartSq (r : ℕ) (i : Fin (r + 2)) :
    SSet.Subcomplex.BicartSq
      (SSet.Subcomplex.range
        ((SSet.horn (r + 1) i).ι ≫
          simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Δ[r + 1] ≫
          (simplicialJoinStdSimplexIsoNat 0 (r + 1)).hom))
      (representableJoinHornInitial 0 (r + 1) i)
      (SSet.stdSimplex.face ({(0 : Fin (0 + (r + 1) + 2))}ᶜ))
      (representableJoinHornInitial 0 (r + 1) i ⊔
        SSet.stdSimplex.face ({(0 : Fin (0 + (r + 1) + 2))}ᶜ)) where
  sup_eq := rfl
  inf_eq := by
    rw [range_horn_comp_rightConeBase_eq_emptyHornRange,
      ← emptyJoinCell_zero_eq_baseFace,
      initial_inf_emptyJoinCell_eq_hornRange]

noncomputable def leftConeHornSourceIsPushoutRange
    (r : ℕ) (i : Fin (r + 2)) :
    let f := simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Λ[r + 1, i]
    let g := (SSet.horn (r + 1) i).ι
    let h := representableJoinHornMap.{u} 0 (r + 1) i
    let k := simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Δ[r + 1] ≫
      (simplicialJoinStdSimplexIsoNat 0 (r + 1)).hom
    let sq := leftConeHornRangeBicartSq.{u} r i
    IsPushout f g
      (SSet.Subcomplex.toRange h ≫ SSet.Subcomplex.homOfLE sq.le₂₄)
      (SSet.Subcomplex.toRange k ≫ SSet.Subcomplex.homOfLE sq.le₃₄) := by
  dsimp only
  let f := simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Λ[r + 1, i]
  let g := (SSet.horn (r + 1) i).ι
  let h := representableJoinHornMap.{u} 0 (r + 1) i
  let k := simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Δ[r + 1] ≫
    (simplicialJoinStdSimplexIsoNat 0 (r + 1)).hom
  let sq := leftConeHornRangeBicartSq.{u} r i
  let e₁ := simplicialSetIsoRangeOfMono (g ≫ k)
  let e₂ := simplicialSetIsoRangeOfMono h
  let e₃ := simplicialSetIsoRangeOfMono k
  refine sq.isPushout.of_iso' e₁ e₂ e₃ (Iso.refl _) ?_ ?_ ?_ ?_
  · apply (cancel_mono (SSet.Subcomplex.range h).ι).mp
    simp [e₁, e₂, f, g, h, k, sq, simplicialSetIsoRangeOfMono,
      Category.assoc]
  · apply (cancel_mono (SSet.Subcomplex.range k).ι).mp
    simp [e₁, e₃, g, k, sq, simplicialSetIsoRangeOfMono,
      Category.assoc]
  · simp [e₂, h, sq, simplicialSetIsoRangeOfMono, Category.assoc]
  · simp [e₃, k, sq, simplicialSetIsoRangeOfMono, Category.assoc]

noncomputable def leftConeHornSourceRangeIso (r : ℕ) (i : Fin (r + 2)) :
    pushout (simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Λ[r + 1, i])
        (SSet.horn (r + 1) i).ι ≅
      ((representableJoinHornInitial 0 (r + 1) i ⊔
        SSet.stdSimplex.face ({(0 : Fin (0 + (r + 1) + 2))}ᶜ)) : SSet.{u}) :=
  (leftConeHornSourceIsPushoutRange.{u} r i).isoPushout.symm

lemma leftConeHornSourceRangeIso_hom_ι (r : ℕ) (i : Fin (r + 2)) :
    (leftConeHornSourceRangeIso.{u} r i).hom ≫
        (representableJoinHornInitial 0 (r + 1) i ⊔
          SSet.stdSimplex.face ({(0 : Fin (0 + (r + 1) + 2))}ᶜ)).ι =
      leftConeHornCornerStdMap (r + 1) i := by
  apply pushout.hom_ext
  · rw [← Category.assoc]
    rw [leftConeHornSourceRangeIso, Iso.symm_hom,
      IsPushout.inl_isoPushout_inv]
    simp [representableJoinHornMap, leftConeHornCornerStdMap,
      Category.assoc]
  · rw [← Category.assoc]
    rw [leftConeHornSourceRangeIso, Iso.symm_hom,
      IsPushout.inr_isoPushout_inv]
    simp [leftConeHornCornerStdMap, Category.assoc]

noncomputable instance leftConeHornCornerStdMap_mono
    (r : ℕ) (i : Fin (r + 2)) :
    Mono (leftConeHornCornerStdMap.{u} (r + 1) i) := by
  rw [← leftConeHornSourceRangeIso_hom_ι (u := u) r i]
  infer_instance

lemma leftConeHornCornerStdMap_innerAnodyne
    (n : ℕ) (i : Fin (n + 1)) (hi : i < Fin.last n) :
    SSet.innerAnodyneExtensions (leftConeHornCornerStdMap.{u} n i) := by
  cases n with
  | zero => omega
  | succ r =>
      let D := representableJoinHornInitial 0 (r + 1) i ⊔
        SSet.stdSimplex.face ({(0 : Fin (0 + (r + 1) + 2))}ᶜ)
      have hD : D = SSet.horn (0 + (r + 1) + 1)
          (⟨i.val + 1, by omega⟩ : Fin (0 + (r + 1) + 2)) :=
        representableJoinHornInitial_sup_baseFace_eq_shiftedHorn r i
      have hι : SSet.innerAnodyneExtensions D.ι := by
        rw [hD]
        exact SSet.innerAnodyneExtensions.horn_ι (by omega) (by
          simpa only [Fin.lt_iff_val_lt_val, Fin.val_mk, Fin.val_last] using hi)
      have he := SSet.innerAnodyneExtensions.of_isIso
        (leftConeHornSourceRangeIso.{u} r i).hom
      have hc := SSet.innerAnodyneExtensions.comp_mem _ _ he hι
      rw [leftConeHornSourceRangeIso_hom_ι] at hc
      exact hc

lemma leftConeHornCornerMap_innerAnodyne
    (n : ℕ) (i : Fin (n + 1)) (hi : i < Fin.last n) :
    SSet.innerAnodyneExtensions (leftConeHornCornerMap.{u} n i) := by
  have hs := leftConeHornCornerStdMap_innerAnodyne (u := u) n i hi
  have he := SSet.innerAnodyneExtensions.of_isIso
    (simplicialJoinStdSimplexIsoNat 0 n).inv
  have hc := SSet.innerAnodyneExtensions.comp_mem _ _ hs he
  change SSet.innerAnodyneExtensions
    ((leftConeHornCornerMap n i ≫
      (simplicialJoinStdSimplexIsoNat 0 n).hom) ≫
      (simplicialJoinStdSimplexIsoNat 0 n).inv) at hc
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hc

end LeanLCAExactChallenge.Infinity
