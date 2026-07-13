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
  exact simplicialJoinRightInclusion_stdSimplex 0 n

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
      exact le_iSup (fun q :
        ({(⟨i.val + 1, by omega⟩ : Fin (0 + (r + 1) + 2))}ᶜ :
          Set (Fin (0 + (r + 1) + 2))) =>
        SSet.stdSimplex.face ({q.1}ᶜ))
        ⟨⟨0 + 1 + j.val, by omega⟩, by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          intro h
          apply hj
          apply Fin.ext
          have hv := congrArg Fin.val h
          simp only [Fin.val_mk] at hv
          omega⟩
    · exact le_iSup (fun q :
        ({(⟨i.val + 1, by omega⟩ : Fin (0 + (r + 1) + 2))}ᶜ :
          Set (Fin (0 + (r + 1) + 2))) =>
        SSet.stdSimplex.face ({q.1}ᶜ)) ⟨0, by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          intro h
          have hv := congrArg Fin.val h
          simp only [Fin.val_zero, Fin.val_mk] at hv
          omega⟩
  · apply iSup_le
    rintro ⟨j, hj⟩
    by_cases hj0 : j = 0
    · subst j
      exact le_sup_right
    · let k : Fin (r + 2) := ⟨j.val - 1, by
          have hjpos : 0 < j.val := Fin.pos_iff_ne_zero.mpr hj0
          omega⟩
      have hface :
          (⟨0 + 1 + k.val, by omega⟩ : Fin (0 + (r + 1) + 2)) = j := by
        apply Fin.ext
        have hjpos : 0 < j.val := Fin.pos_iff_ne_zero.mpr hj0
        dsimp [k]
        omega
      have hki : k ≠ i := by
        intro h
        apply hj
        simp only [Set.mem_singleton_iff]
        apply Fin.ext
        have hv := congrArg Fin.val h
        have hf := congrArg Fin.val hface
        dsimp [k] at hv hf
        simp only [Fin.val_mk] at hf ⊢
        omega
      have hle : SSet.stdSimplex.face
          ({(⟨0 + 1 + k.val, by omega⟩ : Fin (0 + (r + 1) + 2))}ᶜ) ≤
          (⨆ q : ({i}ᶜ : Set (Fin (r + 2))), SSet.stdSimplex.face
            ({(⟨0 + 1 + q.1.val, by omega⟩ :
              Fin (0 + (r + 1) + 2))}ᶜ)) ⊔
            SSet.stdSimplex.face ({(0 : Fin (0 + (r + 1) + 2))}ᶜ) :=
        le_sup_of_le_left (le_iSup (fun q : ({i}ᶜ : Set (Fin (r + 2))) =>
          SSet.stdSimplex.face
            ({(⟨0 + 1 + q.1.val, by omega⟩ :
              Fin (0 + (r + 1) + 2))}ᶜ)) ⟨k, by simpa using hki⟩)
      convert hle using 1
      simp only [Subtype.coe_eta]
      rw [hface]

lemma emptyJoinCell_zero_eq_baseFace (r : ℕ) :
    SSet.Subcomplex.ofSimplex
        (joinSigmaOneSimplex.{u} 0 (r + 1) (∅ : Finset (Fin 1))) =
      SSet.stdSimplex.face ({(0 : Fin (0 + (r + 1) + 2))}ᶜ) := by
  rw [← joinSigmaOneFace_eq_ofSimplex]
  congr 1
  ext x
  simp [joinSigmaOneVertices, joinFirstVertices, joinSecondVertices]
  constructor
  · rintro ⟨a, rfl⟩
    simp
  · intro hx
    obtain rfl | ⟨a, rfl⟩ := Fin.eq_zero_or_eq_succ x
    · exact (hx rfl).elim
    · exact ⟨⟨a.val, by omega⟩, by apply Fin.ext; simp [Nat.add_comm]⟩

noncomputable def hornOneZeroIsoPoint :
    (Λ[1, (0 : Fin 2)] : SSet.{u}) ≅ Δ[0] := by
  let f : ∀ (j : Fin 2) (_ : j ≠ (0 : Fin 2)),
      (Δ[0] : SSet.{u}) ⟶ Δ[0] := fun _ _ ↦ 𝟙 _
  have hf : SSet.horn.IsCompatible f := by trivial
  refine
    { hom := hf.desc
      inv := SSet.horn.ι (0 : Fin 2) (1 : Fin 2) (by decide)
      hom_inv_id := ?_
      inv_hom_id := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _ }
  apply SSet.horn.hom_ext'
  intro j hj
  have hj1 : j = (1 : Fin 2) := by
    rcases Fin.eq_zero_or_eq_succ j with h | ⟨k, rfl⟩
    · exact (hj h).elim
    · have hk : k = 0 := Fin.eq_zero k
      subst k
      rfl
  subst j
  rw [← Category.assoc, hf.ι_desc]
  simp [f]

noncomputable def pointJoinHornOneZeroIso :
    simplicialJoin (Δ[0] : SSet.{u}) Λ[1, (0 : Fin 2)] ≅
      simplicialJoin (Δ[0] : SSet.{u}) Δ[0] := by
  letI : IsIso (hornOneZeroIsoPoint.{u}.hom) :=
    hornOneZeroIsoPoint.isIso_hom
  have hi := ordinaryJoinBifunctor_map_isIso
    (𝟙 (Δ[0] : SSet.{u})) hornOneZeroIsoPoint.hom
  change IsIso (simplicialJoinMap (𝟙 (Δ[0] : SSet.{u}))
    hornOneZeroIsoPoint.hom) at hi
  letI := hi
  exact asIso (simplicialJoinMap (𝟙 (Δ[0] : SSet.{u}))
    hornOneZeroIsoPoint.hom)

@[simp]
lemma pointJoinHornOneZeroIso_hom :
    (pointJoinHornOneZeroIso.{u}).hom =
      simplicialJoinMap (𝟙 (Δ[0] : SSet.{u})) hornOneZeroIsoPoint.hom := by
  rfl

lemma hornOneZeroIsoPoint_hom_comp_coface :
    hornOneZeroIsoPoint.{u}.hom ≫
        SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) =
      (SSet.horn 1 (0 : Fin 2)).ι := by
  apply (cancel_epi hornOneZeroIsoPoint.inv).mp
  rw [Iso.inv_hom_id_assoc]
  simp [hornOneZeroIsoPoint]
  rfl

/-- The one-dimensional horn at index one is a point. -/
noncomputable def hornOneOneIsoPoint :
    (Λ[1, (1 : Fin 2)] : SSet.{u}) ≅ Δ[0] := by
  let f : ∀ (j : Fin 2) (_ : j ≠ (1 : Fin 2)),
      (Δ[0] : SSet.{u}) ⟶ Δ[0] := fun _ _ ↦ 𝟙 _
  have hf : SSet.horn.IsCompatible f := by trivial
  refine
    { hom := hf.desc
      inv := SSet.horn.ι (1 : Fin 2) (0 : Fin 2) (by decide)
      hom_inv_id := ?_
      inv_hom_id := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _ }
  apply SSet.horn.hom_ext'
  intro j hj
  have hj0 : j = (0 : Fin 2) := by
    rcases Fin.eq_zero_or_eq_succ j with h | ⟨k, rfl⟩
    · exact h
    · have hk : k = 0 := Fin.eq_zero k
      subst k
      exact (hj rfl).elim
  subst j
  rw [← Category.assoc, hf.ι_desc]
  simp [f]

lemma hornOneOneIsoPoint_hom_comp_coface :
    hornOneOneIsoPoint.{u}.hom ≫
        SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) =
      (SSet.horn 1 (1 : Fin 2)).ι := by
  apply (cancel_epi hornOneOneIsoPoint.inv).mp
  rw [Iso.inv_hom_id_assoc]
  simp [hornOneOneIsoPoint]
  rfl

/-- A representable left factor joined with the zero-index one-dimensional horn maps monically
to the ambient representable join. -/
noncomputable instance representableJoinHornMap_one_zero_mono (m : ℕ) :
    Mono (representableJoinHornMap.{u} m 1 (0 : Fin 2)) := by
  let e := simplicialJoinMap (𝟙 (Δ[m] : SSet.{u}))
    hornOneZeroIsoPoint.hom
  haveI : IsIso e := by
    dsimp [e]
    apply ordinaryJoinBifunctor_map_isIso
  let q := simplicialJoinMap (𝟙 (Δ[m] : SSet.{u}))
      (SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2))) ≫
    (simplicialJoinStdSimplexIsoNat m 1).hom
  haveI : Mono q := by
    dsimp [q]
    rw [simplicialJoinStdSimplexIsoNat_naturality_rightCoface]
    haveI : Mono (SSet.stdSimplex.map
        (SimplexCategory.δ
          (⟨m + 1 + (1 : Fin 2).val, by omega⟩ : Fin (m + 3)))) := by
      change Mono (SSet.stdSimplex.δ
        (⟨m + 1 + (1 : Fin 2).val, by omega⟩ : Fin (m + 3)))
      infer_instance
    infer_instance
  have heq : representableJoinHornMap.{u} m 1 (0 : Fin 2) = e ≫ q := by
    unfold representableJoinHornMap
    dsimp [e, q]
    rw [← Category.assoc]
    change ordinaryJoinBifunctor.{u}.map
          ((𝟙 (Δ[m] : SSet.{u}), (SSet.horn 1 (0 : Fin 2)).ι) :
            ((Δ[m] : SSet.{u}), (Λ[1, (0 : Fin 2)] : SSet.{u})) ⟶
              ((Δ[m] : SSet.{u}), (Δ[1] : SSet.{u}))) ≫ _ =
      (ordinaryJoinBifunctor.{u}.map
          ((𝟙 (Δ[m] : SSet.{u}), hornOneZeroIsoPoint.hom) :
            ((Δ[m] : SSet.{u}), (Λ[1, (0 : Fin 2)] : SSet.{u})) ⟶
              ((Δ[m] : SSet.{u}), (Δ[0] : SSet.{u}))) ≫
        ordinaryJoinBifunctor.{u}.map
          ((𝟙 (Δ[m] : SSet.{u}),
            SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2))) :
            ((Δ[m] : SSet.{u}), (Δ[0] : SSet.{u})) ⟶
              ((Δ[m] : SSet.{u}), (Δ[1] : SSet.{u})))) ≫ _
    rw [← ordinaryJoinBifunctor.map_comp]
    congr 2
    ext <;> simp [hornOneZeroIsoPoint_hom_comp_coface]
  rw [heq]
  infer_instance

/-- A representable left factor joined with the one-index one-dimensional horn maps monically to
the ambient representable join. -/
noncomputable instance representableJoinHornMap_one_one_mono (m : ℕ) :
    Mono (representableJoinHornMap.{u} m 1 (1 : Fin 2)) := by
  let e := simplicialJoinMap (𝟙 (Δ[m] : SSet.{u}))
    hornOneOneIsoPoint.hom
  haveI : IsIso e := by
    dsimp [e]
    apply ordinaryJoinBifunctor_map_isIso
  let q := simplicialJoinMap (𝟙 (Δ[m] : SSet.{u}))
      (SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2))) ≫
    (simplicialJoinStdSimplexIsoNat m 1).hom
  haveI : Mono q := by
    dsimp [q]
    rw [simplicialJoinStdSimplexIsoNat_naturality_rightCoface]
    haveI : Mono (SSet.stdSimplex.map
        (SimplexCategory.δ
          (⟨m + 1 + (0 : Fin 2).val, by omega⟩ : Fin (m + 3)))) := by
      change Mono (SSet.stdSimplex.δ
        (⟨m + 1 + (0 : Fin 2).val, by omega⟩ : Fin (m + 3)))
      infer_instance
    infer_instance
  have heq : representableJoinHornMap.{u} m 1 (1 : Fin 2) = e ≫ q := by
    unfold representableJoinHornMap
    dsimp [e, q]
    rw [← Category.assoc]
    change ordinaryJoinBifunctor.{u}.map
          ((𝟙 (Δ[m] : SSet.{u}), (SSet.horn 1 (1 : Fin 2)).ι) :
            ((Δ[m] : SSet.{u}), (Λ[1, (1 : Fin 2)] : SSet.{u})) ⟶
              ((Δ[m] : SSet.{u}), (Δ[1] : SSet.{u}))) ≫ _ =
      (ordinaryJoinBifunctor.{u}.map
          ((𝟙 (Δ[m] : SSet.{u}), hornOneOneIsoPoint.hom) :
            ((Δ[m] : SSet.{u}), (Λ[1, (1 : Fin 2)] : SSet.{u})) ⟶
              ((Δ[m] : SSet.{u}), (Δ[0] : SSet.{u}))) ≫
        ordinaryJoinBifunctor.{u}.map
          ((𝟙 (Δ[m] : SSet.{u}),
            SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2))) :
            ((Δ[m] : SSet.{u}), (Δ[0] : SSet.{u})) ⟶
              ((Δ[m] : SSet.{u}), (Δ[1] : SSet.{u})))) ≫ _
    rw [← ordinaryJoinBifunctor.map_comp]
    congr 2
    ext <;> simp [hornOneOneIsoPoint_hom_comp_coface]
  rw [heq]
  infer_instance

lemma pointJoinHornOneZeroIso_hom_comp_rightCoface :
    pointJoinHornOneZeroIso.{u}.hom ≫
        simplicialJoinMap (𝟙 (Δ[0] : SSet.{u}))
          (SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2))) =
      simplicialJoinMap (𝟙 (Δ[0] : SSet.{u}))
        (SSet.horn 1 (0 : Fin 2)).ι := by
  rw [pointJoinHornOneZeroIso_hom]
  let F := augmentedDayTensorLeft
    (emptyAugmentation.{u}.obj (Δ[0] : SSet.{u}))
  have hmid :
      forgetAugmentation.{u}.map
          (F.map (emptyAugmentation.{u}.map hornOneZeroIsoPoint.hom)) ≫
          forgetAugmentation.{u}.map
            (F.map (emptyAugmentation.{u}.map
              (SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2))))) =
        forgetAugmentation.{u}.map
          (F.map (emptyAugmentation.{u}.map
            (SSet.horn 1 (0 : Fin 2)).ι)) := by
    rw [← forgetAugmentation.map_comp, ← F.map_comp,
      ← emptyAugmentation.map_comp,
      hornOneZeroIsoPoint_hom_comp_coface]
  calc
    _ = forgetAugmentation.{u}.map
          (F.map (emptyAugmentation.{u}.map hornOneZeroIsoPoint.hom)) ≫
        forgetAugmentation.{u}.map
          (F.map (emptyAugmentation.{u}.map
            (SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2))))) :=
      congrArg₂ (fun a b ↦ a ≫ b)
        (simplicialJoinMap_id_eq_augmentedDayTensorLeft_map
          (Δ[0] : SSet.{u}) hornOneZeroIsoPoint.hom)
        (simplicialJoinMap_id_eq_augmentedDayTensorLeft_map
          (Δ[0] : SSet.{u})
            (SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2))))
    _ = _ := hmid
    _ = _ := (simplicialJoinMap_id_eq_augmentedDayTensorLeft_map
      (Δ[0] : SSet.{u}) (SSet.horn 1 (0 : Fin 2)).ι).symm

lemma representableJoinHornInitial_zero_one_zero :
    representableJoinHornInitial.{u} 0 1 (0 : Fin 2) =
      SSet.stdSimplex.face ({(2 : Fin 3)}ᶜ) := by
  rw [representableJoinHornInitial_eq_iSup_shiftedRightFaces 0 0]
  apply le_antisymm
  · apply iSup_le
    rintro ⟨j, hj⟩
    have hj1 : j = (1 : Fin 2) := by
      rcases Fin.eq_zero_or_eq_succ j with h | ⟨k, rfl⟩
      · exact (hj h).elim
      · have hk : k = 0 := Fin.eq_zero k
        subst k
        rfl
    subst j
    exact le_rfl
  · exact le_iSup (fun j : ({(0 : Fin 2)}ᶜ : Set (Fin 2)) ↦
      SSet.stdSimplex.face
        ({(⟨0 + 1 + j.1.val, by omega⟩ : Fin (0 + (0 + 1) + 2))}ᶜ))
      ⟨1, by decide⟩

noncomputable def pointJoinHornOneZeroInitialIso :
    simplicialJoin (Δ[0] : SSet.{u}) Λ[1, (0 : Fin 2)] ≅
      (representableJoinHornInitial 0 1 (0 : Fin 2) : SSet.{u}) :=
  pointJoinHornOneZeroIso.{u} ≪≫
    simplicialJoinStdSimplexIsoNat 0 0 ≪≫
    SSet.stdSimplex.faceSingletonComplIso (2 : Fin 3) ≪≫
    (eqToIso (congrArg (fun S : (Δ[2] : SSet.{u}).Subcomplex ↦ (S : SSet.{u}))
      representableJoinHornInitial_zero_one_zero)).symm

lemma eqToIso_subcomplex_symm_hom_ι {n : ℕ}
    {X Y : (Δ[n] : SSet.{u}).Subcomplex} (h : X = Y) :
    (eqToIso (congrArg
      (fun S : (Δ[n] : SSet.{u}).Subcomplex ↦ (S : SSet.{u})) h)).symm.hom ≫
      X.ι = Y.ι := by
  subst Y
  simp

lemma pointJoinHornOneZeroInitialIso_hom_ι :
    (pointJoinHornOneZeroInitialIso.{u}).hom ≫
        (representableJoinHornInitial 0 1 (0 : Fin 2)).ι =
      (pointJoinHornOneZeroIso.{u} ≪≫
        simplicialJoinStdSimplexIsoNat 0 0 ≪≫
        SSet.stdSimplex.faceSingletonComplIso (2 : Fin 3)).hom ≫
          (SSet.stdSimplex.face ({(2 : Fin 3)}ᶜ)).ι := by
  unfold pointJoinHornOneZeroInitialIso
  simp only [Iso.trans_hom, Category.assoc]
  rw [eqToIso_subcomplex_symm_hom_ι
    representableJoinHornInitial_zero_one_zero]

/-- The canonical range square underlying the cone-horn corner. -/
noncomputable def leftConeHornCanonicalBicartSq (r : ℕ) (i : Fin (r + 2)) :
    SSet.Subcomplex.BicartSq
      (joinSigmaOneHornRange 0 (r + 1) (∅ : Finset (Fin 1)) i)
      (representableJoinHornInitial 0 (r + 1) i)
      (SSet.stdSimplex.face
        (joinSigmaOneVertices 0 (r + 1) (∅ : Finset (Fin 1))))
      (representableJoinHornInitial 0 (r + 1) i ⊔
        SSet.stdSimplex.face
          (joinSigmaOneVertices 0 (r + 1) (∅ : Finset (Fin 1)))) where
  sup_eq := rfl
  inf_eq := by
    rw [joinSigmaOneFace_eq_ofSimplex]
    exact initial_inf_emptyJoinCell_eq_hornRange 0 r i

/- The source-normalization iso is constructed together with the transported square below.
noncomputable def emptyJoinHornIsoRange (r : ℕ) (i : Fin (r + 2)) :
    (Λ[r + 1, i] : SSet.{u}) ≅
      (joinSigmaOneHornRange 0 (r + 1) (∅ : Finset (Fin 1)) i : SSet.{u}) := by
  convert joinSigmaOneHornIsoRange 0 (r + 1) (∅ : Finset (Fin 1)) i using 1 <;>
    simp only [Finset.card_empty, Nat.zero_add,
      joinSigmaOneDistinguishedIndex]
-/

noncomputable def emptyJoinFaceIso (r : ℕ) :
    (Δ[r + 1] : SSet.{u}) ≅
      (SSet.stdSimplex.face
        (joinSigmaOneVertices 0 (r + 1) (∅ : Finset (Fin 1))) : SSet.{u}) := by
  exact SSet.stdSimplex.isoOfRepresentableBy
    (SSet.stdSimplex.faceRepresentableBy
      (joinSigmaOneVertices 0 (r + 1) (∅ : Finset (Fin 1))) (r + 1)
      ((joinSigmaOneVertices 0 (r + 1) (∅ : Finset (Fin 1))).orderIsoOfFin (by
        rw [card_joinSigmaOneVertices]
        simp)))

lemma emptyJoinFaceIso_hom_ι (r : ℕ) :
    (emptyJoinFaceIso.{u} r).hom ≫
        (SSet.stdSimplex.face
          (joinSigmaOneVertices 0 (r + 1) (∅ : Finset (Fin 1)))).ι =
      SSet.stdSimplex.map (standardJoinRightOperator 0 (r + 1)) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_map]
  apply ULift.ext
  apply SimplexCategory.Hom.ext
  ext j
  simp [emptyJoinFaceIso, joinSigmaOneFaceIso, SSet.stdSimplex.isoOfRepresentableBy,
    SSet.stdSimplex.faceRepresentableBy, joinSigmaOneVertices,
    joinFirstVertices, joinSecondVertices, standardJoinRightOperator]
  let e : Fin (r + 2) ↪o Fin (0 + (r + 1) + 2) :=
    { toFun := fun (k : Fin (r + 2)) => ⟨1 + k.val, by omega⟩
      inj' := by
        intro a b h
        apply Fin.ext
        simpa using congrArg Fin.val h
      map_rel_iff' := by
        intro a b
        change (1 + a.val ≤ 1 + b.val) ↔ a.val ≤ b.val
        omega }
  have he : e =
      (joinSigmaOneVertices 0 (r + 1) (∅ : Finset (Fin 1))).orderEmbOfFin (by
        rw [card_joinSigmaOneVertices]
        simp) := by
    apply Finset.orderEmbOfFin_unique'
    intro a
    simp [joinSigmaOneVertices, joinFirstVertices, joinSecondVertices, e]
  exact congrArg Fin.val (congrArg (fun f ↦ f j) he.symm)

lemma hornOneZeroIsoPoint_inv_comp_joinSigmaOneHornMap :
    hornOneZeroIsoPoint.{u}.inv ≫
        joinSigmaOneHornMap 0 1 (∅ : Finset (Fin 1)) (0 : Fin 2) =
      SSet.const (X := Δ[0])
        (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 3)) := by
  unfold joinSigmaOneHornMap
  change hornOneZeroIsoPoint.inv ≫ (SSet.horn 1 (0 : Fin 2)).ι ≫
      (emptyJoinFaceIso 0).hom ≫
      (SSet.stdSimplex.face
        (joinSigmaOneVertices 0 1 (∅ : Finset (Fin 1)))).ι = _
  rw [emptyJoinFaceIso_hom_ι]
  simp only [hornOneZeroIsoPoint, SSet.horn.ι_ι_assoc]
  rw [SSet.stdSimplex.δ_one_eq_const, SSet.const_comp]
  congr 2

noncomputable def positiveJoinHornIsoRange (s : ℕ) (i : Fin (s + 3)) :
    simplicialJoin (Δ[0] : SSet.{u}) Λ[s + 2, i] ≅
      (representableJoinHornInitial 0 (s + 2) i : SSet.{u}) := by
  change (representableJoinHornCocone.{u} 0 i).pt ≅
    (representableJoinHornRangeCoconePrecompose.{u} 0 s i).pt
  exact representableJoinHornPointIso 0 s i

noncomputable def normalizedEmptyJoinHornIso (r : ℕ) (i : Fin (r + 2)) :
    (Λ[r + 1, i] : SSet.{u}) ≅
      (SSet.horn (0 + (r + 1))
        (Fin.cast (congrArg (fun n => n + 1) (Nat.zero_add (r + 1)).symm) i) :
        SSet.{u}) := by
  let hN : 0 + (r + 1) = r + 1 := Nat.zero_add _
  let a : Σ n : ℕ, Fin (n + 1) := ⟨r + 1, i⟩
  let b : Σ n : ℕ, Fin (n + 1) :=
    ⟨0 + (r + 1), Fin.cast (congrArg (fun n => n + 1) hN.symm) i⟩
  have hab : a = b := by
    apply Sigma.ext hN.symm
    apply (Fin.heq_ext_iff (congrArg (fun n => n + 1) hN.symm)).2
    simp [a, b]
  have h : (SSet.horn (r + 1) i : SSet.{u}) =
      (SSet.horn (0 + (r + 1))
        (Fin.cast (congrArg (fun n => n + 1) hN.symm) i) : SSet.{u}) := by
    exact congrArg (fun p : Σ n : ℕ, Fin (n + 1) =>
      (SSet.horn p.1 p.2 : SSet.{u})) hab
  exact eqToIso h

noncomputable def emptyJoinHornIsoRange (r : ℕ) (i : Fin (r + 2)) :
    (Λ[r + 1, i] : SSet.{u}) ≅
      (joinSigmaOneHornRange 0 (r + 1) (∅ : Finset (Fin 1)) i : SSet.{u}) := by
  let iRaw := Fin.cast
    (congrArg (fun n => n + 1) (Nat.zero_add (r + 1)).symm) i
  let iJoin := joinSigmaOneDistinguishedIndex (r + 1)
    (∅ : Finset (Fin 1)) i
  have hidx : iRaw = iJoin := by
    apply Fin.ext
    simp [iRaw, iJoin, joinSigmaOneDistinguishedIndex]
  exact normalizedEmptyJoinHornIso r i ≪≫
    eqToIso (congrArg (fun j =>
      (SSet.horn (0 + (r + 1)) j : SSet.{u})) hidx) ≪≫
    joinSigmaOneHornIsoRange 0 (r + 1) (∅ : Finset (Fin 1)) i

lemma eqToHom_app_heq {X Y : SSet.{u}} (h : X = Y) (U : SimplexCategoryᵒᵖ)
    (x : X.obj U) : HEq ((eqToHom h).app U x) x := by
  cases h
  rfl

lemma normalizedEmptyJoinHornIso_hom_app_heq (r : ℕ) (i : Fin (r + 2))
    (U : SimplexCategoryᵒᵖ) (x : (Λ[r + 1, i] : SSet.{u}).obj U) :
    HEq ((normalizedEmptyJoinHornIso.{u} r i).hom.app U x) x := by
  let hN : 0 + (r + 1) = r + 1 := Nat.zero_add _
  let a : Σ n : ℕ, Fin (n + 1) := ⟨r + 1, i⟩
  let b : Σ n : ℕ, Fin (n + 1) :=
    ⟨0 + (r + 1), Fin.cast (congrArg (fun n => n + 1) hN.symm) i⟩
  have hab : a = b := by
    apply Sigma.ext hN.symm
    apply (Fin.heq_ext_iff (congrArg (fun n => n + 1) hN.symm)).2
    simp [a, b]
  have h : (SSet.horn (r + 1) i : SSet.{u}) =
      (SSet.horn (0 + (r + 1))
        (Fin.cast (congrArg (fun n => n + 1) hN.symm) i) : SSet.{u}) := by
    exact congrArg (fun p : Σ n : ℕ, Fin (n + 1) =>
      (SSet.horn p.1 p.2 : SSet.{u})) hab
  change HEq ((eqToHom h).app U x) x
  exact eqToHom_app_heq h U x

lemma eqToIso_horn_index_hom_ι (n : ℕ) {i j : Fin (n + 1)} (h : i = j) :
    (eqToIso (congrArg (fun k ↦ (SSet.horn n k : SSet.{u})) h)).hom ≫
      (SSet.horn n j).ι = (SSet.horn n i).ι := by
  subst j
  simp

noncomputable def positiveConeHornTransportedLeftLeg
    (s : ℕ) (i : Fin (s + 3)) :
    (Λ[s + 2, i] : SSet.{u}) ⟶ simplicialJoin (Δ[0] : SSet.{u}) Λ[s + 2, i] :=
  (emptyJoinHornIsoRange (s + 1) i).hom ≫
    SSet.Subcomplex.homOfLE
      (leftConeHornCanonicalBicartSq (s + 1) i).le₁₂ ≫
    (positiveJoinHornIsoRange s i).inv

noncomputable def positiveConeHornTransportedRightLeg
    (s : ℕ) (i : Fin (s + 3)) :
    (Λ[s + 2, i] : SSet.{u}) ⟶ Δ[s + 2] :=
  (emptyJoinHornIsoRange (s + 1) i).hom ≫
    SSet.Subcomplex.homOfLE
      (leftConeHornCanonicalBicartSq (s + 1) i).le₁₃ ≫
    (emptyJoinFaceIso (s + 1)).inv

noncomputable def positiveConeHornTransportedIsPushout
    (s : ℕ) (i : Fin (s + 3)) :
    let sq := leftConeHornCanonicalBicartSq.{u} (s + 1) i
    IsPushout
      (positiveConeHornTransportedLeftLeg s i)
      (positiveConeHornTransportedRightLeg s i)
      ((positiveJoinHornIsoRange s i).hom ≫
        SSet.Subcomplex.homOfLE sq.le₂₄)
      ((emptyJoinFaceIso (s + 1)).hom ≫
        SSet.Subcomplex.homOfLE sq.le₃₄) := by
  dsimp only
  let sq := leftConeHornCanonicalBicartSq.{u} (s + 1) i
  refine sq.isPushout.of_iso'
    (emptyJoinHornIsoRange (s + 1) i)
    (positiveJoinHornIsoRange s i)
    (emptyJoinFaceIso (s + 1)) (Iso.refl _) ?_ ?_ ?_ ?_
  all_goals simp [positiveConeHornTransportedLeftLeg,
    positiveConeHornTransportedRightLeg, sq, Category.assoc]

set_option maxHeartbeats 800000 in
noncomputable def smallConeHornStandardIsPushout :
    IsPushout
      (simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Λ[1, (0 : Fin 2)])
      (SSet.horn 1 (0 : Fin 2)).ι
      ((pointJoinHornOneZeroInitialIso.{u}).hom ≫
        SSet.Subcomplex.homOfLE
          (leftConeHornCanonicalBicartSq 0 (0 : Fin 2)).le₂₄)
      ((emptyJoinFaceIso 0).hom ≫
        SSet.Subcomplex.homOfLE
          (leftConeHornCanonicalBicartSq 0 (0 : Fin 2)).le₃₄) := by
  let sq := leftConeHornCanonicalBicartSq.{u} 0 (0 : Fin 2)
  refine sq.isPushout.of_iso'
    (emptyJoinHornIsoRange 0 (0 : Fin 2))
    pointJoinHornOneZeroInitialIso
    (emptyJoinFaceIso 0) (Iso.refl _) ?_ ?_ ?_ ?_
  · apply (cancel_mono (representableJoinHornInitial 0 1 (0 : Fin 2)).ι).mp
    simp only [Category.assoc, SSet.Subcomplex.homOfLE_ι]
    unfold emptyJoinHornIsoRange
    simp only [Iso.trans_hom, ← Category.assoc]
    dsimp [joinSigmaOneHornIsoRange, joinSigmaOneHornRange]
    rw [Category.assoc, SSet.Subcomplex.toRange_ι]
    apply (cancel_epi (hornOneZeroIsoPoint.{u}).inv).mp
    have hjoin : (hornOneZeroIsoPoint.{u}).inv ≫
        simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Λ[1, (0 : Fin 2)] ≫
        simplicialJoinMap (𝟙 (Δ[0] : SSet.{u})) hornOneZeroIsoPoint.hom =
        simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Δ[0] := by
      calc
        _ = hornOneZeroIsoPoint.inv ≫
            (simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Λ[1, (0 : Fin 2)] ≫
              simplicialJoinMap (𝟙 (Δ[0] : SSet.{u}))
                hornOneZeroIsoPoint.hom) := rfl
        _ = hornOneZeroIsoPoint.inv ≫
            (hornOneZeroIsoPoint.hom ≫
              simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Δ[0]) :=
          congrArg (fun k ↦ hornOneZeroIsoPoint.inv ≫ k)
            (rightCone_rightInclusion_naturality
              (Δ[0] : SSet.{u}) hornOneZeroIsoPoint.hom).symm
        _ = (hornOneZeroIsoPoint.inv ≫ hornOneZeroIsoPoint.hom) ≫
            simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Δ[0] :=
          (Category.assoc _ _ _).symm
        _ = _ := by rw [Iso.inv_hom_id, Category.id_comp]
    simp only [Category.assoc]
    rw [pointJoinHornOneZeroInitialIso_hom_ι]
    simp only [Iso.trans_hom, pointJoinHornOneZeroIso_hom]
    simp only [← Category.assoc] at hjoin ⊢
    rw [hjoin]
    rw [rightCone_rightInclusion_stdSimplex]
    apply SSet.yonedaEquiv.injective
    simp_rw [SSet.yonedaEquiv_comp]
    apply ULift.ext
    apply SimplexCategory.Hom.ext
    ext k
    let U : SimplexCategoryᵒᵖ := Opposite.op ⦋0⦌
    let x := SSet.yonedaEquiv (hornOneZeroIsoPoint.{u}.inv)
    let iRaw := Fin.cast
      (congrArg (fun n ↦ n + 1) (Nat.zero_add (0 + 1)).symm) (0 : Fin 2)
    let iJoin := joinSigmaOneDistinguishedIndex (0 + 1)
      (∅ : Finset (Fin 1)) (0 : Fin 2)
    have hidx : iRaw = iJoin := by
      apply Fin.ext
      simp [iRaw, iJoin, joinSigmaOneDistinguishedIndex]
    have hn := normalizedEmptyJoinHornIso_hom_app_heq
      0 (0 : Fin 2) U x
    have hi := eqToHom_app_heq
      (congrArg (fun j ↦ (SSet.horn (0 + (0 + 1)) j : SSet.{u})) hidx)
      U ((normalizedEmptyJoinHornIso 0 (0 : Fin 2)).hom.app U x)
    have ht := hi.trans hn
    simp only [emptyJoinHornIsoRange, Iso.trans_hom, Category.assoc]
    have ht' := eq_of_heq ht
    have ht'' := congrArg
      (fun y ↦ (joinSigmaOneHornMap 0 1
        (∅ : Finset (Fin 1)) (0 : Fin 2)).app U y) ht'
    have ht''' := congrArg
      (fun y ↦ Fin.val ((SimplexCategory.Hom.toOrderHom y.down) k)) ht''
    dsimp [U, x] at ht'''
    refine ht'''.trans ?_
    have hy := congrArg SSet.yonedaEquiv
      hornOneZeroIsoPoint_inv_comp_joinSigmaOneHornMap.{u}
    simp only [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_map] at hy
    have hyval := congrArg
      (fun y ↦ Fin.val ((SimplexCategory.Hom.toOrderHom y.down) (0 : Fin 1))) hy
    simp only [SSet.stdSimplex.objEquiv_symm_apply] at hyval
    simp [pointJoinHornOneZeroIso, hornOneZeroIsoPoint,
      pointJoinHornOneZeroInitialIso, emptyJoinHornIsoRange,
      normalizedEmptyJoinHornIso, joinSigmaOneHornIsoRange,
      joinSigmaOneHornRange, joinSigmaOneHornMap,
      representableJoinHornInitial_zero_one_zero, Category.assoc]
    have hk : k = 0 := Fin.eq_zero k
    subst k
    let e : Fin 2 ↪o Fin 3 :=
      { toFun := fun k ↦ ⟨1 + k.val, by omega⟩
        inj' := by
          intro a b h
          apply Fin.ext
          simpa using congrArg Fin.val h
        map_rel_iff' := by
          intro a b
          change (1 + a.val ≤ 1 + b.val) ↔ a.val ≤ b.val
          omega }
    have he : e =
        (joinSigmaOneVertices 0 1 (∅ : Finset (Fin 1))).orderEmbOfFin (by
          rw [card_joinSigmaOneVertices]
          simp) := by
      apply Finset.orderEmbOfFin_unique'
      intro a
      simp [joinSigmaOneVertices, joinFirstVertices, joinSecondVertices, e]
    let e' : Fin 2 ↪o Fin 3 :=
      { toFun := fun k ↦ ⟨k.val, by omega⟩
        inj' := by
          intro a b h
          apply Fin.ext
          simpa using congrArg Fin.val h
        map_rel_iff' := by
          intro a b
          rfl }
    have he' : e' =
        (SSet.stdSimplex.finSuccAboveOrderIsoFinset
          (2 : Fin 3)).toOrderEmbedding.comp (OrderEmbedding.subtype _) := by
      apply DFunLike.ext
      intro a
      apply Fin.ext
      change a.val = ((2 : Fin 3).succAbove a).val
      rw [show (2 : Fin 3) = Fin.last 2 by rfl, Fin.succAbove_last_apply]
      rfl
    have hv :
        (joinSigmaOneVertices 0 1 (∅ : Finset (Fin 1))).orderEmbOfFin (by
            rw [card_joinSigmaOneVertices]
            simp) (0 : Fin 2) =
          (SSet.stdSimplex.finSuccAboveOrderIsoFinset
              (2 : Fin 3)).toOrderEmbedding.comp
            (OrderEmbedding.subtype _) (1 : Fin 2) := by
      rw [← he, ← he']
      rfl
    simp [emptyJoinHornIsoRange, normalizedEmptyJoinHornIso,
      joinSigmaOneHornIsoRange, joinSigmaOneHornRange, joinSigmaOneHornMap,
      pointJoinHornOneZeroInitialIso,
      joinSigmaOneFaceIso, SSet.stdSimplex.faceSingletonComplIso,
      SSet.stdSimplex.isoOfRepresentableBy,
      SSet.stdSimplex.faceRepresentableBy, standardJoinRightOperator,
      joinSigmaOneVertices, joinFirstVertices, joinSecondVertices,
      SSet.yonedaEquiv_map, SimplexCategory.eqToHom_toOrderHom]
    convert congrArg Fin.val hv using 1
    · exact hyval.trans (congrArg Fin.val
        (congrArg (fun f ↦ f (0 : Fin 2)) he))
    · change (1 : ℕ) = 1
      rfl
  · apply (cancel_mono (SSet.stdSimplex.face
      (joinSigmaOneVertices 0 1 (∅ : Finset (Fin 1)))).ι).mp
    apply SSet.horn.hom_ext'
    intro j hj
    have hj1 : j = (1 : Fin 2) := by
      rcases Fin.eq_zero_or_eq_succ j with h | ⟨k, rfl⟩
      · exact (hj h).elim
      · have hk : k = 0 := Fin.eq_zero k
        subst k
        rfl
    subst j
    simp [sq, Category.assoc, emptyJoinHornIsoRange,
      normalizedEmptyJoinHornIso, emptyJoinFaceIso,
      joinSigmaOneHornIsoRange, joinSigmaOneHornRange,
      joinSigmaOneHornMap]
    apply SSet.yonedaEquiv.injective
    apply ULift.ext
    apply SimplexCategory.Hom.ext
    ext k
    simp [emptyJoinHornIsoRange, normalizedEmptyJoinHornIso,
      emptyJoinFaceIso, joinSigmaOneHornIsoRange,
      joinSigmaOneHornRange, joinSigmaOneHornMap, Category.assoc]
    have hk : k = 0 := Fin.eq_zero k
    subst k
    rfl
  · change _ = _ ≫ 𝟙 _
    rw [Category.comp_id]
  · change _ = _ ≫ 𝟙 _
    rw [Category.comp_id]

noncomputable def smallCanonicalConeHornApex : SSet.{u} :=
  ((representableJoinHornInitial 0 1 (0 : Fin 2) ⊔
    SSet.stdSimplex.face
      (joinSigmaOneVertices 0 1 (∅ : Finset (Fin 1))) :
    (Δ[2] : SSet.{u}).Subcomplex) : SSet.{u})

noncomputable def smallCanonicalConeHornCornerMap :
    smallCanonicalConeHornApex.{u} ⟶
      simplicialJoin (Δ[0] : SSet.{u}) Δ[1] :=
  (representableJoinHornInitial 0 1 (0 : Fin 2) ⊔
      SSet.stdSimplex.face
        (joinSigmaOneVertices 0 1 (∅ : Finset (Fin 1)))).ι ≫
    (simplicialJoinStdSimplexIsoNat 0 1).inv

noncomputable def smallConeHornStandardPushoutIso :
    smallCanonicalConeHornApex.{u} ≅
      pushout
        (simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Λ[1, (0 : Fin 2)])
        (SSet.horn 1 (0 : Fin 2)).ι :=
  (smallConeHornStandardIsPushout.{u}).isoPushout

@[reassoc]
lemma smallConeHornStandardPushoutIso_inl_factor :
    pushout.inl
        (simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Λ[1, (0 : Fin 2)])
        (SSet.horn 1 (0 : Fin 2)).ι ≫
      smallConeHornStandardPushoutIso.{u}.inv =
    pointJoinHornOneZeroInitialIso.hom ≫
      SSet.Subcomplex.homOfLE
        (leftConeHornCanonicalBicartSq 0 (0 : Fin 2)).le₂₄ :=
  (smallConeHornStandardIsPushout.{u}).inl_isoPushout_inv

@[reassoc]
lemma smallConeHornStandardPushoutIso_inr_factor :
    pushout.inr
        (simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Λ[1, (0 : Fin 2)])
        (SSet.horn 1 (0 : Fin 2)).ι ≫
      smallConeHornStandardPushoutIso.{u}.inv =
    (emptyJoinFaceIso 0).hom ≫
      SSet.Subcomplex.homOfLE
        (leftConeHornCanonicalBicartSq 0 (0 : Fin 2)).le₃₄ :=
  (smallConeHornStandardIsPushout.{u}).inr_isoPushout_inv

noncomputable def smallConeHornStandardCornerMap :
    pushout
        (simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Λ[1, (0 : Fin 2)])
        (SSet.horn 1 (0 : Fin 2)).ι ⟶
      simplicialJoin (Δ[0] : SSet.{u}) Δ[1] :=
  smallConeHornStandardPushoutIso.{u}.inv ≫
    smallCanonicalConeHornCornerMap

@[reassoc]
lemma smallConeHornStandardCornerMap_inl :
    pushout.inl
        (simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Λ[1, (0 : Fin 2)])
        (SSet.horn 1 (0 : Fin 2)).ι ≫
      smallConeHornStandardCornerMap =
    simplicialJoinMap (𝟙 (Δ[0] : SSet.{u}))
      (SSet.horn 1 (0 : Fin 2)).ι := by
  unfold smallConeHornStandardCornerMap
  rw [← Category.assoc, smallConeHornStandardPushoutIso_inl_factor]
  apply (cancel_mono (simplicialJoinStdSimplexIsoNat 0 1).hom).mp
  unfold smallCanonicalConeHornCornerMap
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  calc
    _ = pointJoinHornOneZeroInitialIso.hom ≫
        (SSet.Subcomplex.homOfLE
          (leftConeHornCanonicalBicartSq 0 (0 : Fin 2)).le₂₄ ≫
          (representableJoinHornInitial 0 1 (0 : Fin 2) ⊔
            SSet.stdSimplex.face
              (joinSigmaOneVertices 0 1 (∅ : Finset (Fin 1)))).ι) :=
      Category.assoc _ _ _
    _ = pointJoinHornOneZeroInitialIso.hom ≫
        (representableJoinHornInitial 0 1 (0 : Fin 2)).ι := by
      exact congrArg (fun k ↦ pointJoinHornOneZeroInitialIso.hom ≫ k)
        (SSet.Subcomplex.homOfLE_ι _)
    _ = _ := by
      rw [pointJoinHornOneZeroInitialIso_hom_ι]
      simp only [Iso.trans_hom, Category.assoc,
        SSet.stdSimplex.faceSingletonComplIso_hom_ι]
      have hnat :
          simplicialJoinMap (𝟙 (Δ[0] : SSet.{u}))
              (SSet.stdSimplex.map
                (SimplexCategory.δ (1 : Fin 2))) ≫
              (simplicialJoinStdSimplexIsoNat 0 1).hom =
            (simplicialJoinStdSimplexIsoNat 0 0).hom ≫
              SSet.stdSimplex.map
                (SimplexCategory.δ (2 : Fin 3)) :=
        simplicialJoinStdSimplexIsoNat_naturality_rightCoface
          0 0 (1 : Fin 2)
      change pointJoinHornOneZeroIso.hom ≫
          (simplicialJoinStdSimplexIsoNat 0 0).hom ≫
            SSet.stdSimplex.map (SimplexCategory.δ (2 : Fin 3)) = _
      rw [← hnat]
      rw [← Category.assoc,
        pointJoinHornOneZeroIso_hom_comp_rightCoface]

@[reassoc]
lemma smallConeHornStandardCornerMap_inr :
    pushout.inr
        (simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Λ[1, (0 : Fin 2)])
        (SSet.horn 1 (0 : Fin 2)).ι ≫
      smallConeHornStandardCornerMap =
    simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Δ[1] := by
  unfold smallConeHornStandardCornerMap
  rw [← Category.assoc, smallConeHornStandardPushoutIso_inr_factor]
  apply (cancel_mono (simplicialJoinStdSimplexIsoNat 0 1).hom).mp
  unfold smallCanonicalConeHornCornerMap
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    rightCone_rightInclusion_stdSimplex]
  calc
    _ = (emptyJoinFaceIso 0).hom ≫
        (SSet.Subcomplex.homOfLE
          (leftConeHornCanonicalBicartSq 0 (0 : Fin 2)).le₃₄ ≫
          (representableJoinHornInitial 0 1 (0 : Fin 2) ⊔
            SSet.stdSimplex.face
              (joinSigmaOneVertices 0 1 (∅ : Finset (Fin 1)))).ι) :=
      Category.assoc _ _ _
    _ = (emptyJoinFaceIso 0).hom ≫
        (SSet.stdSimplex.face
          (joinSigmaOneVertices 0 1 (∅ : Finset (Fin 1)))).ι := by
      exact congrArg (fun k ↦ (emptyJoinFaceIso 0).hom ≫ k)
        (SSet.Subcomplex.homOfLE_ι _)
    _ = _ := emptyJoinFaceIso_hom_ι 0

lemma smallCanonicalConeHornCornerMap_innerAnodyne :
    SSet.innerAnodyneExtensions
      smallCanonicalConeHornCornerMap.{u} := by
  let D := representableJoinHornInitial 0 1 (0 : Fin 2) ⊔
    SSet.stdSimplex.face
      (joinSigmaOneVertices 0 1 (∅ : Finset (Fin 1)))
  have hface : SSet.stdSimplex.face
      (joinSigmaOneVertices 0 1 (∅ : Finset (Fin 1))) =
      SSet.stdSimplex.face ({(0 : Fin 3)}ᶜ) := by
    congr 1
  have hD : D = SSet.horn 2 (1 : Fin 3) := by
    dsimp [D]
    rw [hface]
    simpa using representableJoinHornInitial_sup_baseFace_eq_shiftedHorn
      0 (0 : Fin 2)
  have hι : SSet.innerAnodyneExtensions D.ι := by
    rw [hD]
    exact SSet.innerAnodyneExtensions.horn_ι (by decide) (by decide)
  exact SSet.innerAnodyneExtensions.comp_mem _ _ hι
    (SSet.innerAnodyneExtensions.of_isIso
      (simplicialJoinStdSimplexIsoNat 0 1).inv)

lemma smallConeHornStandardCornerMap_innerAnodyne :
    SSet.innerAnodyneExtensions
      smallConeHornStandardCornerMap.{u} := by
  exact SSet.innerAnodyneExtensions.comp_mem _ _
    (SSet.innerAnodyneExtensions.of_isIso
      smallConeHornStandardPushoutIso.{u}.inv)
    smallCanonicalConeHornCornerMap_innerAnodyne

lemma positiveConeHornTransported_w (s : ℕ) (i : Fin (s + 3)) :
    positiveConeHornTransportedLeftLeg.{u} s i ≫
        ((positiveJoinHornIsoRange s i).hom ≫
          SSet.Subcomplex.homOfLE
            (leftConeHornCanonicalBicartSq (s + 1) i).le₂₄) =
      positiveConeHornTransportedRightLeg s i ≫
        ((emptyJoinFaceIso (s + 1)).hom ≫
          SSet.Subcomplex.homOfLE
            (leftConeHornCanonicalBicartSq (s + 1) i).le₃₄) :=
  (positiveConeHornTransportedIsPushout.{u} s i).w

lemma positiveConeHornTransported_compat_of_original
    (s : ℕ) (i : Fin (s + 3)) {Q : SSet.{u}}
    (f : (representableJoinHornInitial 0 (s + 2) i : SSet.{u}) ⟶ Q)
    (g : (SSet.stdSimplex.face
      (joinSigmaOneVertices 0 (s + 2) (∅ : Finset (Fin 1))) : SSet.{u}) ⟶ Q)
    (h : SSet.Subcomplex.homOfLE
          (leftConeHornCanonicalBicartSq (s + 1) i).le₁₂ ≫ f =
      SSet.Subcomplex.homOfLE
          (leftConeHornCanonicalBicartSq (s + 1) i).le₁₃ ≫ g) :
    positiveConeHornTransportedLeftLeg s i ≫
        (positiveJoinHornIsoRange s i).hom ≫ f =
      positiveConeHornTransportedRightLeg s i ≫
        (emptyJoinFaceIso (s + 1)).hom ≫ g := by
  simp [positiveConeHornTransportedLeftLeg,
    positiveConeHornTransportedRightLeg, Category.assoc]
  exact h

noncomputable def positiveConeHornTransportedDesc
    (s : ℕ) (i : Fin (s + 3)) {Q : SSet.{u}}
    (u : simplicialJoin (Δ[0] : SSet.{u}) Λ[s + 2, i] ⟶ Q)
    (v : Δ[s + 2] ⟶ Q)
    (h : positiveConeHornTransportedLeftLeg s i ≫ u =
      positiveConeHornTransportedRightLeg s i ≫ v) :
    ((representableJoinHornInitial 0 (s + 2) i ⊔
      SSet.stdSimplex.face
        (joinSigmaOneVertices 0 (s + 2) (∅ : Finset (Fin 1))) :
        (Δ[0 + (s + 2) + 1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ Q :=
  (positiveConeHornTransportedIsPushout s i).desc u v h

@[reassoc]
lemma positiveConeHornTransported_inl_desc
    (s : ℕ) (i : Fin (s + 3)) {Q : SSet.{u}}
    (u : simplicialJoin (Δ[0] : SSet.{u}) Λ[s + 2, i] ⟶ Q)
    (v : Δ[s + 2] ⟶ Q)
    (h : positiveConeHornTransportedLeftLeg s i ≫ u =
      positiveConeHornTransportedRightLeg s i ≫ v) :
    ((positiveJoinHornIsoRange s i).hom ≫
        SSet.Subcomplex.homOfLE
          (leftConeHornCanonicalBicartSq (s + 1) i).le₂₄) ≫
      positiveConeHornTransportedDesc s i u v h = u :=
  (positiveConeHornTransportedIsPushout s i).inl_desc _ _ _

@[reassoc]
lemma positiveConeHornTransported_inr_desc
    (s : ℕ) (i : Fin (s + 3)) {Q : SSet.{u}}
    (u : simplicialJoin (Δ[0] : SSet.{u}) Λ[s + 2, i] ⟶ Q)
    (v : Δ[s + 2] ⟶ Q)
    (h : positiveConeHornTransportedLeftLeg s i ≫ u =
      positiveConeHornTransportedRightLeg s i ≫ v) :
    ((emptyJoinFaceIso (s + 1)).hom ≫
        SSet.Subcomplex.homOfLE
          (leftConeHornCanonicalBicartSq (s + 1) i).le₃₄) ≫
      positiveConeHornTransportedDesc s i u v h = v :=
  (positiveConeHornTransportedIsPushout s i).inr_desc _ _ _

noncomputable def positiveCanonicalConeHornCornerMap
    (s : ℕ) (i : Fin (s + 3)) :
    ((representableJoinHornInitial 0 (s + 2) i ⊔
      SSet.stdSimplex.face
        (joinSigmaOneVertices 0 (s + 2) (∅ : Finset (Fin 1))) :
        (Δ[0 + (s + 2) + 1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶
      simplicialJoin (Δ[0] : SSet.{u}) Δ[s + 2] :=
  (representableJoinHornInitial 0 (s + 2) i ⊔
      SSet.stdSimplex.face
        (joinSigmaOneVertices 0 (s + 2) (∅ : Finset (Fin 1)))).ι ≫
    (simplicialJoinStdSimplexIsoNat 0 (s + 2)).inv

lemma positiveCanonicalConeHorn_le₂₄_ι (s : ℕ) (i : Fin (s + 3)) :
    SSet.Subcomplex.homOfLE
          (leftConeHornCanonicalBicartSq (s + 1) i).le₂₄ ≫
        (representableJoinHornInitial 0 (s + 2) i ⊔
          SSet.stdSimplex.face
            (joinSigmaOneVertices 0 (s + 2) (∅ : Finset (Fin 1)))).ι =
      (representableJoinHornInitial 0 (s + 2) i).ι :=
  SSet.Subcomplex.homOfLE_ι _

lemma positiveCanonicalConeHorn_le₃₂_ι (s : ℕ) (i : Fin (s + 3)) :
    SSet.Subcomplex.homOfLE
          (leftConeHornCanonicalBicartSq (s + 1) i).le₃₄ ≫
        (representableJoinHornInitial 0 (s + 2) i ⊔
          SSet.stdSimplex.face
            (joinSigmaOneVertices 0 (s + 2) (∅ : Finset (Fin 1)))).ι =
      (SSet.stdSimplex.face
        (joinSigmaOneVertices 0 (s + 2) (∅ : Finset (Fin 1)))).ι :=
  SSet.Subcomplex.homOfLE_ι _

noncomputable def positiveCanonicalConeHornApex
    (s : ℕ) (i : Fin (s + 3)) : SSet.{u} :=
  (representableJoinHornInitial 0 (s + 2) i ⊔
    SSet.stdSimplex.face
      (joinSigmaOneVertices 0 (s + 2) (∅ : Finset (Fin 1))) :
    (Δ[0 + (s + 2) + 1] : SSet.{u}).Subcomplex)

noncomputable def positiveCanonicalConeHornApex.ι
    (s : ℕ) (i : Fin (s + 3)) :
    positiveCanonicalConeHornApex.{u} s i ⟶ Δ[0 + (s + 2) + 1] :=
  (representableJoinHornInitial 0 (s + 2) i ⊔
    SSet.stdSimplex.face
      (joinSigmaOneVertices 0 (s + 2) (∅ : Finset (Fin 1)))).ι

lemma positiveCanonicalConeHorn_le₂₄_apex_ι
    (s : ℕ) (i : Fin (s + 3)) :
    SSet.Subcomplex.homOfLE
        (leftConeHornCanonicalBicartSq (s + 1) i).le₂₄ ≫
      positiveCanonicalConeHornApex.ι s i =
        (representableJoinHornInitial 0 (s + 2) i).ι := by
  unfold positiveCanonicalConeHornApex.ι
  exact SSet.Subcomplex.homOfLE_ι _

noncomputable def positiveCanonicalConeHornLeftComposite
    (s : ℕ) (i : Fin (s + 3)) :
    simplicialJoin (Δ[0] : SSet.{u}) Λ[s + 2, i] ⟶
      positiveCanonicalConeHornApex s i :=
  (positiveJoinHornIsoRange s i).hom ≫
    SSet.Subcomplex.homOfLE
      (leftConeHornCanonicalBicartSq (s + 1) i).le₂₄

set_option maxHeartbeats 800000 in
lemma positiveJoinHornIsoRange_hom_initial_ι
    (s : ℕ) (i : Fin (s + 3)) :
    (positiveJoinHornIsoRange.{u} s i).hom ≫
        (representableJoinHornInitial 0 (s + 2) i).ι =
      representableJoinHornMap 0 (s + 2) i := by
  change (representableJoinHornPointIso 0 s i).hom ≫
    (representableJoinHornInitial 0 (s + 2) i).ι = _
  rw [representableJoinHornPointIso_hom]
  unfold representableJoinHornInitial
  exact SSet.Subcomplex.toRange_ι _

lemma positiveCanonicalConeHorn_pointIso_to_ambient
    (s : ℕ) (i : Fin (s + 3)) :
    positiveCanonicalConeHornLeftComposite.{u} s i ≫
        positiveCanonicalConeHornApex.ι s i =
      representableJoinHornMap 0 (s + 2) i := by
  unfold positiveCanonicalConeHornLeftComposite
  have hle := positiveCanonicalConeHorn_le₂₄_apex_ι s i
  have hp := positiveJoinHornIsoRange_hom_initial_ι s i
  exact (congrArg (fun k ↦ (positiveJoinHornIsoRange s i).hom ≫ k) hle).trans hp

lemma representableJoinHornMap_comp_stdIso_inv
    (s : ℕ) (i : Fin (s + 3)) :
    representableJoinHornMap.{u} 0 (s + 2) i ≫
        (simplicialJoinStdSimplexIsoNat 0 (s + 2)).inv =
      simplicialJoinMap (𝟙 (Δ[0] : SSet.{u})) (SSet.horn (s + 2) i).ι := by
  rw [representableJoinHornMap, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

lemma positiveCanonicalConeHornCornerMap_left
    (s : ℕ) (i : Fin (s + 3)) :
    positiveCanonicalConeHornLeftComposite.{u} s i ≫
        positiveCanonicalConeHornCornerMap s i =
      simplicialJoinMap (𝟙 (Δ[0] : SSet.{u})) (SSet.horn (s + 2) i).ι := by
  have ha := positiveCanonicalConeHorn_pointIso_to_ambient s i
  have hb := representableJoinHornMap_comp_stdIso_inv s i
  calc
    _ = (positiveCanonicalConeHornLeftComposite s i ≫
          positiveCanonicalConeHornApex.ι s i) ≫
        (simplicialJoinStdSimplexIsoNat 0 (s + 2)).inv := by
      rfl
    _ = representableJoinHornMap 0 (s + 2) i ≫
        (simplicialJoinStdSimplexIsoNat 0 (s + 2)).inv :=
      congrArg (fun k ↦ k ≫
        (simplicialJoinStdSimplexIsoNat 0 (s + 2)).inv) ha
    _ = _ := hb

lemma positiveCanonicalConeHorn_le₁₃_face_ι
    (s : ℕ) (i : Fin (s + 3)) :
    SSet.Subcomplex.homOfLE
        (leftConeHornCanonicalBicartSq (s + 1) i).le₁₃ ≫
      (SSet.stdSimplex.face
        (joinSigmaOneVertices 0 (s + 2) (∅ : Finset (Fin 1)))).ι =
      (joinSigmaOneHornRange 0 (s + 2)
        (∅ : Finset (Fin 1)) i).ι :=
  SSet.Subcomplex.homOfLE_ι _

noncomputable def normalizedEmptyJoinAmbientIso (r : ℕ) :
    (Δ[r + 1] : SSet.{u}) ≅ Δ[0 + (r + 1)] :=
  SSet.stdSimplex.mapIso
    (eqToIso (congrArg SimplexCategory.mk (Nat.zero_add (r + 1)).symm))

lemma hornSigmaEqIso_hom_ι
    {p q : Σ n : ℕ, Fin (n + 1)} (h : p = q) :
    (eqToIso (congrArg (fun z : Σ n : ℕ, Fin (n + 1) ↦
      (SSet.horn z.1 z.2 : SSet.{u})) h)).hom ≫
        (SSet.horn q.1 q.2).ι =
      (SSet.horn p.1 p.2).ι ≫
        (SSet.stdSimplex.mapIso
          (eqToIso (congrArg SimplexCategory.mk
            (congrArg Sigma.fst h)))).hom := by
  subst q
  simp

lemma normalizedEmptyJoinHornIso_hom_ι
    (r : ℕ) (i : Fin (r + 2)) :
    (normalizedEmptyJoinHornIso.{u} r i).hom ≫
        (SSet.horn (0 + (r + 1))
          (Fin.cast
            (congrArg (fun n => n + 1) (Nat.zero_add (r + 1)).symm) i)).ι =
      (SSet.horn (r + 1) i).ι ≫ (normalizedEmptyJoinAmbientIso r).hom := by
  let hN : 0 + (r + 1) = r + 1 := Nat.zero_add _
  let p : Σ n : ℕ, Fin (n + 1) := ⟨r + 1, i⟩
  let q : Σ n : ℕ, Fin (n + 1) :=
    ⟨0 + (r + 1), Fin.cast (congrArg (fun n => n + 1) hN.symm) i⟩
  have hpq : p = q := by
    apply Sigma.ext hN.symm
    apply (Fin.heq_ext_iff (congrArg (fun n => n + 1) hN.symm)).2
    simp [p, q]
  have h := hornSigmaEqIso_hom_ι hpq
  simpa only [normalizedEmptyJoinHornIso, normalizedEmptyJoinAmbientIso,
    p, q] using h

lemma normalizedEmptyJoinAmbientIso_hom_comp_faceIso_ι (r : ℕ) :
    (normalizedEmptyJoinAmbientIso.{u} r).hom ≫
        (joinSigmaOneFaceIso 0 (r + 1) (∅ : Finset (Fin 1))).hom ≫
        (SSet.stdSimplex.face
          (joinSigmaOneVertices 0 (r + 1) (∅ : Finset (Fin 1)))).ι =
      SSet.stdSimplex.map (standardJoinRightOperator 0 (r + 1)) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_map]
  apply ULift.ext
  apply SimplexCategory.Hom.ext
  ext j
  simp [normalizedEmptyJoinAmbientIso, joinSigmaOneFaceIso,
    SSet.stdSimplex.isoOfRepresentableBy,
    SSet.stdSimplex.faceRepresentableBy, joinSigmaOneVertices,
    joinFirstVertices, joinSecondVertices, standardJoinRightOperator,
    SSet.yonedaEquiv_map, SimplexCategory.eqToHom_toOrderHom]
  let e : Fin (r + 2) ↪o Fin (0 + (r + 1) + 2) :=
    { toFun := fun (k : Fin (r + 2)) => ⟨1 + k.val, by omega⟩
      inj' := by
        intro a b h
        apply Fin.ext
        simpa using congrArg Fin.val h
      map_rel_iff' := by
        intro a b
        change (1 + a.val ≤ 1 + b.val) ↔ a.val ≤ b.val
        omega }
  have he : e =
      (joinSigmaOneVertices 0 (r + 1) (∅ : Finset (Fin 1))).orderEmbOfFin (by
        rw [card_joinSigmaOneVertices]
        simp) := by
    apply Finset.orderEmbOfFin_unique'
    intro a
    simp [joinSigmaOneVertices, joinFirstVertices, joinSecondVertices, e]
  exact congrArg Fin.val (congrArg (fun f ↦ f j) he.symm)

lemma joinSigmaOneHornIsoRange_hom_ι_empty
    (r : ℕ) (i : Fin (r + 2)) :
    (joinSigmaOneHornIsoRange.{u} 0 (r + 1)
        (∅ : Finset (Fin 1)) i).hom ≫
      (joinSigmaOneHornRange 0 (r + 1)
        (∅ : Finset (Fin 1)) i).ι =
      joinSigmaOneHornMap 0 (r + 1) (∅ : Finset (Fin 1)) i := by
  change SSet.Subcomplex.toRange
      (joinSigmaOneHornMap 0 (r + 1) (∅ : Finset (Fin 1)) i) ≫
    (SSet.Subcomplex.range
      (joinSigmaOneHornMap 0 (r + 1) (∅ : Finset (Fin 1)) i)).ι = _
  exact SSet.Subcomplex.toRange_ι _

set_option maxHeartbeats 800000 in
lemma emptyJoinHornIsoRange_hom_ι
    (s : ℕ) (i : Fin (s + 3)) :
    (emptyJoinHornIsoRange.{u} (s + 1) i).hom ≫
        (joinSigmaOneHornRange 0 (s + 2)
          (∅ : Finset (Fin 1)) i).ι =
      (SSet.horn (s + 2) i).ι ≫
        SSet.stdSimplex.map (standardJoinRightOperator 0 (s + 2)) := by
  unfold emptyJoinHornIsoRange
  change (normalizedEmptyJoinHornIso (s + 1) i).hom ≫ _ ≫
    (joinSigmaOneHornIsoRange 0 ((s + 1) + 1)
      (∅ : Finset (Fin 1)) i).hom ≫
    (joinSigmaOneHornRange 0 ((s + 1) + 1)
      (∅ : Finset (Fin 1)) i).ι = _
  have hj := joinSigmaOneHornIsoRange_hom_ι_empty (s + 1) i
  let iRaw := Fin.cast
    (congrArg (fun n => n + 1) (Nat.zero_add ((s + 1) + 1)).symm) i
  let iJoin := joinSigmaOneDistinguishedIndex ((s + 1) + 1)
    (∅ : Finset (Fin 1)) i
  have hidx : iRaw = iJoin := by
    apply Fin.ext
    simp [iRaw, iJoin, joinSigmaOneDistinguishedIndex]
  have hi := eqToIso_horn_index_hom_ι (0 + ((s + 1) + 1)) hidx
  have hn := normalizedEmptyJoinHornIso_hom_ι (s + 1) i
  have hpref : (normalizedEmptyJoinHornIso (s + 1) i).hom ≫
      (eqToIso (congrArg (fun j =>
          (SSet.horn (0 + ((s + 1) + 1)) j : SSet.{u})) hidx)).hom ≫
      (SSet.horn (0 + ((s + 1) + 1)) iJoin).ι =
      (SSet.horn ((s + 1) + 1) i).ι ≫
        (normalizedEmptyJoinAmbientIso (s + 1)).hom := by
    exact (congrArg (fun k ↦
      (normalizedEmptyJoinHornIso (s + 1) i).hom ≫ k) hi).trans hn
  have hpref' : ((normalizedEmptyJoinHornIso (s + 1) i).hom ≫
      (eqToIso (congrArg (fun j =>
        (SSet.horn (0 + ((s + 1) + 1)) j : SSet.{u})) hidx)).hom) ≫
      (SSet.horn (0 + ((s + 1) + 1)) iJoin).ι =
      (SSet.horn ((s + 1) + 1) i).ι ≫
        (normalizedEmptyJoinAmbientIso (s + 1)).hom := by
    rw [Category.assoc]
    exact hpref
  dsimp [iJoin] at hpref'
  calc
    _ = (normalizedEmptyJoinHornIso (s + 1) i).hom ≫ _ ≫
        joinSigmaOneHornMap 0 ((s + 1) + 1)
          (∅ : Finset (Fin 1)) i :=
      congrArg (fun k ↦ (normalizedEmptyJoinHornIso (s + 1) i).hom ≫ _ ≫ k) hj
    _ = _ := by
      unfold joinSigmaOneHornMap
      simp only [Finset.card_empty]
      exact (congrArg (fun k ↦ k ≫
        (joinSigmaOneFaceIso 0 ((s + 1) + 1) (∅ : Finset (Fin 1))).hom ≫
        (SSet.stdSimplex.face
          (joinSigmaOneVertices 0 ((s + 1) + 1) (∅ : Finset (Fin 1)))).ι)
        hpref').trans (by
          convert congrArg
              (fun k ↦ (SSet.horn ((s + 1) + 1) i).ι ≫ k)
              (normalizedEmptyJoinAmbientIso_hom_comp_faceIso_ι (s + 1)) using 1 <;>
            rfl)

lemma positiveConeHornTransportedRightLeg_eq
    (s : ℕ) (i : Fin (s + 3)) :
    positiveConeHornTransportedRightLeg.{u} s i =
      (SSet.horn (s + 2) i).ι := by
  apply (cancel_mono (emptyJoinFaceIso (s + 1)).hom).mp
  unfold positiveConeHornTransportedRightLeg
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply (cancel_mono (SSet.stdSimplex.face
    (joinSigmaOneVertices 0 (s + 2) (∅ : Finset (Fin 1)))).ι).mp
  have hl := positiveCanonicalConeHorn_le₁₃_face_ι s i
  have hc := emptyJoinHornIsoRange_hom_ι s i
  have hr := emptyJoinFaceIso_hom_ι (s + 1)
  exact (congrArg (fun k ↦ (emptyJoinHornIsoRange (s + 1) i).hom ≫ k) hl).trans
    (hc.trans (congrArg (fun k ↦ (SSet.horn (s + 2) i).ι ≫ k) hr.symm))

lemma positiveCanonicalConeHornCornerMap_right
    (s : ℕ) (i : Fin (s + 3)) :
    (emptyJoinFaceIso (s + 1)).hom ≫
        SSet.Subcomplex.homOfLE
          (leftConeHornCanonicalBicartSq (s + 1) i).le₃₄ ≫
        positiveCanonicalConeHornCornerMap.{u} s i =
      simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Δ[s + 2] := by
  calc
    _ = (emptyJoinFaceIso (s + 1)).hom ≫
          (SSet.stdSimplex.face
            (joinSigmaOneVertices 0 (s + 2) (∅ : Finset (Fin 1)))).ι ≫
          (simplicialJoinStdSimplexIsoNat 0 (s + 2)).inv := by
        rw [positiveCanonicalConeHornCornerMap]
        slice_lhs 2 3 => rw [positiveCanonicalConeHorn_le₃₂_ι]
    _ = SSet.stdSimplex.map (standardJoinRightOperator 0 (s + 2)) ≫
          (simplicialJoinStdSimplexIsoNat 0 (s + 2)).inv := by
        rw [← Category.assoc, emptyJoinFaceIso_hom_ι]
    _ = (simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Δ[s + 2] ≫
          (simplicialJoinStdSimplexIsoNat 0 (s + 2)).hom) ≫
          (simplicialJoinStdSimplexIsoNat 0 (s + 2)).inv := by
        rw [rightCone_rightInclusion_stdSimplex]
    _ = _ := by rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

lemma positiveConeHornTransportedLeftLeg_eq
    (s : ℕ) (i : Fin (s + 3)) :
    positiveConeHornTransportedLeftLeg.{u} s i =
      simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Λ[s + 2, i] := by
  let g := SSet.Subcomplex.homOfLE
    (leftConeHornCanonicalBicartSq.{u} (s + 1) i).le₂₄
  let a := (positiveJoinHornIsoRange.{u} s i).hom ≫ g
  let b := (emptyJoinFaceIso (s + 1)).hom ≫
    SSet.Subcomplex.homOfLE
      (leftConeHornCanonicalBicartSq (s + 1) i).le₃₄
  letI : Mono (positiveCanonicalConeHornCornerMap.{u} s i) := by
    unfold positiveCanonicalConeHornCornerMap
    infer_instance
  letI : Mono a := by
    letI : Mono g := SSet.Subcomplex.mono_homOfLE _
    dsimp [a]
    exact mono_comp _ _
  have hab : simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Λ[s + 2, i] ≫ a =
      (SSet.horn (s + 2) i).ι ≫ b := by
    apply (cancel_mono (positiveCanonicalConeHornCornerMap s i)).mp
    have hl := positiveCanonicalConeHornCornerMap_left s i
    have hr := positiveCanonicalConeHornCornerMap_right s i
    calc
      _ = simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Λ[s + 2, i] ≫
          (a ≫ positiveCanonicalConeHornCornerMap s i) := Category.assoc _ _ _
      _ = simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Λ[s + 2, i] ≫
          simplicialJoinMap (𝟙 (Δ[0] : SSet.{u}))
            (SSet.horn (s + 2) i).ι := congrArg _ hl
      _ = (SSet.horn (s + 2) i).ι ≫
          simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Δ[s + 2] :=
        (rightCone_rightInclusion_naturality
          (Δ[0] : SSet.{u}) (SSet.horn (s + 2) i).ι).symm
      _ = (SSet.horn (s + 2) i).ι ≫
          (b ≫ positiveCanonicalConeHornCornerMap s i) := congrArg _ hr.symm
      _ = ((SSet.horn (s + 2) i).ι ≫ b) ≫
          positiveCanonicalConeHornCornerMap s i := (Category.assoc _ _ _).symm
  apply (cancel_mono a).mp
  have hw := positiveConeHornTransported_w s i
  change positiveConeHornTransportedLeftLeg s i ≫ a =
    positiveConeHornTransportedRightLeg s i ≫ b at hw
  rw [positiveConeHornTransportedRightLeg_eq] at hw
  exact hw.trans hab.symm

noncomputable def positiveConeHornStandardIsPushout
    (s : ℕ) (i : Fin (s + 3)) :
    IsPushout
      (simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Λ[s + 2, i])
      (SSet.horn (s + 2) i).ι
      ((positiveJoinHornIsoRange s i).hom ≫
        SSet.Subcomplex.homOfLE
          (leftConeHornCanonicalBicartSq (s + 1) i).le₂₄)
      ((emptyJoinFaceIso (s + 1)).hom ≫
        SSet.Subcomplex.homOfLE
          (leftConeHornCanonicalBicartSq (s + 1) i).le₃₄) := by
  simpa only [positiveConeHornTransportedLeftLeg_eq,
    positiveConeHornTransportedRightLeg_eq] using
      positiveConeHornTransportedIsPushout.{u} s i

noncomputable def positiveConeHornStandardPushoutIso
    (s : ℕ) (i : Fin (s + 3)) :
    positiveCanonicalConeHornApex.{u} s i ≅
      pushout (simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Λ[s + 2, i])
        (SSet.horn (s + 2) i).ι :=
  (positiveConeHornStandardIsPushout.{u} s i).isoPushout

noncomputable def positiveConeHornStandardCornerMap
    (s : ℕ) (i : Fin (s + 3)) :
    pushout (simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Λ[s + 2, i])
        (SSet.horn (s + 2) i).ι ⟶
      simplicialJoin (Δ[0] : SSet.{u}) Δ[s + 2] :=
  (positiveConeHornStandardPushoutIso s i).inv ≫
    positiveCanonicalConeHornCornerMap s i

@[reassoc]
lemma positiveConeHornStandardCornerMap_inl
    (s : ℕ) (i : Fin (s + 3)) :
    pushout.inl (simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Λ[s + 2, i])
        (SSet.horn (s + 2) i).ι ≫
      positiveConeHornStandardCornerMap.{u} s i =
    simplicialJoinMap (𝟙 (Δ[0] : SSet.{u})) (SSet.horn (s + 2) i).ι := by
  unfold positiveConeHornStandardCornerMap
  have h := (positiveConeHornStandardIsPushout.{u} s i).inl_isoPushout_inv
  calc
    _ = (pushout.inl _ _ ≫ (positiveConeHornStandardPushoutIso.{u} s i).inv) ≫
        positiveCanonicalConeHornCornerMap.{u} s i := (Category.assoc _ _ _).symm
    _ = positiveCanonicalConeHornLeftComposite.{u} s i ≫
        positiveCanonicalConeHornCornerMap.{u} s i :=
      congrArg (fun k ↦ k ≫ positiveCanonicalConeHornCornerMap.{u} s i) h
    _ = _ := positiveCanonicalConeHornCornerMap_left s i

@[reassoc]
lemma positiveConeHornStandardCornerMap_inr
    (s : ℕ) (i : Fin (s + 3)) :
    pushout.inr (simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Λ[s + 2, i])
        (SSet.horn (s + 2) i).ι ≫
      positiveConeHornStandardCornerMap.{u} s i =
    simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Δ[s + 2] := by
  unfold positiveConeHornStandardCornerMap
  have h := (positiveConeHornStandardIsPushout.{u} s i).inr_isoPushout_inv
  calc
    _ = (pushout.inr _ _ ≫ (positiveConeHornStandardPushoutIso.{u} s i).inv) ≫
        positiveCanonicalConeHornCornerMap.{u} s i := (Category.assoc _ _ _).symm
    _ = ((emptyJoinFaceIso (s + 1)).hom ≫
          SSet.Subcomplex.homOfLE
            (leftConeHornCanonicalBicartSq (s + 1) i).le₃₄) ≫
        positiveCanonicalConeHornCornerMap.{u} s i :=
      congrArg (fun k ↦ k ≫ positiveCanonicalConeHornCornerMap.{u} s i) h
    _ = _ := positiveCanonicalConeHornCornerMap_right s i

lemma positiveCanonicalConeHornCornerMap_innerAnodyne
    (s : ℕ) (i : Fin (s + 3)) (hi : i < Fin.last (s + 2)) :
    SSet.innerAnodyneExtensions
      (positiveCanonicalConeHornCornerMap.{u} s i) := by
  let D := representableJoinHornInitial 0 (s + 2) i ⊔
    SSet.stdSimplex.face
      (joinSigmaOneVertices 0 (s + 2) (∅ : Finset (Fin 1)))
  have hface : SSet.stdSimplex.face
      (joinSigmaOneVertices 0 (s + 2) (∅ : Finset (Fin 1))) =
      SSet.stdSimplex.face ({(0 : Fin (0 + (s + 2) + 2))}ᶜ) := by
    congr 1
    ext j
    simp [joinSigmaOneVertices, joinFirstVertices, joinSecondVertices]
    constructor
    · rintro ⟨a, rfl⟩
      intro h
      have hv := congrArg Fin.val h
      simp at hv
    · intro hj
      have hjv : j.val ≠ 0 := by
        intro h
        apply hj
        apply Fin.ext
        simpa using h
      use ⟨j.val - 1, by have := j.isLt; omega⟩
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
  have hD : D = SSet.horn (0 + (s + 2) + 1)
      (⟨i.val + 1, by omega⟩ : Fin (0 + (s + 2) + 2)) := by
    dsimp [D]
    rw [hface]
    exact representableJoinHornInitial_sup_baseFace_eq_shiftedHorn (s + 1) i
  have hι : SSet.innerAnodyneExtensions D.ι := by
    rw [hD]
    exact SSet.innerAnodyneExtensions.horn_ι (by
      simpa only [Fin.lt_iff_val_lt_val, Fin.val_zero, Fin.val_mk] using
        Nat.zero_lt_succ i.val) (by
      apply Fin.mk_lt_mk.mpr
      have hi' := Fin.mk_lt_mk.mp hi
      omega)
  have he := SSet.innerAnodyneExtensions.of_isIso
    (simplicialJoinStdSimplexIsoNat 0 (s + 2)).inv
  exact SSet.innerAnodyneExtensions.comp_mem _ _ hι he

lemma positiveConeHornStandardCornerMap_innerAnodyne
    (s : ℕ) (i : Fin (s + 3)) (hi : i < Fin.last (s + 2)) :
    SSet.innerAnodyneExtensions
      (positiveConeHornStandardCornerMap.{u} s i) := by
  exact SSet.innerAnodyneExtensions.comp_mem _ _
    (SSet.innerAnodyneExtensions.of_isIso
      (positiveConeHornStandardPushoutIso s i).inv)
    (positiveCanonicalConeHornCornerMap_innerAnodyne s i hi)

end LeanLCAExactChallenge.Infinity
