import LeanLCAExactChallenge.Infinity.JoyalSlices

/-! # Diagram slices and restriction left fibrations -/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped CategoryTheory.MonoidalCategory.DayConvolution MonoidalCategory

/-- The simplicial set of cones under a fixed diagram. -/
abbrev diagramUnderSlice (Q K : SSet.{u}) (a : K ⟶ Q) : SSet.{u} :=
  relativeDaySliceOverMap (emptyAugmentation.{u}.obj K)
    (emptyAugmentation.{u}.obj Q) (emptyAugmentation.{u}.map a)

/-- The augmented Day-slice evaluation is restriction along the augmented initial map. -/
@[simp]
theorem dayInternalHomAugmentedObject_hom_app
    (Q K : SSet.{u}) (U : SimplexCategory) :
    (dayInternalHomAugmentedObject
      (emptyAugmentation.{u}.obj K) (emptyAugmentation.{u}.obj Q)).hom.app
        (Opposite.op U) =
      (augmentedDayInternalHom
        (emptyAugmentation.{u}.obj K) (emptyAugmentation.{u}.obj Q)).map
        (Opposite.op (WithInitial.starInitial.to (WithInitial.of U))) := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Contravariance of the chosen augmented Day internal hom in its first input. -/
noncomputable def augmentedDayInternalHomPre
    {F F' G : AugmentedSSet.{u}} (u : F' ⟶ F) :
    augmentedDayInternalHom F G ⟶ augmentedDayInternalHom F' G where
  app c := Wedge.IsLimit.lift
    ((augmentedDayInternalHomStructure F' G).isLimitWedge c)
    (fun j ↦ by
      change _ ⟶ (ihom (F'.obj j)).obj (G.obj (j ⊗ c))
      exact (augmentedDayInternalHomStructure F G).π c j ≫
        (MonoidalClosed.pre (u.app j)).app (G.obj (j ⊗ c)))
    (fun ⦃i j⦄ f ↦ by
      change ((augmentedDayInternalHomStructure F G).π c i ≫
          (MonoidalClosed.pre (u.app i)).app (G.obj (i ⊗ c))) ≫
            (ihom (F'.obj i)).map (G.map (f ▷ c)) =
        ((augmentedDayInternalHomStructure F G).π c j ≫
          (MonoidalClosed.pre (u.app j)).app (G.obj (j ⊗ c))) ≫
            (MonoidalClosed.pre (F'.map f)).app (G.obj (j ⊗ c))
      rw [Category.assoc, MonoidalClosed.pre_comm_ihom_map]
      rw [← Category.assoc, (augmentedDayInternalHomStructure F G).hπ]
      simp only [Category.assoc, ← NatTrans.comp_app]
      rw [← MonoidalClosed.pre_map, ← MonoidalClosed.pre_map,
        u.naturality])
  naturality {c c'} f := by
    apply Wedge.IsLimit.hom_ext
      ((augmentedDayInternalHomStructure F' G).isLimitWedge c')
    intro j
    dsimp
    simp only [Category.assoc,
      CategoryTheory.MonoidalCategory.DayConvolutionInternalHom.map_comp_π]
    rw [← Wedge.mk_ι
        (F := CategoryTheory.MonoidalCategory.dayConvolutionInternalHomDiagramFunctor
          F' |>.obj G |>.obj c')
        (augmentedDayInternalHom F' G |>.obj c')
        ((augmentedDayInternalHomStructure F' G).π c')
        ((augmentedDayInternalHomStructure F' G).hπ c'),
      ← Wedge.mk_ι
        (F := CategoryTheory.MonoidalCategory.dayConvolutionInternalHomDiagramFunctor
          F' |>.obj G |>.obj c)
        (augmentedDayInternalHom F' G |>.obj c)
        ((augmentedDayInternalHomStructure F' G).π c)
        ((augmentedDayInternalHomStructure F' G).hπ c),
      Wedge.IsLimit.lift_ι
        ((augmentedDayInternalHomStructure F' G).isLimitWedge c'),
      Wedge.IsLimit.lift_ι_assoc
        ((augmentedDayInternalHomStructure F' G).isLimitWedge c)]
    rw [← Category.assoc,
      CategoryTheory.MonoidalCategory.DayConvolutionInternalHom.map_comp_π]
    let j' : AugmentedSimplexCategoryᵒᵖ := j
    have hc := MonoidalClosed.pre_comm_ihom_map
      (u.app j') (G.map (j' ◁ f))
    simpa only [j', Category.assoc] using
      congrArg (fun k ↦
        (augmentedDayInternalHomStructure F G).π c j' ≫ k) hc.symm

theorem augmentedDayInternalHomPre_starOfMap
    {F F' G : AugmentedSSet.{u}} (u : F' ⟶ F) (a : F ⟶ G) :
    (augmentedDayInternalHomPre u).app (Opposite.op WithInitial.star)
        (dayInternalHomStarOfMap a) =
      dayInternalHomStarOfMap (u ≫ a) := by
  apply Subtype.ext
  funext j
  change (MonoidalClosed.pre (u.app j)).app _
      (MonoidalClosed.curry ((ρ_ (F.obj j)).hom ≫ a.app j ≫
        G.map (ρ_ j).inv) PUnit.unit) =
    MonoidalClosed.curry ((ρ_ (F'.obj j)).hom ≫
      (u ≫ a).app j ≫ G.map (ρ_ j).inv) PUnit.unit
  rw [← ConcreteCategory.comp_apply, MonoidalClosed.curry_pre_app]
  apply ConcreteCategory.congr_hom
  simp only [NatTrans.comp_app, Category.assoc]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of cones along a map of diagram shapes. -/
noncomputable def diagramUnderRestriction
    {Q K K' : SSet.{u}} (j : K' ⟶ K) (a : K ⟶ Q) :
    diagramUnderSlice Q K a ⟶ diagramUnderSlice Q K' (j ≫ a) := by
  let F := emptyAugmentation.{u}.obj K
  let F' := emptyAugmentation.{u}.obj K'
  let G := emptyAugmentation.{u}.obj Q
  let uMap := emptyAugmentation.{u}.map j
  let H := diagramUnderSlice Q K a
  let ψ : H ⟶ forgetAugmentation.{u}.obj (augmentedDayInternalHom F' G) :=
    relativeDaySlice.ι F G (dayInternalHomStarOfMap
      (emptyAugmentation.map a)) ≫
      forgetAugmentation.map (augmentedDayInternalHomPre (G := G) uMap)
  change H ⟶ relativeDaySliceOverMap F' G
    (emptyAugmentation.map (j ≫ a))
  refine (relativeDaySliceOverMapHomEquiv F' G
    (emptyAugmentation.map (j ≫ a)) H).symm ⟨ψ, ?_⟩
  let E := AugmentedSimplexCategory.equivAugmentedSimplicialObject (C := Type u)
  have hw : (E.functor.map
        (augmentedDayInternalHomPre (G := G) uMap)).left ≫
        (E.functor.obj (augmentedDayInternalHom F' G)).hom =
      (E.functor.obj (augmentedDayInternalHom F G)).hom ≫
        (SimplicialObject.const (Type u)).map
          (E.functor.map
            (augmentedDayInternalHomPre (G := G) uMap)).right := by
    exact (E.functor.map
      (augmentedDayInternalHomPre (G := G) uMap)).w
  change (relativeDaySlice.ι F G (dayInternalHomStarOfMap
      (emptyAugmentation.map a)) ≫
      (E.functor.map
        (augmentedDayInternalHomPre (G := G) uMap)).left) ≫
        (E.functor.obj (augmentedDayInternalHom F' G)).hom = _
  rw [Category.assoc, hw]
  rw [← Category.assoc]
  change ((Limits.pullback.fst
      (dayInternalHomAugmentedObject F G).hom
      (dayInternalHomConstantPoint F G
        (dayInternalHomStarOfMap (emptyAugmentation.map a)))) ≫
        (dayInternalHomAugmentedObject F G).hom) ≫ _ = _
  rw [Limits.pullback.condition]
  have hsnd : Limits.pullback.snd
      (dayInternalHomAugmentedObject F G).hom
      (dayInternalHomConstantPoint F G
        (dayInternalHomStarOfMap (emptyAugmentation.map a))) =
      toConstantTerminal H := by
    apply NatTrans.ext
    funext n
    apply Limits.terminal.hom_ext
  rw [hsnd, Category.assoc]
  congr 1
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  change (augmentedDayInternalHomPre (G := G) uMap).app
      (Opposite.op WithInitial.star)
        (dayInternalHomStarOfMap (emptyAugmentation.map a)) =
    dayInternalHomStarOfMap (emptyAugmentation.map (j ≫ a))
  rw [augmentedDayInternalHomPre_starOfMap]
  rw [Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
theorem augmentedDayInternalHomPre_app_comp_π
    {F F' G : AugmentedSSet.{u}} (uMap : F' ⟶ F)
    (c j : AugmentedSimplexCategoryᵒᵖ) :
    (augmentedDayInternalHomPre uMap).app c ≫
        (augmentedDayInternalHomStructure F' G).π c j =
      (augmentedDayInternalHomStructure F G).π c j ≫
        (MonoidalClosed.pre (uMap.app j)).app (G.obj (j ⊗ c)) := by
  unfold augmentedDayInternalHomPre
  dsimp
  rw [← Wedge.mk_ι
      (F := CategoryTheory.MonoidalCategory.dayConvolutionInternalHomDiagramFunctor
        F' |>.obj G |>.obj c)
      (augmentedDayInternalHom F' G |>.obj c)
      ((augmentedDayInternalHomStructure F' G).π c)
      ((augmentedDayInternalHomStructure F' G).hπ c),
    Wedge.IsLimit.lift_ι
      ((augmentedDayInternalHomStructure F' G).isLimitWedge c)]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the augmented Day transpose in its first tensor input. -/
theorem augmentedDayHomEquiv_precomp_left
    {F F' K G : AugmentedSSet.{u}} (uMap : F' ⟶ F)
    (phi : letI := augmentedDayConvolution F K
      CategoryTheory.MonoidalCategory.DayConvolution.convolution F K ⟶ G) :
    letI := augmentedDayConvolution F K
    letI := augmentedDayConvolution F' K
    augmentedDayHomEquiv F' K G
        (CategoryTheory.MonoidalCategory.DayConvolution.map
          uMap (𝟙 K) ≫ phi) =
      augmentedDayHomEquiv F K G phi ≫ augmentedDayInternalHomPre uMap := by
  letI := augmentedDayConvolution F K
  letI := augmentedDayConvolution F' K
  let lG := augmentedDayInternalHomStructure F G
  let lG' := augmentedDayInternalHomStructure F' G
  let lFK := augmentedDayInternalHomStructure F
    (CategoryTheory.MonoidalCategory.DayConvolution.convolution F K)
  let lF'K := augmentedDayInternalHomStructure F'
    (CategoryTheory.MonoidalCategory.DayConvolution.convolution F' K)
  change lF'K.coev_app ≫
      lF'K.map
        (CategoryTheory.MonoidalCategory.DayConvolution.map
          uMap (𝟙 K) ≫ phi) lG' =
    (lFK.coev_app ≫ lFK.map phi lG) ≫ augmentedDayInternalHomPre uMap
  apply NatTrans.ext
  funext c
  apply Wedge.IsLimit.hom_ext (lG'.isLimitWedge c)
  intro j
  dsimp
  let j' : AugmentedSimplexCategoryᵒᵖ := j
  change lF'K.coev_app.app c ≫
      (lF'K.map
        (CategoryTheory.MonoidalCategory.DayConvolution.map
          uMap (𝟙 K) ≫ phi) lG').app c ≫
        lG'.π c j' =
    lFK.coev_app.app c ≫ (lFK.map phi lG).app c ≫
      (augmentedDayInternalHomPre uMap).app c ≫ lG'.π c j'
  rw [lF'K.map_app_comp_π]
  rw [← Category.assoc, lF'K.coev_app_π]
  rw [← MonoidalClosed.curry_natural_right]
  rw [← Category.assoc, augmentedDayInternalHomPre_app_comp_π]
  rw [Category.assoc (lFK.coev_app.app c) ((lFK.map phi lG).app c)]
  rw [lFK.map_app_comp_π_assoc]
  rw [lFK.coev_app_π_assoc]
  rw [← MonoidalClosed.curry_natural_right_assoc]
  rw [MonoidalClosed.curry_pre_app]
  congr 1
  simp only [NatTrans.comp_app]
  rw [CategoryTheory.MonoidalCategory.DayConvolution.unit_app_map_app_assoc]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Restriction followed by the slice inclusion is first-variable internal-hom restriction. -/
theorem diagramUnderRestriction_comp_ι
    {Q K K' : SSet.{u}} (j : K' ⟶ K) (a : K ⟶ Q) :
    diagramUnderRestriction j a ≫
        relativeDaySlice.ι
          (emptyAugmentation.{u}.obj K') (emptyAugmentation.{u}.obj Q)
          (dayInternalHomStarOfMap
            (emptyAugmentation.{u}.map (j ≫ a))) =
      relativeDaySlice.ι
          (emptyAugmentation.{u}.obj K) (emptyAugmentation.{u}.obj Q)
          (dayInternalHomStarOfMap (emptyAugmentation.{u}.map a)) ≫
        forgetAugmentation.{u}.map
          (augmentedDayInternalHomPre (emptyAugmentation.{u}.map j)) := by
  unfold diagramUnderRestriction
  dsimp
  unfold relativeDaySliceOverMapHomEquiv relativeDaySliceHomEquiv
  dsimp [relativeDaySlice.ι]
  rw [Limits.pullback.lift_fst]

theorem diagramUnderRestriction_comp_pullback_fst
    {Q K K' : SSet.{u}} (j : K' ⟶ K) (a : K ⟶ Q) :
    diagramUnderRestriction j a ≫
        Limits.pullback.fst
          (dayInternalHomAugmentedObject
            (emptyAugmentation.{u}.obj K')
            (emptyAugmentation.{u}.obj Q)).hom
          (dayInternalHomConstantPoint
            (emptyAugmentation.{u}.obj K')
            (emptyAugmentation.{u}.obj Q)
            (dayInternalHomStarOfMap
              (emptyAugmentation.{u}.map (j ≫ a)))) =
      Limits.pullback.fst
          (dayInternalHomAugmentedObject
            (emptyAugmentation.{u}.obj K)
            (emptyAugmentation.{u}.obj Q)).hom
          (dayInternalHomConstantPoint
            (emptyAugmentation.{u}.obj K)
            (emptyAugmentation.{u}.obj Q)
            (dayInternalHomStarOfMap (emptyAugmentation.{u}.map a))) ≫
        forgetAugmentation.{u}.map
          (augmentedDayInternalHomPre (emptyAugmentation.{u}.map j)) :=
  diagramUnderRestriction_comp_ι j a

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 200000 in
-- This finite combinatorial normalization exceeds the default elaboration budget.
/-- The fixed-base Day transpose of a restricted cone is precomposition in the first tensor
variable. -/
theorem relativeDaySliceOverMapFixedBaseEquiv_diagramUnderRestriction
    {Q K K' L : SSet.{u}} (j : K' ⟶ K) (a : K ⟶ Q)
    (f : L ⟶ diagramUnderSlice Q K a) :
    letI := augmentedDayConvolution
      (emptyAugmentation.{u}.obj K) (emptyAugmentation.{u}.obj L)
    letI := augmentedDayConvolution
      (emptyAugmentation.{u}.obj K') (emptyAugmentation.{u}.obj L)
    ((relativeDaySliceOverMapFixedBaseEquiv
      (emptyAugmentation.{u}.obj K') (emptyAugmentation.{u}.obj Q) L
      (emptyAugmentation.{u}.map (j ≫ a)))
        (f ≫ diagramUnderRestriction j a)).1 =
      CategoryTheory.MonoidalCategory.DayConvolution.map
          (emptyAugmentation.{u}.map j)
          (𝟙 (emptyAugmentation.{u}.obj L)) ≫
        ((relativeDaySliceOverMapFixedBaseEquiv
          (emptyAugmentation.{u}.obj K) (emptyAugmentation.{u}.obj Q) L
          (emptyAugmentation.{u}.map a)) f).1 := by
  let F := emptyAugmentation.{u}.obj K
  let F' := emptyAugmentation.{u}.obj K'
  let G := emptyAugmentation.{u}.obj Q
  let E := emptyAugmentation.{u}.obj L
  letI := augmentedDayConvolution F E
  letI := augmentedDayConvolution F' E
  apply (augmentedDayHomEquiv F' E G).injective
  rw [augmentedDayHomEquiv_precomp_left]
  unfold relativeDaySliceOverMapFixedBaseEquiv relativeDaySliceFixedBaseEquiv
  dsimp
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  let A := AugmentedSimplexCategory.equivAugmentedSimplicialObject (C := Type u)
  apply A.functor.map_injective
  apply CommaMorphism.ext
  · change forgetAugmentation.map
        (augmentedMapOfFixedUnderlying L _ _ _ _) =
      forgetAugmentation.map
        (augmentedMapOfFixedUnderlying L _ _ _ _ ≫
          augmentedDayInternalHomPre (emptyAugmentation.map j))
    rw [forgetAugmentation.map_comp,
      forgetAugmentation_augmentedMapOfFixedUnderlying,
      forgetAugmentation_augmentedMapOfFixedUnderlying]
    unfold relativeDaySliceHomEquiv
    dsimp
    simp only [Category.assoc]
    rw [diagramUnderRestriction_comp_pullback_fst]
  · apply ConcreteCategory.hom_ext
    intro x
    change (augmentedMapOfFixedUnderlying L _ _ _ _).app
        (Opposite.op WithInitial.star) x =
      (augmentedDayInternalHomPre (emptyAugmentation.map j)).app
        (Opposite.op WithInitial.star)
          ((augmentedMapOfFixedUnderlying L _ _ _ _).app
            (Opposite.op WithInitial.star) x)
    have hx : x = emptyAugmentationStarPoint L := by
      let fx :
          (emptyAugmentation.obj L).obj (Opposite.op WithInitial.star) ⟶
            (emptyAugmentation.obj L).obj
              (Opposite.op WithInitial.star) :=
        ConcreteCategory.ofHom (TypeCat.Fun.mk (fun _ ↦ x))
      let ft :
          (emptyAugmentation.obj L).obj (Opposite.op WithInitial.star) ⟶
            (emptyAugmentation.obj L).obj
              (Opposite.op WithInitial.star) :=
        ConcreteCategory.ofHom
          (TypeCat.Fun.mk (fun _ ↦ emptyAugmentationStarPoint L))
      exact ConcreteCategory.congr_hom
        ((emptyAugmentationStarIsTerminal L).hom_ext fx ft) x
    subst x
    rw [augmentedMapOfFixedUnderlying_star,
      augmentedMapOfFixedUnderlying_star,
      augmentedDayInternalHomPre_starOfMap,
      Functor.map_comp]

/-- The join pushout-product square controlling restriction of diagram slices. -/
noncomputable def diagramRestrictionHornCornerSq
    {K K' : SSet.{u}} (j : K' ⟶ K) (n : ℕ) (i : Fin (n + 1)) :=
  Functor.PushoutObjObj.ofHasPushout
    (Functor.curryObj ordinaryJoinBifunctor) j
    ((SSet.horn n i).ι : (Λ[n, i] : SSet.{u}) ⟶ Δ[n])

@[reassoc (attr := simp)]
lemma diagramRestrictionHornCornerSq_inl_ι
    {K K' : SSet.{u}} (j : K' ⟶ K) (n : ℕ) (i : Fin (n + 1)) :
    (diagramRestrictionHornCornerSq j n i).inl ≫
        (diagramRestrictionHornCornerSq j n i).ι =
      simplicialJoinMap (𝟙 K) (SSet.horn n i).ι :=
  (diagramRestrictionHornCornerSq j n i).inl_ι

@[reassoc (attr := simp)]
lemma diagramRestrictionHornCornerSq_inr_ι
    {K K' : SSet.{u}} (j : K' ⟶ K) (n : ℕ) (i : Fin (n + 1)) :
    (diagramRestrictionHornCornerSq j n i).inr ≫
        (diagramRestrictionHornCornerSq j n i).ι =
      simplicialJoinMap j (𝟙 Δ[n]) :=
  (diagramRestrictionHornCornerSq j n i).inr_ι

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- This finite combinatorial normalization exceeds the default elaboration budget.
/-- A lift of the associated join corner gives a lift against diagram-slice restriction. -/
theorem diagramUnderRestriction_hasLiftingProperty_of_corner
    {Q K K' : SSet.{u}} (j : K' ⟶ K) (a : K ⟶ Q)
    (n : ℕ) (i : Fin (n + 1))
    (hcorner : HasLiftingProperty (diagramRestrictionHornCornerSq j n i).ι
      (terminalIsTerminal.from Q)) :
    HasLiftingProperty (SSet.horn n i).ι
      (diagramUnderRestriction j a) := by
  refine ⟨fun {f b} sq ↦ ?_⟩
  let F := emptyAugmentation.{u}.obj K
  let F' := emptyAugmentation.{u}.obj K'
  let G := emptyAugmentation.{u}.obj Q
  let EΛ := emptyAugmentation.{u}.obj (Λ[n, i] : SSet.{u})
  let EΔ := emptyAugmentation.{u}.obj (Δ[n] : SSet.{u})
  let uMap := emptyAugmentation.{u}.map j
  let hornMap := emptyAugmentation.{u}.map (SSet.horn n i).ι
  let aMap := emptyAugmentation.{u}.map a
  let ajMap := emptyAugmentation.{u}.map (j ≫ a)
  let φ := (relativeDaySliceOverMapFixedBaseEquiv F G
    (Λ[n, i] : SSet.{u}) aMap) f
  let ψ := (relativeDaySliceOverMapFixedBaseEquiv F' G
    (Δ[n] : SSet.{u}) ajMap) b
  letI := augmentedDayConvolution F EΛ
  letI := augmentedDayConvolution F' EΛ
  letI := augmentedDayConvolution F EΔ
  letI := augmentedDayConvolution F' EΔ
  have hcompatAug :
      CategoryTheory.MonoidalCategory.DayConvolution.map uMap (𝟙 EΛ) ≫ φ.1 =
        (augmentedDayTensorLeft F').map hornMap ≫ ψ.1 := by
    have h := congrArg
      (fun k ↦ ((relativeDaySliceOverMapFixedBaseEquiv F' G
        (Λ[n, i] : SSet.{u}) ajMap) k).1) sq.w
    rw [relativeDaySliceOverMapFixedBaseEquiv_diagramUnderRestriction,
      relativeDaySliceOverMapFixedBaseEquiv_precomp_fst] at h
    exact h
  have hcompat :
      simplicialJoinMap j (𝟙 (Λ[n, i] : SSet.{u})) ≫
          forgetAugmentation.map φ.1 =
        simplicialJoinMap (𝟙 K') (SSet.horn n i).ι ≫
          forgetAugmentation.map ψ.1 := by
    unfold simplicialJoinMap
    rw [emptyAugmentation.map_id, emptyAugmentation.map_id]
    change forgetAugmentation.map
        (CategoryTheory.MonoidalCategory.DayConvolution.map uMap (𝟙 EΛ)) ≫
          forgetAugmentation.map φ.1 =
      forgetAugmentation.map ((augmentedDayTensorLeft F').map hornMap) ≫
        forgetAugmentation.map ψ.1
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (forgetAugmentation.{u}.map) hcompatAug
  let cornerTop : (diagramRestrictionHornCornerSq j n i).pt ⟶ Q :=
    (diagramRestrictionHornCornerSq j n i).isPushout.desc
      (forgetAugmentation.map φ.1) (forgetAugmentation.map ψ.1) hcompat
  let cornerSq : CommSq cornerTop (diagramRestrictionHornCornerSq j n i).ι
      (terminalIsTerminal.from Q)
      (terminalIsTerminal.from (simplicialJoin K (Δ[n] : SSet.{u}))) :=
    ⟨terminalIsTerminal.hom_ext _ _⟩
  letI : HasLiftingProperty (diagramRestrictionHornCornerSq j n i).ι
      (terminalIsTerminal.from Q) := hcorner
  let g : simplicialJoin K (Δ[n] : SSet.{u}) ⟶ Q := cornerSq.lift
  let τ := augmentedJoinMapOfUnderlying K (Δ[n] : SSet.{u}) Q g
  have hleft : simplicialJoinMap (𝟙 K) (SSet.horn n i).ι ≫ g =
      forgetAugmentation.map φ.1 := by
    calc
      _ = (diagramRestrictionHornCornerSq j n i).inl ≫
          (diagramRestrictionHornCornerSq j n i).ι ≫ g :=
        (diagramRestrictionHornCornerSq_inl_ι_assoc j n i g).symm
      _ = (diagramRestrictionHornCornerSq j n i).inl ≫ cornerTop :=
        congrArg (fun k ↦ (diagramRestrictionHornCornerSq j n i).inl ≫ k)
          cornerSq.fac_left
      _ = _ := (diagramRestrictionHornCornerSq j n i).isPushout.inl_desc
        (forgetAugmentation.map φ.1) (forgetAugmentation.map ψ.1) hcompat
  have hright : simplicialJoinMap j (𝟙 (Δ[n] : SSet.{u})) ≫ g =
      forgetAugmentation.map ψ.1 := by
    calc
      _ = (diagramRestrictionHornCornerSq j n i).inr ≫
          (diagramRestrictionHornCornerSq j n i).ι ≫ g :=
        (diagramRestrictionHornCornerSq_inr_ι_assoc j n i g).symm
      _ = (diagramRestrictionHornCornerSq j n i).inr ≫ cornerTop :=
        congrArg (fun k ↦ (diagramRestrictionHornCornerSq j n i).inr ≫ k)
          cornerSq.fac_left
      _ = _ := (diagramRestrictionHornCornerSq j n i).isPushout.inr_desc
        (forgetAugmentation.map φ.1) (forgetAugmentation.map ψ.1) hcompat
  have hτHorn : (augmentedDayTensorLeft F).map hornMap ≫ τ = φ.1 := by
    apply augmentedMapToEmptyAugmentation_ext
    rw [Functor.map_comp]
    have hforgetτ := forgetAugmentation_augmentedJoinMapOfUnderlying
      K (Δ[n] : SSet.{u}) Q g
    have hT :
        forgetAugmentation.map ((augmentedDayTensorLeft F).map hornMap) =
          simplicialJoinMap (𝟙 K) (SSet.horn n i).ι := by
      exact (simplicialJoinMap_id_eq_augmentedDayTensorLeft_map K
        (SSet.horn n i).ι).symm
    exact (congrArg (fun k ↦
      forgetAugmentation.map ((augmentedDayTensorLeft F).map hornMap) ≫ k)
        hforgetτ).trans ((congrArg (fun k ↦ k ≫ g) hT).trans hleft)
  have hτLeft :
      CategoryTheory.MonoidalCategory.DayConvolution.map uMap (𝟙 EΔ) ≫ τ =
        ψ.1 := by
    apply augmentedMapToEmptyAugmentation_ext
    rw [Functor.map_comp]
    have hforgetτ := forgetAugmentation_augmentedJoinMapOfUnderlying
      K (Δ[n] : SSet.{u}) Q g
    have hT : forgetAugmentation.map
        (CategoryTheory.MonoidalCategory.DayConvolution.map uMap (𝟙 EΔ)) =
        simplicialJoinMap j (𝟙 (Δ[n] : SSet.{u})) := by
      unfold uMap EΔ simplicialJoinMap
      rw [emptyAugmentation.map_id]
      rfl
    exact (congrArg (fun k ↦ forgetAugmentation.map
      (CategoryTheory.MonoidalCategory.DayConvolution.map uMap (𝟙 EΔ)) ≫ k)
        hforgetτ).trans ((congrArg (fun k ↦ k ≫ g) hT).trans hright)
  let Φ := fixedBaseDayConvolutionMapOfRestriction F G aMap
    (SSet.horn n i).ι φ τ hτHorn
  let l :=
    (relativeDaySliceOverMapFixedBaseEquiv F G (Δ[n] : SSet.{u}) aMap).symm Φ
  apply CommSq.HasLift.mk'
  refine { l := l, fac_left := ?_, fac_right := ?_ }
  · apply (relativeDaySliceOverMapFixedBaseEquiv F G
      (Λ[n, i] : SSet.{u}) aMap).injective
    apply Subtype.ext
    have hpre := relativeDaySliceOverMapFixedBaseEquiv_precomp_fst
      F G aMap (SSet.horn n i).ι l
    have hl : (relativeDaySliceOverMapFixedBaseEquiv F G
        (Δ[n] : SSet.{u}) aMap) l = Φ := Equiv.apply_symm_apply _ Φ
    have hm := congrArg (fun k ↦
      (augmentedDayTensorLeft F).map hornMap ≫ k.1) hl
    have hΦ : (augmentedDayTensorLeft F).map hornMap ≫ Φ.1 = φ.1 := by
      dsimp only [Φ, fixedBaseDayConvolutionMapOfRestriction]
      exact hτHorn
    exact hpre.trans (hm.trans hΦ)
  · apply (relativeDaySliceOverMapFixedBaseEquiv F' G
      (Δ[n] : SSet.{u}) ajMap).injective
    apply Subtype.ext
    have hres := relativeDaySliceOverMapFixedBaseEquiv_diagramUnderRestriction
      j a l
    have hl : (relativeDaySliceOverMapFixedBaseEquiv F G
        (Δ[n] : SSet.{u}) aMap) l = Φ := Equiv.apply_symm_apply _ Φ
    have hm := congrArg (fun k ↦
      CategoryTheory.MonoidalCategory.DayConvolution.map uMap (𝟙 EΔ) ≫ k.1) hl
    have hΦ : CategoryTheory.MonoidalCategory.DayConvolution.map uMap (𝟙 EΔ) ≫
        Φ.1 = ψ.1 := by
      dsimp only [Φ, fixedBaseDayConvolutionMapOfRestriction]
      exact hτLeft
    exact hres.trans (hm.trans hΦ)

/--
Terminal-map join-corner lifting makes diagram-slice restriction a left fibration.
-/
theorem diagramUnderRestriction_leftFibration_of_corner_lifts
    {Q K K' : SSet.{u}} (j : K' ⟶ K) (a : K ⟶ Q)
    (hcorners : ∀ (s : ℕ) (i : Fin (s + 2)),
      i < Fin.last (s + 1) →
        HasLiftingProperty (diagramRestrictionHornCornerSq j (s + 1) i).ι
          (terminalIsTerminal.from Q)) :
    LeftFibration (diagramUnderRestriction j a) := by
  refine ⟨?_⟩
  intro A B horn hhorn
  cases hhorn with
  | @intro s i hi =>
      exact diagramUnderRestriction_hasLiftingProperty_of_corner
        j a (s + 1) i (hcorners s i hi)

/-- Inner-anodyne join corners imply that restriction of diagram slices is a left fibration. -/
theorem diagramUnderRestriction_leftFibration_of_innerAnodyne_corners
    {Q K K' : SSet.{u}} [SSet.Quasicategory Q]
    (j : K' ⟶ K) (a : K ⟶ Q)
    (hcorners : ∀ (s : ℕ) (i : Fin (s + 2)),
      i < Fin.last (s + 1) →
        SSet.innerAnodyneExtensions
          (diagramRestrictionHornCornerSq j (s + 1) i).ι) :
    LeftFibration (diagramUnderRestriction j a) := by
  apply diagramUnderRestriction_leftFibration_of_corner_lifts
  intro s i hi
  let t : IsTerminal (⊤_ SSet.{u}) := terminalIsTerminal
  have hQ : SSet.InnerFibration (t.from Q) :=
    (SSet.quasicategory_iff_of_isTerminal (t.from Q) t).mp inferInstance
  exact hcorners s i hi _ hQ.mem

end LeanLCAExactChallenge.Infinity
