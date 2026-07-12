import LeanLCAExactChallenge.Infinity.JoyalSlices

/-! # Diagram slices and restriction right fibrations -/

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

end LeanLCAExactChallenge.Infinity
