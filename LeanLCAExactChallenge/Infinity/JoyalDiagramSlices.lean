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

end LeanLCAExactChallenge.Infinity
