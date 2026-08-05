/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.EnrichedNaturalTransformationHomotopy
import LeanLCAExactChallenge.Infinity.OrdinaryToSimplicialNerve

/-! # Naturality of locally constant coherent simplices

An ordinary natural transformation between composable chains induces a strict unit-graded
enriched natural transformation between their locally constant coherent simplices.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

namespace LeanLCAExactChallenge.Infinity.OrdinaryToSimplicialNerve

open CategoryTheory CategoryTheory.EnrichedCategory CategoryTheory.MonoidalCategory
open Opposite Simplicial
open scoped MonoidalCategory Simplicial

variable (C : Type u) [Category.{v} C] [CategoryTheory.SimplicialCategory C]

@[reassoc]
theorem eHomEquiv_comp_eHomWhiskerLeft
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    eHomEquiv SSet f ≫ eHomWhiskerLeft SSet X g =
      eHomEquiv SSet (f ≫ g) := by
  dsimp [eHomWhiskerLeft]
  rw [rightUnitor_inv_naturality_assoc]
  exact (eHomEquiv_comp SSet f g).symm

@[reassoc]
theorem eHomEquiv_comp_eHomWhiskerRight
    {W X Y : C} (f : W ⟶ X) (g : X ⟶ Y) :
    eHomEquiv SSet g ≫ eHomWhiskerRight SSet f Y =
      eHomEquiv SSet (f ≫ g) := by
  dsimp [eHomWhiskerRight]
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc]
  exact (eHomEquiv_comp SSet f g).symm

@[simp]
theorem eHomEquiv_equivFunctor_map
    {X Y : CategoryTheory.ForgetEnrichment SSet.{v} C}
    (f : X ⟶ Y) :
    eHomEquiv SSet ((CategoryTheory.ForgetEnrichment.equivFunctor SSet C).map f) =
      CategoryTheory.ForgetEnrichment.homTo SSet f := by
  simp [CategoryTheory.ForgetEnrichment.equivFunctor]

theorem coherentSimplexOfChain_map_of_le
    {n : ℕ}
    (F : CategoryTheory.ComposableArrows
      (CategoryTheory.ForgetEnrichment SSet.{v} C) n)
    (i j : CategoryTheory.SimplicialThickening (ULift (Fin (n + 1))))
    (hij : i.as ≤ j.as) :
    (coherentSimplexOfChain C F).map i j =
      CategoryTheory.CartesianMonoidalCategory.toUnit
          (CategoryTheory.nerve (i ⟶ j)) ≫
        CategoryTheory.ForgetEnrichment.homTo SSet
          (F.map (homOfLE (uliftFin_down_mono hij))) := by
  change coherentMapOfChain C F i j = _
  unfold coherentMapOfChain
  rw [dif_pos hij]

/-- An ordinary natural transformation of composable chains induces a strict enriched
natural transformation between the corresponding locally constant coherent simplices. -/
noncomputable def coherentSimplexOfChainUnitGradedNatTrans
    {n : ℕ}
    {F G : CategoryTheory.ComposableArrows
      (CategoryTheory.ForgetEnrichment SSet.{v} C) n}
    (α : F ⟶ G) :
    SSetUnitGradedNatTrans
      (coherentSimplexOfChain C F) (coherentSimplexOfChain C G) :=
  SSetUnitGradedNatTrans.ofComponentHom
    (fun i ↦ (CategoryTheory.ForgetEnrichment.equivFunctor SSet C).map
      (α.app i.as.down))
    (fun i j ↦ by
      by_cases hij : i.as ≤ j.as
      · rw [coherentSimplexOfChain_map_of_le C F i j hij,
          coherentSimplexOfChain_map_of_le C G i j hij]
        rw [← eHomEquiv_equivFunctor_map C
            (F.map (homOfLE (uliftFin_down_mono hij))),
          ← eHomEquiv_equivFunctor_map C
            (G.map (homOfLE (uliftFin_down_mono hij)))]
        change
          CategoryTheory.CartesianMonoidalCategory.toUnit
                (CategoryTheory.nerve (i ⟶ j)) ≫
              eHomEquiv SSet
                ((CategoryTheory.ForgetEnrichment.equivFunctor SSet C).map
                  (F.map (homOfLE (uliftFin_down_mono hij)))) ≫
              eHomWhiskerLeft SSet
                ((CategoryTheory.ForgetEnrichment.equivFunctor SSet C).obj
                  (F.obj i.as.down))
                ((CategoryTheory.ForgetEnrichment.equivFunctor SSet C).map
                  (α.app j.as.down)) =
            CategoryTheory.CartesianMonoidalCategory.toUnit
                (CategoryTheory.nerve (i ⟶ j)) ≫
              eHomEquiv SSet
                ((CategoryTheory.ForgetEnrichment.equivFunctor SSet C).map
                  (G.map (homOfLE (uliftFin_down_mono hij)))) ≫
              eHomWhiskerRight SSet
                ((CategoryTheory.ForgetEnrichment.equivFunctor SSet C).map
                  (α.app i.as.down))
                ((CategoryTheory.ForgetEnrichment.equivFunctor SSet C).obj
                  (G.obj j.as.down))
        rw [eHomEquiv_comp_eHomWhiskerLeft,
          eHomEquiv_comp_eHomWhiskerRight]
        have hnat := congrArg
          (CategoryTheory.ForgetEnrichment.equivFunctor SSet C).map
          (α.naturality (homOfLE (uliftFin_down_mono hij)))
        rw [Functor.map_comp, Functor.map_comp] at hnat
        exact congrArg
          (fun k ↦ CategoryTheory.CartesianMonoidalCategory.toUnit
            (CategoryTheory.nerve (i ⟶ j)) ≫ eHomEquiv SSet k)
          hnat
      · apply NatTrans.ext
        funext U
        apply ConcreteCategory.hom_ext
        intro p
        exact (hij (CategoryTheory.SimplicialThickening.Path.le (p.obj 0))).elim)

@[simp]
theorem coherentSimplexOfChainUnitGradedNatTrans_componentHom
    {n : ℕ}
    {F G : CategoryTheory.ComposableArrows
      (CategoryTheory.ForgetEnrichment SSet.{v} C) n}
    (α : F ⟶ G)
    (i : CategoryTheory.SimplicialThickening (ULift (Fin (n + 1)))) :
    (coherentSimplexOfChainUnitGradedNatTrans C α).componentHom i =
      (CategoryTheory.ForgetEnrichment.equivFunctor SSet C).map
        (α.app i.as.down) := by
  simp [coherentSimplexOfChainUnitGradedNatTrans]

@[simp]
theorem coherentSimplexOfChainUnitGradedNatTrans_id
    {n : ℕ}
    (F : CategoryTheory.ComposableArrows
      (CategoryTheory.ForgetEnrichment SSet.{v} C) n) :
    coherentSimplexOfChainUnitGradedNatTrans C (𝟙 F) =
      SSetUnitGradedNatTrans.id (coherentSimplexOfChain C F) := by
  apply GradedNatTrans.ext
  funext i
  apply (eHomEquiv SSet).symm.injective
  change
    (coherentSimplexOfChainUnitGradedNatTrans C (𝟙 F)).componentHom i =
      (SSetUnitGradedNatTrans.id (coherentSimplexOfChain C F)).componentHom i
  rw [coherentSimplexOfChainUnitGradedNatTrans_componentHom,
    SSetUnitGradedNatTrans.componentHom_id]
  change (CategoryTheory.ForgetEnrichment.equivFunctor SSet C).map
      (𝟙 (F.obj i.as.down)) =
    𝟙 ((CategoryTheory.ForgetEnrichment.equivFunctor SSet C).obj
      (F.obj i.as.down))
  exact (CategoryTheory.ForgetEnrichment.equivFunctor SSet C).map_id _

@[simp]
theorem coherentSimplexOfChainUnitGradedNatTrans_comp
    {n : ℕ}
    {F G H : CategoryTheory.ComposableArrows
      (CategoryTheory.ForgetEnrichment SSet.{v} C) n}
    (α : F ⟶ G) (β : G ⟶ H) :
    coherentSimplexOfChainUnitGradedNatTrans C (α ≫ β) =
      SSetUnitGradedNatTrans.comp
        (coherentSimplexOfChainUnitGradedNatTrans C α)
        (coherentSimplexOfChainUnitGradedNatTrans C β) := by
  apply GradedNatTrans.ext
  funext i
  apply (eHomEquiv SSet).symm.injective
  change
    (coherentSimplexOfChainUnitGradedNatTrans C (α ≫ β)).componentHom i =
      (SSetUnitGradedNatTrans.comp
        (coherentSimplexOfChainUnitGradedNatTrans C α)
        (coherentSimplexOfChainUnitGradedNatTrans C β)).componentHom i
  rw [coherentSimplexOfChainUnitGradedNatTrans_componentHom,
    SSetUnitGradedNatTrans.componentHom_comp,
    coherentSimplexOfChainUnitGradedNatTrans_componentHom,
    coherentSimplexOfChainUnitGradedNatTrans_componentHom]
  exact (CategoryTheory.ForgetEnrichment.equivFunctor SSet C).map_comp _ _

end LeanLCAExactChallenge.Infinity.OrdinaryToSimplicialNerve
