/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.QuotientAlexanderWhitneyChainMap

/-! # Alexander--Whitney naturality -/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord
namespace QuotientDoldKanMonoidal

open AlgebraicTopology
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Opposite

variable (X Y : SimplicialObject (QuotientModule))

/-- The unnormalized Alexander--Whitney chain map. -/
def alternatingAlexanderWhitney :
    alternatingChains (X ⊗ Y) ⟶
      HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y) where
  f := alternatingAlexanderWhitneyDegree X Y
  comm' := by
    rintro _ n ⟨rfl⟩
    exact (alternatingAlexanderWhitneyDegree_comm X Y n).symm

@[simp]
theorem alternatingAlexanderWhitney_f (n : ℕ) :
    (alternatingAlexanderWhitney X Y).f n =
      alternatingAlexanderWhitneyDegree X Y n := rfl

theorem alternatingAlexanderWhitneySummand_natural
    {X' Y' : SimplicialObject (QuotientModule)}
    (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ) (p : Fin (n + 1)) :
    alternatingAlexanderWhitneySummand X Y n p ≫
        (HomologicalComplex.tensorHom
          ((alternatingFaceMapComplex (QuotientModule)).map f)
          ((alternatingFaceMapComplex (QuotientModule)).map g)).f n =
      (f ⊗ₘ g).app (op (SimplexCategory.mk n)) ≫
        alternatingAlexanderWhitneySummand X' Y' n p := by
  rw [alternatingAlexanderWhitneySummand, alternatingAlexanderWhitneySummand,
    Category.assoc]
  erw [HomologicalComplex.ι_mapBifunctorMap]
  have hmid :
      ((curriedTensor (QuotientModule)).map
          (((alternatingFaceMapComplex (QuotientModule)).map f).f p)).app
            (((alternatingFaceMapComplex (QuotientModule)).obj Y).X (n - p)) ≫
        ((curriedTensor (QuotientModule)).obj
          (((alternatingFaceMapComplex (QuotientModule)).obj X').X p)).map
            (((alternatingFaceMapComplex (QuotientModule)).map g).f (n - p)) =
      (((alternatingFaceMapComplex (QuotientModule)).map f).f p ⊗ₘ
        ((alternatingFaceMapComplex (QuotientModule)).map g).f (n - p)) :=
    (MonoidalCategory.tensorHom_def _ _).symm
  have hpre :
      (X.map (alexanderWhitneyFront n p).op ⊗ₘ
          Y.map (alexanderWhitneyBack n p).op) ≫
          (((curriedTensor (QuotientModule)).map
            (((alternatingFaceMapComplex (QuotientModule)).map f).f p)).app
              (((alternatingFaceMapComplex (QuotientModule)).obj Y).X (n - p)) ≫
            ((curriedTensor (QuotientModule)).obj
              (((alternatingFaceMapComplex (QuotientModule)).obj X').X p)).map
                (((alternatingFaceMapComplex (QuotientModule)).map g).f (n - p))) =
        (f ⊗ₘ g).app (op (SimplexCategory.mk n)) ≫
          (X'.map (alexanderWhitneyFront n p).op ⊗ₘ
            Y'.map (alexanderWhitneyBack n p).op) := by
    have hfirst := congrArg
      (fun t =>
        (X.map (alexanderWhitneyFront n p).op ⊗ₘ
          Y.map (alexanderWhitneyBack n p).op) ≫ t) hmid
    refine hfirst.trans ?_
    simp only [alternatingFaceMapComplex_map_f]
    rw [Monoidal.tensorHom_app]
    calc
      (X.map (alexanderWhitneyFront n p).op ⊗ₘ
          Y.map (alexanderWhitneyBack n p).op) ≫
          (f.app (op (SimplexCategory.mk p)) ⊗ₘ
            g.app (op (SimplexCategory.mk (n - p)))) =
        (X.map (alexanderWhitneyFront n p).op ≫
            f.app (op (SimplexCategory.mk p))) ⊗ₘ
          (Y.map (alexanderWhitneyBack n p).op ≫
            g.app (op (SimplexCategory.mk (n - p)))) :=
        MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _
      _ = (f.app (op (SimplexCategory.mk n)) ≫
              X'.map (alexanderWhitneyFront n p).op) ⊗ₘ
          (g.app (op (SimplexCategory.mk n)) ≫
            Y'.map (alexanderWhitneyBack n p).op) := by
        rw [f.naturality, g.naturality]
      _ = (f.app (op (SimplexCategory.mk n)) ⊗ₘ
            g.app (op (SimplexCategory.mk n))) ≫
          (X'.map (alexanderWhitneyFront n p).op ⊗ₘ
            Y'.map (alexanderWhitneyBack n p).op) :=
        (MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _).symm
  have hpreAssoc := congrArg (fun t => t ≫
    HomologicalComplex.ιTensorObj
      ((alternatingFaceMapComplex (QuotientModule)).obj X')
      ((alternatingFaceMapComplex (QuotientModule)).obj Y')
      p (n - p) n (by omega)) hpre
  exact (Category.assoc _ _ _).symm.trans (hpreAssoc.trans (Category.assoc _ _ _))

/-- The Alexander--Whitney degree maps are natural in both simplicial modules. -/
theorem alternatingAlexanderWhitneyDegree_natural
    {X' Y' : SimplicialObject (QuotientModule)}
    (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ) :
    alternatingAlexanderWhitneyDegree X Y n ≫
        (HomologicalComplex.tensorHom
          ((alternatingFaceMapComplex (QuotientModule)).map f)
          ((alternatingFaceMapComplex (QuotientModule)).map g)).f n =
      (f ⊗ₘ g).app (op (SimplexCategory.mk n)) ≫
        alternatingAlexanderWhitneyDegree X' Y' n := by
  change
    (Finset.univ.sum fun p : Fin (n + 1) =>
      alternatingAlexanderWhitneySummand X Y n p) ≫ _ =
      _ ≫ Finset.univ.sum fun p : Fin (n + 1) =>
        alternatingAlexanderWhitneySummand X' Y' n p
  rw [CategoryTheory.Preadditive.sum_comp, CategoryTheory.Preadditive.comp_sum]
  exact Finset.sum_congr rfl fun p _ =>
    alternatingAlexanderWhitneySummand_natural X Y f g n p

/-- The unnormalized Alexander--Whitney chain map is natural in both variables. -/
theorem alternatingAlexanderWhitney_natural
    {X' Y' : SimplicialObject (QuotientModule)}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    alternatingAlexanderWhitney X Y ≫
        HomologicalComplex.tensorHom
          ((alternatingFaceMapComplex (QuotientModule)).map f)
          ((alternatingFaceMapComplex (QuotientModule)).map g) =
      (alternatingFaceMapComplex (QuotientModule)).map (f ⊗ₘ g) ≫
        alternatingAlexanderWhitney X' Y' := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact alternatingAlexanderWhitneyDegree_natural X Y f g n


end QuotientDoldKanMonoidal
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
