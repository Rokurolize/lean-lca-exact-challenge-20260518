/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.CoherentNerveMappingComparison
import LeanLCAExactChallenge.Infinity.RightMappingSpaces

/-! # Coherent enriched-Hom cones

An enriched-Hom simplex determines a coherent left cone in the homotopy coherent nerve. The
cone point is the selected source object and the right factor is the constant target diagram.
These endpoint identities are the fixed-base input for comparing enriched Hom objects with
representable left mapping spaces.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
namespace LeanLCAExactChallenge.Infinity.CoherentNerveMappingComparison

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped CategoryTheory.MonoidalCategory.DayConvolution
  MonoidalCategory.ExternalProduct MonoidalCategory Prod

variable (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]

/-- The interval simplex which is zero only at the initial vertex. -/
def initialStepOrderHom (n : ℕ) : Fin (n + 2) →o Fin 2 where
  toFun i := if i.val = 0 then 0 else 1
  monotone' := by
    intro a b hab
    by_cases hb : b.val = 0
    · have ha : a.val = 0 := by omega
      simp [ha, hb]
    · simp only [hb, if_false]
      exact Fin.le_last _

/-- The coherent cone simplex associated to one enriched Hom simplex. -/
def coherentArrowLeftConeSimplex {n : ℕ} {X Y : C}
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n))) :
    (CategoryTheory.SimplicialNerve C).obj
      (op (SimplexCategory.mk (n + 1))) :=
  coherentArrowSimplex C
    ((X ⟶[SSet] Y).map (SimplexCategory.σ (0 : Fin (n + 1))).op h)
    (SSet.stdSimplex.objMk (initialStepOrderHom n))

/-- The left cone on `Δ[n]`, normalized to the standard `(n+1)`-simplex. -/
def leftConeStdSimplexIso (n : ℕ) :
    simplicialJoin (Δ[0] : SSet.{u}) (Δ[n] : SSet.{u}) ≅
      (Δ[n + 1] : SSet.{u}) :=
  simplicialJoinStdSimplexIsoNat 0 n ≪≫
    SSet.stdSimplex.mapIso
      (eqToIso (congrArg SimplexCategory.mk (by omega : 0 + n + 1 = n + 1)))

/-- The right-factor inclusion of the normalized left cone is the zeroth coface. -/
theorem simplicialJoinRightInclusion_leftConeStdSimplexIso (n : ℕ) :
    simplicialJoinRightInclusion (Δ[0] : SSet.{u}) (Δ[n] : SSet.{u}) ≫
        (leftConeStdSimplexIso n).hom =
      SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin (n + 2))) := by
  unfold leftConeStdSimplexIso
  rw [Iso.trans_hom, ← Category.assoc, rightCone_rightInclusion_stdSimplex]
  change SSet.stdSimplex.map (standardJoinRightOperator 0 n) ≫
      SSet.stdSimplex.map (eqToHom
        (congrArg SimplexCategory.mk (by omega : 0 + n + 1 = n + 1))) = _
  rw [← Functor.map_comp]
  congr 1
  apply SimplexCategory.Hom.ext
  ext i
  simp [standardJoinRightOperator, SimplexCategory.δ]
  omega

/-- The cone point in the normalized left cone. -/
def leftConeVertex (n : ℕ) :
    (Δ[0] : SSet.{u}) ⟶ simplicialJoin (Δ[0] : SSet.{u}) (Δ[n] : SSet.{u}) :=
  simplicialJoinLeftInclusion (Δ[0] : SSet.{u}) (Δ[n] : SSet.{u})

@[reassoc]
theorem leftConeVertex_comp_leftConeStdSimplexIso (n : ℕ) :
    leftConeVertex n ≫ (leftConeStdSimplexIso n).hom =
      SSet.stdSimplex.map
        (SimplexCategory.const (SimplexCategory.mk 0)
          (SimplexCategory.mk (n + 1)) 0) := by
  unfold leftConeVertex leftConeStdSimplexIso
  rw [Iso.trans_hom, ← Category.assoc,
    simplicialJoinLeftInclusion_stdSimplex]
  change SSet.stdSimplex.map (standardJoinLeftOperator 0 n) ≫
      SSet.stdSimplex.map (eqToHom
        (congrArg SimplexCategory.mk (by omega : 0 + n + 1 = n + 1))) = _
  rw [← Functor.map_comp]
  congr 1
  apply SimplexCategory.Hom.ext
  ext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  simp [standardJoinLeftOperator]

/-- The coherent cone map associated to one enriched Hom simplex. -/
def coherentArrowLeftConeMap {n : ℕ} {X Y : C}
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n))) :
    simplicialJoin (Δ[0] : SSet.{u}) (Δ[n] : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C :=
  (leftConeStdSimplexIso n).hom ≫
    SSet.yonedaEquiv.symm (coherentArrowLeftConeSimplex C h)

/-- The right factor of the coherent cone is the constant target diagram. -/
theorem simplicialJoinRightInclusion_coherentArrowLeftConeMap {n : ℕ} {X Y : C}
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n))) :
    simplicialJoinRightInclusion (Δ[0] : SSet.{u}) (Δ[n] : SSet.{u}) ≫
        coherentArrowLeftConeMap C h =
      SSet.const (coherentNerveVertex C Y) := by
  unfold coherentArrowLeftConeMap
  rw [← Category.assoc, simplicialJoinRightInclusion_leftConeStdSimplexIso]
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_map]
  change (CategoryTheory.SimplicialNerve C).map
      (SimplexCategory.δ (0 : Fin (n + 2))).op
      (coherentArrowLeftConeSimplex C h) =
    (SSet.const (coherentNerveVertex C Y)).app
      (op (SimplexCategory.mk n)) (SSet.yonedaEquiv (𝟙 (Δ[n] : SSet.{u})))
  let h' := (X ⟶[SSet] Y).map
    (SimplexCategory.σ (0 : Fin (n + 1))).op h
  let s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk (n + 1))) :=
    SSet.stdSimplex.objMk (initialStepOrderHom n)
  let hs : ((X ⟶[SSet] Y) ⊗ (Δ[1] : SSet.{u})).obj
      (op (SimplexCategory.mk (n + 1))) := (h', s)
  have hn := (coherentArrowCylinderMap C (X := X) (Y := Y)).naturality_apply
    (SimplexCategory.δ (0 : Fin (n + 2))).op hs
  change coherentArrowSimplex C
      ((X ⟶[SSet] Y).map (SimplexCategory.δ (0 : Fin (n + 2))).op h')
      ((Δ[1] : SSet.{u}).map (SimplexCategory.δ (0 : Fin (n + 2))).op s) =
    (CategoryTheory.SimplicialNerve C).map
      (SimplexCategory.δ (0 : Fin (n + 2))).op
      (coherentArrowLeftConeSimplex C h) at hn
  rw [← hn]
  have hs : (Δ[1] : SSet.{u}).map
      (SimplexCategory.δ (0 : Fin (n + 2))).op s = intervalOneSimplex n := by
    apply SSet.stdSimplex.ext
    intro i
    change initialStepOrderHom n ((SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom i) = 1
    simp [initialStepOrderHom, SimplexCategory.δ]
  rw [hs]
  exact (coherentArrowSimplex_intervalOne C _).symm


/-- The cone point of the coherent cone is the selected source object. -/
theorem leftConeVertex_coherentArrowLeftConeMap {n : ℕ} {X Y : C}
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n))) :
    leftConeVertex n ≫ coherentArrowLeftConeMap C h =
      SSet.yonedaEquiv.symm (coherentNerveVertex C X) := by
  unfold coherentArrowLeftConeMap
  rw [← Category.assoc, leftConeVertex_comp_leftConeStdSimplexIso]
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_map, Equiv.apply_symm_apply]
  change (CategoryTheory.SimplicialNerve C).map
      (SimplexCategory.const (SimplexCategory.mk 0)
        (SimplexCategory.mk (n + 1)) 0).op
      (coherentArrowLeftConeSimplex C h) = coherentNerveVertex C X
  let h' := (X ⟶[SSet] Y).map
    (SimplexCategory.σ (0 : Fin (n + 1))).op h
  let s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk (n + 1))) :=
    SSet.stdSimplex.objMk (initialStepOrderHom n)
  let f := SimplexCategory.const (SimplexCategory.mk 0)
    (SimplexCategory.mk (n + 1)) 0
  let hs : ((X ⟶[SSet] Y) ⊗ (Δ[1] : SSet.{u})).obj
      (op (SimplexCategory.mk (n + 1))) := (h', s)
  have hn := (coherentArrowCylinderMap C (X := X) (Y := Y)).naturality_apply f.op hs
  change coherentArrowSimplex C ((X ⟶[SSet] Y).map f.op h')
      ((Δ[1] : SSet.{u}).map f.op s) =
    (CategoryTheory.SimplicialNerve C).map f.op
      (coherentArrowLeftConeSimplex C h) at hn
  rw [← hn]
  have hs0 : (Δ[1] : SSet.{u}).map f.op s = intervalZeroSimplex 0 := by
    apply SSet.stdSimplex.ext
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl
  rw [hs0]
  have hz := (coherentArrowSimplex_intervalZero C
    ((X ⟶[SSet] Y).map f.op h')).symm
  have hc : (SSet.const (coherentNerveVertex C X)).app
      (op (SimplexCategory.mk 0)) (zeroSimplex 0) = coherentNerveVertex C X := by
    change SSet.yonedaEquiv (SSet.const (coherentNerveVertex C X)) =
      coherentNerveVertex C X
    exact SSet.yonedaEquiv_const _
  exact hz.trans hc


end LeanLCAExactChallenge.Infinity.CoherentNerveMappingComparison
