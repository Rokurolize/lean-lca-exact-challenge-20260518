/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.EndpointMappingSpaceKan

/-! # Inner horns in strict endpoint mapping spaces -/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge
namespace Infinity

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open Opposite Simplicial

private lemma boundaryOne_constant {U : SimplexCategory} (s : (∂Δ[1] : SSet.{u}).obj (op U))
    (j : Fin (U.len + 1)) :
    SSet.stdSimplex.asOrderHom s.val j = SSet.stdSimplex.asOrderHom s.val 0 := by
  rcases SSet.mem_boundary_iff_notMem_range s.val |>.mp s.property with ⟨i, hi⟩
  fin_cases i
  · have hs : ∀ l, SSet.stdSimplex.asOrderHom s.val l = 1 := by
      intro l
      let z := SSet.stdSimplex.asOrderHom s.val l
      have h : z = 0 ∨ z = 1 := by
        by_cases hz : z = 0
        · exact Or.inl hz
        · exact Or.inr (Fin.eq_one_of_ne_zero z hz)
      rcases h with h | h
      · exact (hi ⟨l, h⟩).elim
      · exact h
    rw [hs j, hs 0]
  · have hs : ∀ l, SSet.stdSimplex.asOrderHom s.val l = 0 := by
      intro l
      let z := SSet.stdSimplex.asOrderHom s.val l
      have h : z = 0 ∨ z = 1 := by
        by_cases hz : z = 0
        · exact Or.inl hz
        · exact Or.inr (Fin.eq_one_of_ne_zero z hz)
      rcases h with h | h
      · exact h
      · exact (hi ⟨l, h⟩).elim
    rw [hs j, hs 0]

private def boundaryOneEndpoints (Q : SSet.{u}) (x y : Q _⦋0⦌) :
    (∂Δ[1] : SSet.{u}) ⟶ Q where
  app U := ↾fun s ↦ if SSet.stdSimplex.asOrderHom s.val 0 = 0 then
      Q.map (U.unop.const ⦋0⦌ 0).op x
    else Q.map (U.unop.const ⦋0⦌ 0).op y
  naturality U V f := by
    ext s
    have hs : SSet.stdSimplex.asOrderHom ((∂Δ[1] : SSet.{u}).map f s).val 0 =
        SSet.stdSimplex.asOrderHom s.val 0 := by
      exact boundaryOne_constant s _
    change (if SSet.stdSimplex.asOrderHom ((∂Δ[1] : SSet.{u}).map f s).val 0 = 0 then
        Q.map (V.unop.const ⦋0⦌ 0).op x else Q.map (V.unop.const ⦋0⦌ 0).op y) =
      Q.map f (if SSet.stdSimplex.asOrderHom s.val 0 = 0 then
        Q.map (U.unop.const ⦋0⦌ 0).op x else Q.map (U.unop.const ⦋0⦌ 0).op y)
    rw [hs]
    split_ifs <;> rw [← CategoryTheory.comp_apply, ← Functor.map_comp] <;> rfl

private lemma boundaryOneEndpoints_ι_one (Q : SSet.{u}) (x y : Q _⦋0⦌) :
    SSet.boundary.ι (1 : Fin 2) ≫ boundaryOneEndpoints Q x y = SSet.const x := by
  ext U s
  have hs : s = (SSet.stdSimplex.const 0 0 U : (Δ[0] : SSet.{u}).obj U) := by
    apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext j
    exact Fin.eq_zero _
  rw [hs]
  change (if SSet.stdSimplex.asOrderHom
      ((SSet.boundary.ι (1 : Fin 2)).app U
        (SSet.stdSimplex.const 0 0 U : (Δ[0] : SSet.{u}).obj U)).val 0 = 0 then
        Q.map (U.unop.const ⦋0⦌ 0).op x else Q.map (U.unop.const ⦋0⦌ 0).op y) = _
  rw [if_pos (by rfl)]
  rfl

private lemma boundaryOneEndpoints_ι_zero (Q : SSet.{u}) (x y : Q _⦋0⦌) :
    SSet.boundary.ι (0 : Fin 2) ≫ boundaryOneEndpoints Q x y = SSet.const y := by
  ext U s
  have hs : s = (SSet.stdSimplex.const 0 0 U : (Δ[0] : SSet.{u}).obj U) := by
    apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext j
    exact Fin.eq_zero _
  rw [hs]
  change (if SSet.stdSimplex.asOrderHom
      ((SSet.boundary.ι (0 : Fin 2)).app U
        (SSet.stdSimplex.const 0 0 U : (Δ[0] : SSet.{u}).obj U)).val 0 = 0 then
        Q.map (U.unop.const ⦋0⦌ 0).op x else Q.map (U.unop.const ⦋0⦌ 0).op y) = _
  rw [if_neg (by
    intro h
    have h' : SSet.stdSimplex.asOrderHom
        ((SSet.boundary.ι (0 : Fin 2)).app U
          (SSet.stdSimplex.const 0 0 U : (Δ[0] : SSet.{u}).obj U)).val 0 = 1 := by rfl
    exact Fin.zero_ne_one (h.symm.trans h'))]
  rfl

private lemma tensorBoundaryOne_hom_ext (D Z : SSet.{u})
    (f g : D ⊗ (∂Δ[1] : SSet.{u}) ⟶ Z)
    (h₀ : (D ◁ SSet.boundary.ι (1 : Fin 2)) ≫ f =
      (D ◁ SSet.boundary.ι (1 : Fin 2)) ≫ g)
    (h₁ : (D ◁ SSet.boundary.ι (0 : Fin 2)) ≫ f =
      (D ◁ SSet.boundary.ι (0 : Fin 2)) ≫ g) : f = g := by
  apply MonoidalClosed.curry_injective
  apply SSet.boundary.hom_ext (n := 0)
  intro i
  fin_cases i
  · have h := congrArg MonoidalClosed.curry h₁
    simp only [MonoidalClosed.curry_natural_left] at h
    convert h using 1 <;> congr 2
  · have h := congrArg MonoidalClosed.curry h₀
    simp only [MonoidalClosed.curry_natural_left] at h
    convert h using 1 <;> congr 2

theorem endpointFiber_innerHorn_filling
    (Q : SSet.{u}) (_hQ : SSet.Quasicategory Q) (x y : Q _⦋0⦌)
    (n : ℕ) (k : Fin (n + 2)) (h0 : 0 < k) (hn : k < Fin.last (n + 1))
    (a : (Λ[n + 1, k] : SSet.{u}) ⟶ endpointFiber Q x y) :
    ∃ b : (Δ[n + 1] : SSet.{u}) ⟶ endpointFiber Q x y,
      (SSet.horn (n + 1) k).ι ≫ b = a := by
  let e := endpointEvaluation Q
  let q := endpointPoint Q x y
  let p : endpointFiber Q x y ⟶ (ihom (Δ[1] : SSet.{u})).obj Q := pullback.snd q e
  let r : (Δ[n + 1] : SSet.{u}) ⊗ (∂Δ[1] : SSet.{u}) ⟶ Q :=
    CartesianMonoidalCategory.snd _ _ ≫ boundaryOneEndpoints Q x y
  let d : (Λ[n + 1, k] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ Q :=
    (β_ (Λ[n + 1, k] : SSet.{u}) (Δ[1] : SSet.{u})).hom ≫
      MonoidalClosed.uncurry (a ≫ p)
  have endpoint_rows (D : SSet.{u}) (f : D ⟶ endpointFiber Q x y) :
      ((D ◁ SSet.stdSimplex.δ (1 : Fin 2)) ≫
          (β_ D (Δ[1] : SSet.{u})).hom ≫ MonoidalClosed.uncurry (f ≫ p) = SSet.const x) ∧
        ((D ◁ SSet.stdSimplex.δ (0 : Fin 2)) ≫
          (β_ D (Δ[1] : SSet.{u})).hom ≫ MonoidalClosed.uncurry (f ≫ p) = SSet.const y) := by
    have hp : f ≫ p ≫ e = f ≫ pullback.fst q e ≫ q := by
      simpa only [p, q, e, Category.assoc] using
        congrArg (fun t ↦ f ≫ t) (pullback.condition (f := q) (g := e)).symm
    constructor
    · have hp₀ := congrArg
          (fun z ↦ z ≫ CartesianMonoidalCategory.fst
            ((ihom (Δ[0] : SSet.{u})).obj Q) ((ihom (Δ[0] : SSet.{u})).obj Q)) hp
      simp only [Category.assoc, e, endpointEvaluation,
        CartesianMonoidalCategory.lift_fst, q, endpointPoint] at hp₀
      have hp₀' := congrArg MonoidalClosed.uncurry hp₀
      simp only [MonoidalClosed.uncurry_natural_left] at hp₀'
      rw [BraidedCategory.braiding_naturality_right_assoc,
        MonoidalClosed.uncurry_natural_left, ← MonoidalCategory.whisker_exchange_assoc,
        ← MonoidalClosed.uncurry_pre_app, MonoidalClosed.uncurry_natural_left, hp₀']
      simp [endpointVertex, MonoidalClosed.curry']
    · have hp₁ := congrArg
          (fun z ↦ z ≫ CartesianMonoidalCategory.snd
            ((ihom (Δ[0] : SSet.{u})).obj Q) ((ihom (Δ[0] : SSet.{u})).obj Q)) hp
      simp only [Category.assoc, e, endpointEvaluation,
        CartesianMonoidalCategory.lift_snd, q, endpointPoint] at hp₁
      have hp₁' := congrArg MonoidalClosed.uncurry hp₁
      simp only [MonoidalClosed.uncurry_natural_left] at hp₁'
      rw [BraidedCategory.braiding_naturality_right_assoc,
        MonoidalClosed.uncurry_natural_left, ← MonoidalCategory.whisker_exchange_assoc,
        ← MonoidalClosed.uncurry_pre_app, MonoidalClosed.uncurry_natural_left, hp₁']
      simp [endpointVertex, MonoidalClosed.curry']
  have hcompat :
      ((SSet.horn (n + 1) k).ι ▷ (∂Δ[1] : SSet.{u})) ≫ r =
        ((Λ[n + 1, k] : SSet.{u}) ◁ (SSet.boundary 1).ι) ≫ d := by
    apply tensorBoundaryOne_hom_ext
    · dsimp only [r, d]
      simp only [CartesianMonoidalCategory.whiskerRight_snd_assoc,
        CartesianMonoidalCategory.whiskerLeft_snd_assoc,
        ← MonoidalCategory.whiskerLeft_comp_assoc, SSet.boundary.ι_ι]
      rw [boundaryOneEndpoints_ι_one, SSet.comp_const]
      exact (endpoint_rows (Λ[n + 1, k] : SSet.{u}) a).1.symm
    · dsimp only [r, d]
      simp only [CartesianMonoidalCategory.whiskerRight_snd_assoc,
        CartesianMonoidalCategory.whiskerLeft_snd_assoc,
        ← MonoidalCategory.whiskerLeft_comp_assoc, SSet.boundary.ι_ι]
      rw [boundaryOneEndpoints_ι_zero, SSet.comp_const]
      exact (endpoint_rows (Λ[n + 1, k] : SSet.{u}) a).2.symm
  let c : endpointHornUnion n k ⟶ Q :=
    (SSet.Subcomplex.unionProd.isPushout
      (SSet.horn (n + 1) k) (SSet.boundary 1)).desc r d hcompat
  have hc₁ :
      SSet.Subcomplex.unionProd.ι₁ (SSet.horn (n + 1) k) (SSet.boundary 1) ≫ c = r := by
    exact (SSet.Subcomplex.unionProd.isPushout
      (SSet.horn (n + 1) k) (SSet.boundary 1)).inl_desc _ _ _
  have hc₂ :
      SSet.Subcomplex.unionProd.ι₂ (SSet.horn (n + 1) k) (SSet.boundary 1) ≫ c = d := by
    exact (SSet.Subcomplex.unionProd.isPushout
      (SSet.horn (n + 1) k) (SSet.boundary 1)).inr_desc _ _ _
  have hrows : HasFixedEndpointRows Q x y n r := by
    constructor
    · simp [r, boundaryOneEndpoints_ι_one]
    · simp [r, boundaryOneEndpoints_ι_zero]
  apply (endpointFiberHornUnionProductCorrespondence Q x y n k a r c hrows hc₁ hc₂).2
  letI : SSet.Quasicategory Q := _hQ
  have hlp := SSet.prodStdSimplex.innerAnodyneExtensions_unionProd_ι k h0 hn 1
  letI : HasLiftingProperty
      (SSet.Subcomplex.unionProd.{u} Λ[n + 1, k] ∂Δ[1]).ι (terminal.from Q) :=
    hlp (terminal.from Q) (SSet.mem_innerFibrations _)
  let sq : CommSq c (SSet.Subcomplex.unionProd.{u} Λ[n + 1, k] ∂Δ[1]).ι
      (terminal.from Q) (terminal.from ((Δ[n + 1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}))) :=
    CommSq.mk (terminalIsTerminal.hom_ext _ _)
  exact ⟨sq.lift, sq.fac_left⟩

end Infinity
end LeanLCAExactChallenge
