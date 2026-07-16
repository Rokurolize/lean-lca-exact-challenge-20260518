/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.EndpointMappingSpaces
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct

/-! # Horn filling in strict endpoint mapping spaces -/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge
namespace Infinity

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open Opposite Simplicial

/-- The union of a horn cylinder and both endpoint rows of the full cylinder. -/
abbrev endpointHornUnion (n : ℕ) (k : Fin (n + 2)) : SSet.{u} :=
  SSet.Subcomplex.unionProd.{u} Λ[n + 1, k] ∂Δ[1]

/-- A map on the boundary rows of a cylinder is fixed at the prescribed endpoints. -/
def HasFixedEndpointRows (Q : SSet.{u}) (x y : Q _⦋0⦌) (n : ℕ)
    (r : (Δ[n + 1] : SSet.{u}) ⊗ (∂Δ[1] : SSet.{u}) ⟶ Q) : Prop :=
  ((Δ[n + 1] : SSet.{u}) ◁ SSet.boundary.ι (1 : Fin 2)) ≫ r = SSet.const x ∧
    ((Δ[n + 1] : SSet.{u}) ◁ SSet.boundary.ι (0 : Fin 2)) ≫ r = SSet.const y

/-- Filling a horn in the strict endpoint fiber is equivalent to extending the corresponding
horn-cylinder map together with its two fixed endpoint rows. -/
theorem endpointFiberHornUnionProductCorrespondence
    (Q : SSet.{u}) (x y : Q _⦋0⦌) (n : ℕ) (k : Fin (n + 2))
    (a : (Λ[n + 1, k] : SSet.{u}) ⟶ endpointFiber Q x y)
    (r : (Δ[n + 1] : SSet.{u}) ⊗ (∂Δ[1] : SSet.{u}) ⟶ Q)
    (c : endpointHornUnion n k ⟶ Q)
    (hrows : HasFixedEndpointRows Q x y n r)
    (hc₁ : SSet.Subcomplex.unionProd.ι₁ (SSet.horn (n + 1) k) (SSet.boundary 1) ≫ c = r)
    (hc₂ : SSet.Subcomplex.unionProd.ι₂ (SSet.horn (n + 1) k) (SSet.boundary 1) ≫ c =
      (β_ (Λ[n + 1, k] : SSet.{u}) (Δ[1] : SSet.{u})).hom ≫
        MonoidalClosed.uncurry
          (a ≫ pullback.snd (endpointPoint Q x y) (endpointEvaluation Q))) :
    ((∃ b : (Δ[n + 1] : SSet.{u}) ⟶ endpointFiber Q x y,
        (SSet.horn (n + 1) k).ι ≫ b = a) ↔
      (∃ b : (Δ[n + 1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ Q,
        (SSet.Subcomplex.unionProd.{u} Λ[n + 1, k] ∂Δ[1]).ι ≫ b = c)) := by
  let e := endpointEvaluation Q
  let q := endpointPoint Q x y
  let p : endpointFiber Q x y ⟶ (ihom (Δ[1] : SSet.{u})).obj Q := pullback.snd q e
  have boundary_rows_hom_ext (D Z : SSet.{u})
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
  have endpoint_rows (D : SSet.{u}) (d : D ⟶ endpointFiber Q x y) :
      ((D ◁ SSet.stdSimplex.δ (1 : Fin 2)) ≫
          (β_ D (Δ[1] : SSet.{u})).hom ≫ MonoidalClosed.uncurry (d ≫ p) = SSet.const x) ∧
        ((D ◁ SSet.stdSimplex.δ (0 : Fin 2)) ≫
          (β_ D (Δ[1] : SSet.{u})).hom ≫ MonoidalClosed.uncurry (d ≫ p) = SSet.const y) := by
    have hp : d ≫ p ≫ e = d ≫ pullback.fst q e ≫ q := by
      simpa only [p, q, e, Category.assoc] using
        congrArg (fun t ↦ d ≫ t) (pullback.condition (f := q) (g := e)).symm
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
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨(β_ (Δ[n + 1] : SSet.{u}) (Δ[1] : SSet.{u})).hom ≫
      MonoidalClosed.uncurry (d ≫ p), ?_⟩
    apply (SSet.Subcomplex.unionProd.isPushout
      (SSet.horn (n + 1) k) (SSet.boundary 1)).hom_ext
    · rw [SSet.Subcomplex.unionProd.ι₁_ι_assoc, hc₁]
      rcases hrows with ⟨hrx, hry⟩
      apply boundary_rows_hom_ext
      · simpa only [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
          SSet.boundary.ι_ι] using
          (endpoint_rows (Δ[n + 1] : SSet.{u}) d).1.trans hrx.symm
      · simpa only [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
          SSet.boundary.ι_ι] using
          (endpoint_rows (Δ[n + 1] : SSet.{u}) d).2.trans hry.symm
    · rw [SSet.Subcomplex.unionProd.ι₂_ι_assoc]
      rw [BraidedCategory.braiding_naturality_left_assoc,
        MonoidalClosed.uncurry_natural_left, ← MonoidalCategory.whiskerLeft_comp_assoc,
        hd, ← MonoidalClosed.uncurry_natural_left]
      simpa only [p] using hc₂.symm
  · rintro ⟨b, hb⟩
    let pb : (Δ[n + 1] : SSet.{u}) ⟶ (ihom (Δ[1] : SSet.{u})).obj Q :=
      MonoidalClosed.curry
        ((β_ (Δ[1] : SSet.{u}) (Δ[n + 1] : SSet.{u})).hom ≫ b)
    have hpb : SemiCartesianMonoidalCategory.toUnit (Δ[n + 1] : SSet.{u}) ≫ q = pb ≫ e := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, Category.assoc]
        simp only [q, endpointPoint, e, endpointEvaluation,
          CartesianMonoidalCategory.lift_fst]
        apply MonoidalClosed.uncurry_injective
        rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_pre_app]
        rcases hrows with ⟨hrx, _⟩
        have hrowb :
            ((Δ[n + 1] : SSet.{u}) ◁ SSet.boundary.ι (1 : Fin 2)) ≫ r =
              ((Δ[n + 1] : SSet.{u}) ◁ SSet.stdSimplex.δ (1 : Fin 2)) ≫ b := by
          rw [← hc₁, ← hb]
          simp only [SSet.Subcomplex.unionProd.ι₁_ι_assoc]
          rw [← MonoidalCategory.whiskerLeft_comp_assoc, SSet.boundary.ι_ι]
        have h := congrArg
          (fun t ↦ (β_ (Δ[0] : SSet.{u}) (Δ[n + 1] : SSet.{u})).hom ≫ t)
          (hrx.symm.trans hrowb)
        simp [pb, endpointVertex, MonoidalClosed.curry']
        simpa only [Category.assoc, SSet.comp_const] using h
      · rw [Category.assoc, Category.assoc]
        simp only [q, endpointPoint, e, endpointEvaluation,
          CartesianMonoidalCategory.lift_snd]
        apply MonoidalClosed.uncurry_injective
        rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_pre_app]
        rcases hrows with ⟨_, hry⟩
        have hrowb :
            ((Δ[n + 1] : SSet.{u}) ◁ SSet.boundary.ι (0 : Fin 2)) ≫ r =
              ((Δ[n + 1] : SSet.{u}) ◁ SSet.stdSimplex.δ (0 : Fin 2)) ≫ b := by
          rw [← hc₁, ← hb]
          simp only [SSet.Subcomplex.unionProd.ι₁_ι_assoc]
          rw [← MonoidalCategory.whiskerLeft_comp_assoc, SSet.boundary.ι_ι]
        have h := congrArg
          (fun t ↦ (β_ (Δ[0] : SSet.{u}) (Δ[n + 1] : SSet.{u})).hom ≫ t)
          (hry.symm.trans hrowb)
        simp [pb, endpointVertex, MonoidalClosed.curry']
        simpa only [Category.assoc, SSet.comp_const] using h
    let d : (Δ[n + 1] : SSet.{u}) ⟶ endpointFiber Q x y :=
      pullback.lift (SemiCartesianMonoidalCategory.toUnit (Δ[n + 1] : SSet.{u})) pb hpb
    refine ⟨d, ?_⟩
    apply pullback.hom_ext
    · apply (SemiCartesianMonoidalCategory.isTerminalTensorUnit (C := SSet.{u})).hom_ext
    · rw [Category.assoc]
      simp only [d, pullback.lift_snd]
      apply MonoidalClosed.uncurry_injective
      rw [MonoidalClosed.uncurry_natural_left]
      apply (cancel_epi
        (β_ (Λ[n + 1, k] : SSet.{u}) (Δ[1] : SSet.{u})).hom).1
      rw [← hc₂, ← hb, SSet.Subcomplex.unionProd.ι₂_ι_assoc]
      simp [pb]

end Infinity
end LeanLCAExactChallenge
