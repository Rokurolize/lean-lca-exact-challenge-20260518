/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGMappingZModuleVertexComposition

/-!
# Vertices of the integer-module Dold--Kan mapping composition

This file proves that normalized Alexander--Whitney composition on mapping simplicial
sets agrees on vertices with ordinary composition of bounded-complex morphisms.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes

open AlgebraicTopology
open CategoryTheory
open CategoryTheory.MonoidalCategory
open Opposite
open Simplicial

theorem dgMappingZModuleSimplicialComposition_f_zero
    (K L M : ComplexCategory) :
    (dgMappingZModuleSimplicialComposition
          DoldKanMonoidal.normalizedMooreOplaxMonoidal K L M).app (op ⦋0⦌) ≫
        (zModuleDoldKanInverseZeroIso
          (dgMappingZModuleChainComplex K M)).inv =
      (β_ (dgMappingZModuleSimplicialModule K L)
          (dgMappingZModuleSimplicialModule L M)).hom.app (op ⦋0⦌) ≫
        (((zModuleDoldKanInverseZeroIso
              (dgMappingZModuleChainComplex L M)).inv ⊗ₘ
            (zModuleDoldKanInverseZeroIso
              (dgMappingZModuleChainComplex K L)).inv) ≫
          HomologicalComplex.ιTensorObj
            (dgMappingZModuleChainComplex L M)
            (dgMappingZModuleChainComplex K L) 0 0 0 rfl) ≫
        (dgMappingZModuleChainComposition K L M).f 0 := by
  let A := dgMappingZModuleChainComplex K L
  let B := dgMappingZModuleChainComplex L M
  let C := dgMappingZModuleChainComplex K M
  let X := dgMappingZModuleSimplicialModule K L
  let Y := dgMappingZModuleSimplicialModule L M
  let c := dgMappingZModuleChainComposition K L M
  let μ := DoldKanMonoidal.inverseTensorator
    DoldKanMonoidal.normalizedMooreOplaxMonoidal B A
  let β := (β_ X Y).hom.app (op ⦋0⦌)
  let zA := (zModuleDoldKanInverseZeroIso A).inv
  let zB := (zModuleDoldKanInverseZeroIso B).inv
  let zC := (zModuleDoldKanInverseZeroIso C).inv
  let ι := HomologicalComplex.ιTensorObj B A 0 0 0 rfl
  have hc := zModuleDoldKanInverseZeroIso_inv_naturality c
  have hμ := inverseTensorator_f_zero B A
  change ((β ≫ μ.app (op ⦋0⦌)) ≫
      (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.map c).app
        (op ⦋0⦌)) ≫ zC =
    β ≫ ((zB ⊗ₘ zA) ≫ ι) ≫ c.f 0
  calc
    _ = (β ≫ μ.app (op ⦋0⦌)) ≫
        ((DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.map c).app
          (op ⦋0⦌) ≫ zC) := Category.assoc _ _ _
    _ = (β ≫ μ.app (op ⦋0⦌)) ≫
        ((zModuleDoldKanInverseZeroIso (B ⊗ A)).inv ≫ c.f 0) :=
      congrArg (fun t => (β ≫ μ.app (op ⦋0⦌)) ≫ t) hc
    _ = β ≫
        ((μ.app (op ⦋0⦌) ≫
          (zModuleDoldKanInverseZeroIso (B ⊗ A)).inv) ≫ c.f 0) := by
      simp only [Category.assoc]
    _ = β ≫ (((zB ⊗ₘ zA) ≫ ι) ≫ c.f 0) :=
      congrArg (fun t => β ≫ (t ≫ c.f 0)) hμ
    _ = _ := by simp only [Category.assoc]

theorem dgMappingZModuleSimplicialComposition_f_zero_apply
    (K L M : ComplexCategory)
    (f : (dgMappingZModuleSimplicialModule K L).obj (op ⦋0⦌))
    (g : (dgMappingZModuleSimplicialModule L M).obj (op ⦋0⦌)) :
    (zModuleDoldKanInverseZeroIso
        (dgMappingZModuleChainComplex K M)).inv
      ((dgMappingZModuleSimplicialComposition
          DoldKanMonoidal.normalizedMooreOplaxMonoidal K L M).app
        (op ⦋0⦌) (f ⊗ₜ[ℤ] g)) =
      (dgMappingZModuleChainComposition K L M).f 0
        (HomologicalComplex.ιTensorObj
          (dgMappingZModuleChainComplex L M)
          (dgMappingZModuleChainComplex K L) 0 0 0 rfl
          (((zModuleDoldKanInverseZeroIso
              (dgMappingZModuleChainComplex L M)).inv g) ⊗ₜ[ℤ]
            ((zModuleDoldKanInverseZeroIso
              (dgMappingZModuleChainComplex K L)).inv f))) := by
  have h := ConcreteCategory.congr_hom
    (dgMappingZModuleSimplicialComposition_f_zero K L M) (f ⊗ₜ[ℤ] g)
  simp only [CategoryTheory.comp_apply] at h
  exact h

theorem dgMappingZModuleSSetComposition_f_zero_apply
    (K L M : ComplexCategory)
    (f : (dgMappingZModuleSimplicialModule K L).obj (op ⦋0⦌))
    (g : (dgMappingZModuleSimplicialModule L M).obj (op ⦋0⦌)) :
    (zModuleDoldKanInverseZeroIso
        (dgMappingZModuleChainComplex K M)).inv
      ((dgMappingZModuleSSetComposition
          DoldKanMonoidal.normalizedMooreOplaxMonoidal K L M).app
        (op ⦋0⦌) (f, g)) =
      (dgMappingZModuleChainComposition K L M).f 0
        (HomologicalComplex.ιTensorObj
          (dgMappingZModuleChainComplex L M)
          (dgMappingZModuleChainComplex K L) 0 0 0 rfl
          (((zModuleDoldKanInverseZeroIso
              (dgMappingZModuleChainComplex L M)).inv g) ⊗ₜ[ℤ]
            ((zModuleDoldKanInverseZeroIso
              (dgMappingZModuleChainComplex K L)).inv f))) := by
  simpa [dgMappingZModuleSSetComposition,
    simplicialZModuleTensorPairing, CategoryTheory.comp_apply] using
      dgMappingZModuleSimplicialComposition_f_zero_apply K L M f g

theorem dgMappingZModuleVerticesEquivBoundedMorphisms_comp
    (K L M : ComplexCategory)
    (f : dgMappingZModuleSSet K L _⦋0⦌)
    (g : dgMappingZModuleSSet L M _⦋0⦌) :
    dgMappingZModuleVerticesEquivBoundedMorphisms K M
        ((dgMappingZModuleSSetComposition
          DoldKanMonoidal.normalizedMooreOplaxMonoidal K L M).app
            (op ⦋0⦌) (f, g)) =
      dgMappingZModuleVerticesEquivBoundedMorphisms K L f ≫
        dgMappingZModuleVerticesEquivBoundedMorphisms L M g := by
  let x := (zModuleDoldKanInverseZeroIso
    (dgMappingZModuleChainComplex K L)).inv f
  let y := (zModuleDoldKanInverseZeroIso
    (dgMappingZModuleChainComplex L M)).inv g
  have hzero := dgMappingZModuleSSetComposition_f_zero_apply K L M f g
  change dgMappingZModuleChainComplexZeroEquivBoundedHom K M
      ((zModuleDoldKanInverseZeroIso
        (dgMappingZModuleChainComplex K M)).inv
        ((dgMappingZModuleSSetComposition
          DoldKanMonoidal.normalizedMooreOplaxMonoidal K L M).app
            (op ⦋0⦌) (f, g))) =
    dgMappingZModuleChainComplexZeroEquivBoundedHom K L x ≫
      dgMappingZModuleChainComplexZeroEquivBoundedHom L M y
  rw [hzero]
  exact dgMappingZModuleChainComposition_zero_tmul K L M x y

end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
