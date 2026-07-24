/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.InnerAnodyneVertices
import LeanLCAExactChallenge.Infinity.Relative
import Mathlib.AlgebraicTopology.Quasicategory.StrictBicategory

/-! # Essential surjectivity detected on vertices -/

set_option autoImplicit false

noncomputable section

universe u v

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory Opposite Simplicial

/-- Essential surjectivity is closed under composition without requiring temporary type-class
instances. -/
theorem functorEssSurj_comp_data
    {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
    (F : C ⥤ D) (G : D ⥤ E) (hF : F.EssSurj) (hG : G.EssSurj) :
    (F ⋙ G).EssSurj where
  mem_essImage Z := by
    obtain ⟨Y, ⟨eY⟩⟩ := hG.mem_essImage Z
    obtain ⟨X, ⟨eX⟩⟩ := hF.mem_essImage Y
    exact ⟨X, ⟨G.mapIso eX ≪≫ eY⟩⟩

/-- Essential surjectivity of two quasicategory maps passes to their composite. -/
theorem hoFunctorMap_comp_essSurj
    {X Y Z : SSet.QCat.{u}} (F : X ⟶ Y) (G : Y ⟶ Z)
    (hF : (SSet.hoFunctor.map F.hom).toFunctor.EssSurj)
    (hG : (SSet.hoFunctor.map G.hom).toFunctor.EssSurj) :
    (SSet.hoFunctor.map (F.hom ≫ G.hom)).toFunctor.EssSurj := by
  rw [SSet.hoFunctor.map_comp]
  exact functorEssSurj_comp_data _ _ hF hG

/-- A map of quasicategories that is surjective on vertices is essentially surjective on its
homotopy categories. -/
theorem hoFunctorMap_essSurj_of_vertex_surjective
    {X Y : SSet.QCat.{u}} (F : X ⟶ Y)
    (h0 : Function.Surjective (F.hom.app (op ⦋0⦌))) :
    (SSet.hoFunctor.map F.hom).toFunctor.EssSurj := by
  apply Functor.essSurj_of_surj
  intro y
  obtain ⟨y, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective y
  obtain ⟨x, rfl⟩ := h0 y
  exact ⟨SSet.Truncated.HomotopyCategory.mk x, rfl⟩

/-- An inner anodyne map between quasicategories is essentially surjective on homotopy
categories. -/
theorem hoFunctorMap_essSurj_of_innerAnodyne
    {X Y : SSet.QCat.{u}} (F : X ⟶ Y)
    (hF : SSet.innerAnodyneExtensions F.hom) :
    (SSet.hoFunctor.map F.hom).toFunctor.EssSurj :=
  hoFunctorMap_essSurj_of_vertex_surjective F
    (innerAnodyne_vertex_bijective hF).surjective

/-- The homotopy-category map induced by the nerve of an essentially surjective functor is
essentially surjective. -/
theorem hoFunctorMap_nerveMap_essSurj
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) [hF : F.EssSurj] :
    (SSet.hoFunctor.map (nerveMap F)).toFunctor.EssSurj where
  mem_essImage Y := by
    obtain ⟨y, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective Y
    let d : D := SSet.OneTruncation₂.nerveEquiv y
    obtain ⟨x, ⟨e⟩⟩ := hF.mem_essImage d
    let sx : SSet.OneTruncation₂
        ((SSet.truncation 2).obj (CategoryTheory.nerve C)) :=
      SSet.OneTruncation₂.nerveEquiv.symm x
    let tx : SSet.OneTruncation₂
        ((SSet.truncation 2).obj (CategoryTheory.nerve D)) :=
      SSet.OneTruncation₂.nerveEquiv.symm (F.obj x)
    let ty : SSet.OneTruncation₂
        ((SSet.truncation 2).obj (CategoryTheory.nerve D)) :=
      SSet.OneTruncation₂.nerveEquiv.symm d
    have hsx :
        ((SSet.truncation 2).map (nerveMap F)).app _ sx = tx := by
      exact CategoryTheory.nerveMap_app_mk₀ F x
    have hy : ty = y := SSet.OneTruncation₂.nerveEquiv.symm_apply_apply y
    let middle := by
      letI : IsIso
          (edgeHomotopyClass (CategoryTheory.nerve.edgeMk e.hom)) :=
        edgeIsEquivalence_nerve_of_isIso e.hom
      exact asIso (edgeHomotopyClass (CategoryTheory.nerve.edgeMk e.hom))
    let sourceObject := SSet.Truncated.HomotopyCategory.mk sx
    have hsource :
        (SSet.hoFunctor.map (nerveMap F)).toFunctor.obj sourceObject =
          SSet.Truncated.HomotopyCategory.mk tx := by
      change SSet.Truncated.HomotopyCategory.mk
          (((SSet.truncation 2).map (nerveMap F)).app _ sx) =
        SSet.Truncated.HomotopyCategory.mk tx
      rw [hsx]
    have htarget :
        SSet.Truncated.HomotopyCategory.mk ty =
          SSet.Truncated.HomotopyCategory.mk y := by
      exact congrArg
        (fun z => SSet.Truncated.HomotopyCategory.mk
          (V := (SSet.truncation 2).obj (CategoryTheory.nerve D)) z) hy
    refine ⟨sourceObject, ⟨?e⟩⟩
    dsimp [tx, ty] at hsource htarget ⊢
    exact eqToIso hsource ≪≫ middle ≪≫ eqToIso htarget

end LeanLCAExactChallenge.Infinity
