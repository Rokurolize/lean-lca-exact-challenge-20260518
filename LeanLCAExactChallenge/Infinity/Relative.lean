/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.Basic
import Mathlib.AlgebraicTopology.Quasicategory.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction

/-!
# Relative infinity functors

This file defines equivalence edges using the simplicial homotopy category and packages a
simplicial map from the nerve of an ordinary relative category which inverts its specified
arrows.  Such a map is only inversion data; no localization universal property is asserted.
-/

set_option autoImplicit false

noncomputable section

universe u v

namespace LeanLCAExactChallenge
namespace Infinity

open CategoryTheory
open Simplicial

/-- An ordinary relative category: a category with a wide, composition-closed class of
specified weak equivalences. -/
structure RelativeCategoryData (C : Type u) [Category.{v} C] where
  weakEquivalences : MorphismProperty C
  isMultiplicative : weakEquivalences.IsMultiplicative

namespace RelativeCategoryData

/-- Install the multiplicativity evidence carried by a relative category. -/
instance {C : Type u} [Category.{v} C] (R : RelativeCategoryData C) :
    R.weakEquivalences.IsMultiplicative :=
  R.isMultiplicative

end RelativeCategoryData

/-- The object of the simplicial homotopy category represented by a vertex. -/
def homotopyObject {X : SSet.{u}} (x : X _⦋0⦌) : SSet.hoFunctor.obj X :=
  SSet.Truncated.HomotopyCategory.mk x

/-- The morphism in the simplicial homotopy category represented by an edge. -/
def edgeHomotopyClass {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : SSet.Edge x y) : homotopyObject x ⟶ homotopyObject y :=
  SSet.Truncated.HomotopyCategory.homMk e.toTruncated

/-- An edge is an equivalence when its homotopy class is an isomorphism.

For a quasicategory, this is the usual notion of an equivalence edge. -/
abbrev EdgeIsEquivalence {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : SSet.Edge x y) : Prop :=
  IsIso (edgeHomotopyClass e)

/-- Every identity edge is an equivalence. -/
theorem edgeIsEquivalence_id {X : SSet.{u}} (x : X _⦋0⦌) :
    EdgeIsEquivalence (SSet.Edge.id x) := by
  change IsIso (SSet.Truncated.HomotopyCategory.homMk
    (SSet.Edge.id x).toTruncated)
  rw [SSet.Edge.toTruncated_id]
  rw [SSet.Truncated.HomotopyCategory.homMk_id]
  infer_instance

/-- An isomorphism in an ordinary category gives an equivalence edge in its nerve. -/
theorem edgeIsEquivalence_nerve_of_isIso
    {C : Type u} [Category.{v} C] {X Y : C} (f : X ⟶ Y) [IsIso f] :
    EdgeIsEquivalence (CategoryTheory.nerve.edgeMk f) := by
  let g : Y ⟶ X := inv f
  let e := CategoryTheory.nerve.edgeMk f
  let e' := CategoryTheory.nerve.edgeMk g
  have hfg : f ≫ g = 𝟙 X := IsIso.hom_inv_id f
  have hgf : g ≫ f = 𝟙 Y := IsIso.inv_hom_id f
  obtain ⟨sfg⟩ :=
    (CategoryTheory.nerve.nonempty_compStruct_iff f g (𝟙 X)).2 hfg
  obtain ⟨sgf⟩ :=
    (CategoryTheory.nerve.nonempty_compStruct_iff g f (𝟙 Y)).2 hgf
  letI : IsIso (edgeHomotopyClass e) :=
    ⟨⟨edgeHomotopyClass e', by
      exact (SSet.Truncated.HomotopyCategory.homMk_comp_homMk
        sfg.toTruncated).trans (by
          rw [CategoryTheory.nerve.edgeMk_id]
          exact SSet.Truncated.HomotopyCategory.homMk_id _), by
      exact (SSet.Truncated.HomotopyCategory.homMk_comp_homMk
        sgf.toTruncated).trans (by
          rw [CategoryTheory.nerve.edgeMk_id]
          exact SSet.Truncated.HomotopyCategory.homMk_id _)⟩⟩
  infer_instance

/-- A simplicial map preserves equivalence edges. -/
theorem EdgeIsEquivalence.map {X Y : SSet.{u}} {x y : X _⦋0⦌}
    {e : SSet.Edge x y} (he : EdgeIsEquivalence e) (F : X ⟶ Y) :
    EdgeIsEquivalence (e.map F) := by
  letI : IsIso (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) := he
  change IsIso (SSet.Truncated.HomotopyCategory.homMk
    (e.toTruncated.map ((SSet.truncation 2).map F)))
  rw [← SSet.Truncated.mapHomotopyCategory_homMk]
  exact CategoryTheory.Functor.map_isIso
    (SSet.Truncated.mapHomotopyCategory ((SSet.truncation 2).map F)) _

/-- A composite edge represented by a `2`-simplex is an equivalence when both factors are. -/
theorem EdgeIsEquivalence.comp {X : SSet.{u}}
    {x y z : X _⦋0⦌} {f : SSet.Edge x y} {g : SSet.Edge y z}
    {h : SSet.Edge x z} (s : SSet.Edge.CompStruct f g h)
    (hf : EdgeIsEquivalence f) (hg : EdgeIsEquivalence g) :
    EdgeIsEquivalence h := by
  letI : IsIso (SSet.Truncated.HomotopyCategory.homMk f.toTruncated) := hf
  letI : IsIso (SSet.Truncated.HomotopyCategory.homMk g.toTruncated) := hg
  change IsIso (SSet.Truncated.HomotopyCategory.homMk h.toTruncated)
  rw [← SSet.Truncated.HomotopyCategory.homMk_comp_homMk s.toTruncated]
  infer_instance

/-- A simplicial functor from an ordinary relative category to a quasicategory which sends
every specified weak equivalence to an equivalence edge.

This is inversion data, not an infinity-localization universal property. -/
structure RelativeInfinityFunctor (C : Type u) [Category.{v} C]
    (R : RelativeCategoryData C) (D : SSet.QCat.{max u v}) where
  map : CategoryTheory.nerve C ⟶ D.obj
  map_weakEquivalence : ∀ {X Y : C} (f : X ⟶ Y), R.weakEquivalences f →
    EdgeIsEquivalence ((CategoryTheory.nerve.edgeMk f).map map)

namespace RelativeInfinityFunctor

variable {C : Type u} [Category.{v} C]
variable {R : RelativeCategoryData C} {D : SSet.QCat.{max u v}}

/-- The ordinary functor on homotopy categories induced by relative infinity data. -/
def homotopyFunctor (F : RelativeInfinityFunctor C R D) :
    C ⥤ SSet.hoFunctor.obj D.obj where
  obj X := homotopyObject
    (F.map.app (Opposite.op ⦋0⦌) (CategoryTheory.nerveEquiv.symm X))
  map {X Y} f := edgeHomotopyClass
    ((CategoryTheory.nerve.edgeMk f).map F.map)
  map_id X := by
    rw [CategoryTheory.nerve.edgeMk_id, SSet.Edge.map_id]
    exact SSet.Truncated.HomotopyCategory.homMk_id _
  map_comp {X Y Z} f g := by
    obtain ⟨s⟩ :=
      (CategoryTheory.nerve.nonempty_compStruct_iff f g (f ≫ g)).2 rfl
    exact (SSet.Truncated.HomotopyCategory.homMk_comp_homMk
      (s.map F.map).toTruncated).symm

/-- The induced homotopy-category functor inverts every specified weak equivalence. -/
theorem homotopyFunctor_inverts (F : RelativeInfinityFunctor C R D)
    {X Y : C} (f : X ⟶ Y) (hf : R.weakEquivalences f) :
    IsIso ((homotopyFunctor F).map f) :=
  F.map_weakEquivalence f hf

end RelativeInfinityFunctor

end Infinity
end LeanLCAExactChallenge
