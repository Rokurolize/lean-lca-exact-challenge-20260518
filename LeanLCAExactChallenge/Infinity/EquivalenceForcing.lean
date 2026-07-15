/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.InnerFibrantReplacement
import LeanLCAExactChallenge.Infinity.Localization
import LeanLCAExactChallenge.Infinity.Relative
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# A concrete ordinary-nerve equivalence-forcing presentation

This file freely adjoins an inverse to every chosen weak-equivalence edge and then applies
inner-fibrant replacement. The pushout is a concrete presentation candidate; its full
infinity-categorical universal property is not asserted here.
-/

set_option autoImplicit false

noncomputable section

universe u v

namespace LeanLCAExactChallenge
namespace Infinity

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open Simplicial

/-- Two objects underlying the free-living equivalence. -/
inductive EquivalenceInterval : Type u where
  | zero
  | one

instance equivalenceIntervalCategory : Category.{0} EquivalenceInterval.{u} where
  Hom _ _ := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit

def equivalenceIntervalZero : EquivalenceInterval.{u} :=
  EquivalenceInterval.zero

def equivalenceIntervalOne : EquivalenceInterval.{u} :=
  EquivalenceInterval.one

def equivalenceIntervalForward :
    equivalenceIntervalZero.{u} ⟶ equivalenceIntervalOne.{u} :=
  PUnit.unit

instance equivalenceIntervalForward_isIso :
    IsIso equivalenceIntervalForward.{u} :=
  ⟨⟨PUnit.unit, rfl, rfl⟩⟩

/-- Include the standard `1`-simplex as the forward edge of the free-living equivalence. -/
def equivalenceIntervalInclusion :
    (Δ[1] : SSet.{u}) ⟶ CategoryTheory.nerve EquivalenceInterval.{u} :=
  SSet.yonedaEquiv.symm
    (CategoryTheory.nerve.edgeMk equivalenceIntervalForward.{u}).edge

/-- An edge together with a coherent extension to the free-living equivalence. -/
structure EquivalenceIntervalExtension {Q : SSet.{u}}
    {x y : Q _⦋0⦌} (e : SSet.Edge x y) where
  map : CategoryTheory.nerve EquivalenceInterval.{u} ⟶ Q
  restrict : equivalenceIntervalInclusion.{u} ≫ map =
    SSet.yonedaEquiv.symm e.edge

/-- A specified weak-equivalence arrow of a relative category. -/
structure WeakEquivalenceArrow (C : Type u) [Category.{v} C]
    (R : RelativeCategoryData C) where
  source : C
  target : C
  hom : source ⟶ target
  weak : R.weakEquivalences hom

def SSet.Edge.castEndpoints {X : SSet.{u}}
    {x₀ x₁ y₀ y₁ : X _⦋0⦌}
    (h₀ : x₀ = y₀) (h₁ : x₁ = y₁) (e : SSet.Edge y₀ y₁) :
    SSet.Edge x₀ x₁ := by
  subst y₀
  subst y₁
  exact e

@[simp]
theorem SSet.Edge.castEndpoints_edge {X : SSet.{u}}
    {x₀ x₁ y₀ y₁ : X _⦋0⦌}
    (h₀ : x₀ = y₀) (h₁ : x₁ = y₁) (e : SSet.Edge y₀ y₁) :
    (SSet.Edge.castEndpoints h₀ h₁ e).edge = e.edge := by
  subst y₀
  subst y₁
  rfl

theorem EdgeIsEquivalence.castEndpoints {X : SSet.{u}}
    {x₀ x₁ y₀ y₁ : X _⦋0⦌}
    {e : SSet.Edge y₀ y₁} (he : EdgeIsEquivalence e)
    (h₀ : x₀ = y₀) (h₁ : x₁ = y₁) :
    EdgeIsEquivalence (SSet.Edge.castEndpoints h₀ h₁ e) := by
  subst y₀
  subst y₁
  exact he

/-- A coherently extended edge is an equivalence edge. -/
theorem EquivalenceIntervalExtension.edgeIsEquivalence
    {Q : SSet.{u}} {x y : Q _⦋0⦌} {e : SSet.Edge x y}
    (h : EquivalenceIntervalExtension e) : EdgeIsEquivalence e := by
  let forward := CategoryTheory.nerve.edgeMk equivalenceIntervalForward.{u}
  have hf : EdgeIsEquivalence forward :=
    edgeIsEquivalence_nerve_of_isIso equivalenceIntervalForward
  have hfm : EdgeIsEquivalence (forward.map h.map) := hf.map h.map
  have hedge : (forward.map h.map).edge = e.edge := by
    have hr := congrArg SSet.yonedaEquiv h.restrict
    simpa [forward, equivalenceIntervalInclusion, SSet.yonedaEquiv_comp] using hr
  let ea := forward.map h.map
  have hsrc :
      h.map.app (op ⦋0⦌)
          (CategoryTheory.nerveEquiv.symm equivalenceIntervalZero) = x := by
    calc
      _ = Q.δ 1 ea.edge := ea.src_eq.symm
      _ = Q.δ 1 e.edge := congrArg (Q.δ 1) hedge
      _ = x := e.src_eq
  have htgt :
      h.map.app (op ⦋0⦌)
          (CategoryTheory.nerveEquiv.symm equivalenceIntervalOne) = y := by
    calc
      _ = Q.δ 0 ea.edge := ea.tgt_eq.symm
      _ = Q.δ 0 e.edge := congrArg (Q.δ 0) hedge
      _ = y := e.tgt_eq
  let ea' := SSet.Edge.castEndpoints hsrc.symm htgt.symm ea
  have hea' : EdgeIsEquivalence ea' := hfm.castEndpoints hsrc.symm htgt.symm
  have heq : ea' = e := by
    apply SSet.Edge.ext
    simpa only [ea', SSet.Edge.castEndpoints_edge] using hedge
  simpa only [heq] using hea'

namespace RelativeCategoryData

variable {C : Type u} [Category.{v} C] (R : RelativeCategoryData C)

abbrev weakIntervalFamily (_ : WeakEquivalenceArrow C R) :
    SSet.{max u v} :=
  Δ[1]

abbrev weakEquivalenceFamily (_ : WeakEquivalenceArrow C R) :
    SSet.{max u v} :=
  CategoryTheory.nerve EquivalenceInterval.{max u v}

def weakArrowSimplex (a : WeakEquivalenceArrow C R) :
    (Δ[1] : SSet.{max u v}) ⟶ CategoryTheory.nerve C :=
  SSet.yonedaEquiv.symm (CategoryTheory.nerve.edgeMk a.hom).edge

def weakIntervalsToNerve :
    ∐ weakIntervalFamily R ⟶ CategoryTheory.nerve C :=
  Sigma.desc fun a => weakArrowSimplex R a

def weakIntervalsToEquivalences :
    ∐ weakIntervalFamily R ⟶ ∐ weakEquivalenceFamily R :=
  Sigma.desc fun a =>
    equivalenceIntervalInclusion.{max u v} ≫
      Sigma.ι (weakEquivalenceFamily R) a

/-- The simplicial-set presentation obtained by freely adjoining inverse edges. -/
abbrev equivalenceForcingPresentation : SSet.{max u v} :=
  pushout (weakIntervalsToNerve R) (weakIntervalsToEquivalences R)

/-- The canonical map from the ordinary nerve into the equivalence-forcing presentation. -/
def toEquivalenceForcingPresentation :
    CategoryTheory.nerve C ⟶ equivalenceForcingPresentation R :=
  pushout.inl _ _

/-- The copy of the free-living equivalence attached at a weak arrow. -/
def equivalenceCopy (a : WeakEquivalenceArrow C R) :
    CategoryTheory.nerve EquivalenceInterval.{max u v} ⟶
      equivalenceForcingPresentation R :=
  Sigma.ι (weakEquivalenceFamily R) a ≫
    pushout.inr _ _

@[reassoc]
theorem equivalenceIntervalInclusion_comp_equivalenceCopy
    (a : WeakEquivalenceArrow C R) :
    equivalenceIntervalInclusion.{max u v} ≫ equivalenceCopy R a =
      weakArrowSimplex R a ≫ toEquivalenceForcingPresentation R := by
  let i := Sigma.ι (weakIntervalFamily R) a
  let j := Sigma.ι (weakEquivalenceFamily R) a
  let f := weakIntervalsToNerve R
  let g := weakIntervalsToEquivalences R
  let l := pushout.inl f g
  let r := pushout.inr f g
  have hif : i ≫ f = weakArrowSimplex R a := by
    exact Sigma.ι_desc (fun a => weakArrowSimplex R a) a
  have hig : i ≫ g =
      equivalenceIntervalInclusion.{max u v} ≫ j := by
    exact Sigma.ι_desc
      (fun a => equivalenceIntervalInclusion.{max u v} ≫
        Sigma.ι (weakEquivalenceFamily R) a) a
  have hpush : f ≫ l = g ≫ r := pushout.condition
  change equivalenceIntervalInclusion.{max u v} ≫ (j ≫ r) =
    weakArrowSimplex R a ≫ l
  calc
    _ = (equivalenceIntervalInclusion.{max u v} ≫ j) ≫ r :=
      (Category.assoc _ _ _).symm
    _ = (i ≫ g) ≫ r := congrArg (fun t => t ≫ r) hig.symm
    _ = i ≫ (g ≫ r) := Category.assoc _ _ _
    _ = i ≫ (f ≫ l) := congrArg (fun t => i ≫ t) hpush.symm
    _ = (i ≫ f) ≫ l := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun t => t ≫ l) hif

/-- Every selected weak arrow already has a coherent free-equivalence extension in the
pushout presentation, before inner-fibrant replacement. -/
def toEquivalenceForcingPresentation_weakEquivalenceExtension
    (a : WeakEquivalenceArrow C R) :
    EquivalenceIntervalExtension
      ((CategoryTheory.nerve.edgeMk a.hom).map
        (toEquivalenceForcingPresentation R)) where
  map := equivalenceCopy R a
  restrict := by
    calc
      equivalenceIntervalInclusion.{max u v} ≫ equivalenceCopy R a =
          weakArrowSimplex R a ≫ toEquivalenceForcingPresentation R :=
        equivalenceIntervalInclusion_comp_equivalenceCopy R a
      _ = SSet.yonedaEquiv.symm
          ((CategoryTheory.nerve.edgeMk a.hom).map
            (toEquivalenceForcingPresentation R)).edge := by
        apply SSet.yonedaEquiv.injective
        simp only [weakArrowSimplex, SSet.yonedaEquiv_comp,
          Equiv.apply_symm_apply, SSet.Edge.map_edge]

/-- Every selected weak arrow is an equivalence already in the pushout presentation. -/
theorem toEquivalenceForcingPresentation_weakEquivalence
    (a : WeakEquivalenceArrow C R) :
    EdgeIsEquivalence
      ((CategoryTheory.nerve.edgeMk a.hom).map
        (toEquivalenceForcingPresentation R)) :=
  (toEquivalenceForcingPresentation_weakEquivalenceExtension R a).edgeIsEquivalence

/-- A chosen quasicategory carrier for the equivalence-forcing presentation. -/
def equivalenceForcingQCat : SSet.QCat.{max u v} :=
  innerFibrantReplacementQCat (equivalenceForcingPresentation R)

/-- The inner-anodyne map from the presentation to its quasicategory replacement. -/
def toEquivalenceForcingQCat :
    equivalenceForcingPresentation R ⟶ (equivalenceForcingQCat R).obj :=
  toInnerFibrantReplacement (equivalenceForcingPresentation R)

theorem toEquivalenceForcingQCat_innerAnodyne :
    SSet.innerAnodyneExtensions (toEquivalenceForcingQCat R) :=
  toInnerFibrantReplacement_innerAnodyne (equivalenceForcingPresentation R)

/-- The ordinary nerve map into the chosen quasicategory carrier. -/
def equivalenceForcingMap :
    CategoryTheory.nerve C ⟶ (equivalenceForcingQCat R).obj :=
  toEquivalenceForcingPresentation R ≫
    toEquivalenceForcingQCat R

/-- Every selected weak arrow has a specified coherent free-equivalence extension. -/
def equivalenceForcingMap_weakEquivalenceExtension
    (a : WeakEquivalenceArrow C R) :
    EquivalenceIntervalExtension
      ((CategoryTheory.nerve.edgeMk a.hom).map
        (equivalenceForcingMap R)) where
  map := equivalenceCopy R a ≫ toEquivalenceForcingQCat R
  restrict := by
    let q := toEquivalenceForcingQCat R
    calc
      equivalenceIntervalInclusion.{max u v} ≫
          (equivalenceCopy R a ≫ q) =
        (equivalenceIntervalInclusion.{max u v} ≫
          equivalenceCopy R a) ≫ q := (Category.assoc _ _ _).symm
      _ = (weakArrowSimplex R a ≫
          toEquivalenceForcingPresentation R) ≫ q := congrArg
        (fun t => t ≫ q)
        (equivalenceIntervalInclusion_comp_equivalenceCopy R a)
      _ = weakArrowSimplex R a ≫ equivalenceForcingMap R :=
        Category.assoc _ _ _
      _ = SSet.yonedaEquiv.symm
          ((CategoryTheory.nerve.edgeMk a.hom).map
            (equivalenceForcingMap R)).edge := by
        apply SSet.yonedaEquiv.injective
        simp only [weakArrowSimplex, SSet.yonedaEquiv_comp,
          Equiv.apply_symm_apply, SSet.Edge.map_edge]

theorem equivalenceForcingMap_weakEquivalence
    (a : WeakEquivalenceArrow C R) :
    EdgeIsEquivalence
      ((CategoryTheory.nerve.edgeMk a.hom).map
        (equivalenceForcingMap R)) :=
  (equivalenceForcingMap_weakEquivalenceExtension R a).edgeIsEquivalence

/-- It is enough to check the specified weak arrows in order to invert the complete nerve
marking. -/
theorem invertsMarkedEdges_of_weakEquivalence
    {Q : SSet.{max u v}}
    (F : CategoryTheory.nerve C ⟶ Q)
    (hF : ∀ a : WeakEquivalenceArrow C R,
      EdgeIsEquivalence ((CategoryTheory.nerve.edgeMk a.hom).map F)) :
    InvertsMarkedEdges (relativeNerveEdgeMarking R) F := by
  intro e he
  obtain ⟨X, Y, f, hf, rfl⟩ := he
  let a : WeakEquivalenceArrow C R :=
    { source := X, target := Y, hom := f, weak := hf }
  let eo := (SSet.Edge.mk' (CategoryTheory.nerve.edgeMk f).edge).map F
  let ea := (CategoryTheory.nerve.edgeMk f).map F
  have hea : EdgeIsEquivalence ea := hF a
  have hsrc :
      F.app (op ⦋0⦌)
          ((CategoryTheory.nerve C).δ 1
            (CategoryTheory.nerve.edgeMk f).edge) =
        F.app (op ⦋0⦌) (CategoryTheory.nerveEquiv.symm X) := by
    exact congrArg (fun x => F.app (op ⦋0⦌) x)
      (CategoryTheory.nerve.edgeMk f).src_eq
  have htgt :
      F.app (op ⦋0⦌)
          ((CategoryTheory.nerve C).δ 0
            (CategoryTheory.nerve.edgeMk f).edge) =
        F.app (op ⦋0⦌) (CategoryTheory.nerveEquiv.symm Y) := by
    exact congrArg (fun x => F.app (op ⦋0⦌) x)
      (CategoryTheory.nerve.edgeMk f).tgt_eq
  let ea' := SSet.Edge.castEndpoints hsrc htgt ea
  have hea' : EdgeIsEquivalence ea' := hea.castEndpoints hsrc htgt
  have hedge : eo = ea' := by
    apply SSet.Edge.ext
    simp only [eo, ea', ea, SSet.Edge.castEndpoints_edge,
      SSet.Edge.map_edge, SSet.Edge.mk'_edge]
  rw [show (SSet.Edge.mk' (CategoryTheory.nerve.edgeMk f).edge).map F = eo from rfl,
    hedge]
  exact hea'

/-- The map into the pushout presentation inverts the complete weak-equivalence marking. -/
theorem toEquivalenceForcingPresentation_invertsMarkedEdges :
    InvertsMarkedEdges (relativeNerveEdgeMarking R)
      (toEquivalenceForcingPresentation R) :=
  invertsMarkedEdges_of_weakEquivalence R
    (toEquivalenceForcingPresentation R)
    (toEquivalenceForcingPresentation_weakEquivalence R)

/-- The presentation-level comparison from maps out of the free-equivalence pushout to maps
of the relative nerve that invert every marked edge. -/
def equivalenceForcingPresentationMappingComparison
    (Q : SSet.QCat.{max u v}) :
    (ihom (equivalenceForcingPresentation R)).obj Q.obj ⟶
      (relativeInternalHom (relativeNerveEdgeMarking R) Q.obj : SSet.{max u v}) :=
  internalHomPrecompToRelative
    (relativeNerveEdgeMarking R)
    (toEquivalenceForcingPresentation R) Q.obj
    (toEquivalenceForcingPresentation_invertsMarkedEdges R)

/-- The presentation comparison includes to ordinary internal-Hom precomposition. -/
@[reassoc (attr := simp)]
theorem equivalenceForcingPresentationMappingComparison_comp_inclusion
    (Q : SSet.QCat.{max u v}) :
    equivalenceForcingPresentationMappingComparison R Q ≫
        (relativeInternalHom (relativeNerveEdgeMarking R) Q.obj).ι =
      internalHomPrecomp (toEquivalenceForcingPresentation R) Q.obj :=
  internalHomPrecompToRelative_comp_inclusion _ _ _ _

/-- Mapping out of the free-equivalence pushout is the pullback of the two restriction maps on
simplicial internal Homs. -/
theorem equivalenceForcingPresentationMapping_isPullback
    (Q : SSet.{max u v}) :
    IsPullback
      (internalHomPrecomp
        (pushout.inr (weakIntervalsToNerve R) (weakIntervalsToEquivalences R)) Q)
      (internalHomPrecomp (toEquivalenceForcingPresentation R) Q)
      (internalHomPrecomp (weakIntervalsToEquivalences R) Q)
      (internalHomPrecomp (weakIntervalsToNerve R) Q) := by
  have h := (IsPushout.of_hasPushout
    (weakIntervalsToNerve R) (weakIntervalsToEquivalences R)).op
  have hm := h.map (MonoidalClosed.internalHom.flip.obj Q)
  simpa [internalHomPrecomp, MonoidalClosed.internalHom, Functor.flip,
    toEquivalenceForcingPresentation] using hm

/-- The equivalence-forcing map inverts the complete marking on the ordinary nerve. -/
theorem equivalenceForcingMap_invertsMarkedEdges :
    InvertsMarkedEdges (relativeNerveEdgeMarking R)
      (equivalenceForcingMap R) :=
  invertsMarkedEdges_of_weakEquivalence R (equivalenceForcingMap R)
    (equivalenceForcingMap_weakEquivalence R)

/-- The final equivalence-forcing comparison factors through precomposition along the chosen
inner-fibrant replacement. -/
@[reassoc]
theorem toEquivalenceForcingQCat_precomp_comp_presentationMappingComparison
    (Q : SSet.QCat.{max u v}) :
    internalHomPrecomp (toEquivalenceForcingQCat R) Q.obj ≫
        equivalenceForcingPresentationMappingComparison R Q =
      internalHomPrecompToRelative
        (relativeNerveEdgeMarking R) (equivalenceForcingMap R) Q.obj
        (equivalenceForcingMap_invertsMarkedEdges R) := by
  apply (cancel_mono
    (relativeInternalHom (relativeNerveEdgeMarking R) Q.obj).ι).1
  rw [Category.assoc,
    equivalenceForcingPresentationMappingComparison_comp_inclusion,
    internalHomPrecompToRelative_comp_inclusion,
    internalHomPrecomp_comp]
  rfl

end RelativeCategoryData

end Infinity
end LeanLCAExactChallenge
