/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.EquivalenceForcing
import LeanLCAExactChallenge.Infinity.EquivalenceIntervalExtension
import LeanLCAExactChallenge.Infinity.MarkedRelativeLifting
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products

/-!
# Product decomposition of equivalence-forcing mapping maps

This file records the componentwise part of the decomposition.  Each component of the
restriction map out of the coproduct of free equivalences is the single-interval restricted
map `Map(J,Q) ⟶ EqEdge(Q)`.  No lifting property for the unrestricted map is asserted.
-/

set_option autoImplicit false

noncomputable section

universe u v w

namespace LeanLCAExactChallenge
namespace Infinity

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MorphismProperty

/-- The right lifting property against all monomorphisms is stable under arbitrary products
of maps. -/
theorem piMap_mem_monomorphisms_rlp {J : Type*} {A B : J → SSet.{w}}
    [CategoryTheory.Limits.HasProduct A] [CategoryTheory.Limits.HasProduct B]
    (f : (j : J) → A j ⟶ B j)
    (hf : ∀ j, (monomorphisms SSet.{w}).rlp (f j)) :
    (monomorphisms SSet.{w}).rlp (CategoryTheory.Limits.Pi.map f) := by
  intro K L i hi
  letI (j : J) : CategoryTheory.HasLiftingProperty i (f j) := hf j i hi
  infer_instance

def internalHomCoproductFan {J : Type*} (A : J → SSet.{u})
    [Limits.HasCoproduct A] (Q : SSet.{u}) :
    Limits.Fan (fun j ↦ (ihom (A j)).obj Q) :=
  Limits.Fan.mk ((ihom (∐ A)).obj Q)
    (fun j ↦ internalHomPrecomp (Limits.Sigma.ι A j) Q)

noncomputable def internalHomCoproductFanIsLimit {J : Type*}
    (A : J → SSet.{u}) [Limits.HasCoproduct A] (Q : SSet.{u}) :
    Limits.IsLimit (internalHomCoproductFan A Q) := by
  let c := Limits.Cofan.mk (∐ A) (Limits.Sigma.ι A)
  let h : Limits.IsLimit c.op :=
    Limits.Cofan.IsColimit.op (Limits.coproductIsCoproduct A)
  let F := MonoidalClosed.internalHom.flip.obj Q
  let hm := Limits.isLimitOfPreserves F h
  let hm' := (Limits.Fan.isLimitMapConeEquiv F _ c.op).toFun hm
  refine Limits.IsLimit.ofIsoLimit hm' ?_
  refine Limits.Cone.ext (Iso.refl _) ?_
  rintro ⟨j⟩
  rfl

/-- The canonical comparison from maps out of a coproduct to the product of the mapping
objects of its summands. -/
noncomputable def internalHomCoproductIsoProduct {J : Type*}
    (A : J → SSet.{u}) [Limits.HasCoproduct A] (Q : SSet.{u})
    [Limits.HasProduct fun j ↦ (ihom (A j)).obj Q] :
    (ihom (∐ A)).obj Q ≅ ∏ᶜ fun j ↦ (ihom (A j)).obj Q :=
  (internalHomCoproductFanIsLimit A Q).conePointUniqueUpToIso
    (Limits.productIsProduct fun j ↦ (ihom (A j)).obj Q)

/-- Every projection of the coproduct-to-product comparison is evaluation at the
corresponding coproduct summand. -/
@[reassoc]
theorem internalHomCoproductIsoProduct_hom_π {J : Type*}
    (A : J → SSet.{u}) [Limits.HasCoproduct A] (Q : SSet.{u})
    [Limits.HasProduct fun j ↦ (ihom (A j)).obj Q] (j : J) :
    (internalHomCoproductIsoProduct A Q).hom ≫
        Limits.Pi.π (fun j ↦ (ihom (A j)).obj Q) j =
      internalHomPrecomp (Limits.Sigma.ι A j) Q :=
  Limits.IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

namespace RelativeCategoryData

open CategoryTheory
open CategoryTheory.Limits
open Simplicial

variable {C : Type u} [Category.{v} C] (R : RelativeCategoryData C)

/-- The marking condition in every simplicial degree is imposed vertexwise: an `n`-simplex
belongs to the relative internal hom exactly when each of its vertices represents a map that
inverts every marked edge. -/
theorem mem_relativeInternalHom_iff_vertices_invert
    {X Q : SSet.{max u v}} (W : EdgeMarking X) {U : SimplexCategoryᵒᵖ}
    (s : ((ihom X).obj Q).obj U) :
    s ∈ (relativeInternalHom W Q).obj U ↔
      ∀ i : Fin (U.unop.len + 1),
        InvertsMarkedEdges W
          (internalHomVertexMap X Q
            (((ihom X).obj Q).map (SimplexCategory.const ⦋0⦌ U.unop i).op s)) :=
  mem_fullSubcomplexOnVertices_iff _ _ _

/-- The explicit family condition on a simplex of the mapping object from the ordinary
nerve: at every vertex, every specified weak arrow is sent to an equivalence edge. -/
def WeakArrowFamilyEquivalenceCondition (Q : SSet.{max u v})
    {U : SimplexCategoryᵒᵖ}
    (s : ((ihom (CategoryTheory.nerve C)).obj Q).obj U) : Prop :=
  ∀ i : Fin (U.unop.len + 1), ∀ a : WeakEquivalenceArrow C R,
    EdgeIsEquivalence
      ((SSet.Edge.mk' (CategoryTheory.nerve.edgeMk a.hom).edge).map
        (internalHomVertexMap (CategoryTheory.nerve C) Q
          (((ihom (CategoryTheory.nerve C)).obj Q).map
            (SimplexCategory.const ⦋0⦌ U.unop i).op s)))

/-- The relative mapping subcomplex condition is exactly the conjunction of the
weak-arrow-by-weak-arrow equivalence conditions in every vertex. -/
theorem mem_relativeInternalHom_iff_weakArrowFamily
    (Q : SSet.{max u v}) {U : SimplexCategoryᵒᵖ}
    (s : ((ihom (CategoryTheory.nerve C)).obj Q).obj U) :
    s ∈ ((relativeInternalHom (relativeNerveEdgeMarking R) Q :
      ((ihom (CategoryTheory.nerve C)).obj Q).Subcomplex).obj U) ↔
      WeakArrowFamilyEquivalenceCondition R Q s := by
  change (∀ i : Fin (U.unop.len + 1),
    InvertsMarkedEdges (relativeNerveEdgeMarking R)
      (internalHomVertexMap (CategoryTheory.nerve C) Q
        (((ihom (CategoryTheory.nerve C)).obj Q).map
          (SimplexCategory.const ⦋0⦌ U.unop i).op s))) ↔ _
  constructor
  · intro h i a
    exact h i _ ⟨a.source, a.target, a.hom, a.weak, rfl⟩
  · intro h i e he
    obtain ⟨X, Y, f, hf, rfl⟩ := he
    exact h i ⟨X, Y, f, hf⟩

/-- Evaluation of maps out of the coproduct of free equivalences at one weak arrow. -/
def weakEquivalenceMappingComponent (Q : SSet.{max u v})
    (a : WeakEquivalenceArrow C R) :
    (ihom (∐ weakEquivalenceFamily R)).obj Q ⟶
      (ihom (CategoryTheory.nerve EquivalenceInterval.{max u v})).obj Q :=
  internalHomPrecomp (Sigma.ι (weakEquivalenceFamily R) a) Q

/-- Evaluation of maps out of the coproduct of intervals at one weak arrow. -/
def weakIntervalMappingComponent (Q : SSet.{max u v})
    (a : WeakEquivalenceArrow C R) :
    (ihom (∐ weakIntervalFamily R)).obj Q ⟶ (ihom (Δ[1] : SSet.{max u v})).obj Q :=
  internalHomPrecomp (Sigma.ι (weakIntervalFamily R) a) Q

theorem weakArrowSimplex_comp_edge
    (Q : SSet.{max u v}) (a : WeakEquivalenceArrow C R)
    (F : CategoryTheory.nerve C ⟶ Q) :
    SSet.yonedaEquiv (weakArrowSimplex R a ≫ F) =
      ((SSet.Edge.mk' (CategoryTheory.nerve.edgeMk a.hom).edge).map F).edge := by
  change F.app _ (SSet.yonedaEquiv (weakArrowSimplex R a)) = _
  simp only [weakArrowSimplex, Equiv.apply_symm_apply, SSet.Edge.map_edge,
    SSet.Edge.mk'_edge]

private theorem edgeIsEquivalence_iff_of_edge_eq {X : SSet.{w}}
    {x₀ x₁ y₀ y₁ : X _⦋0⦌} (e : SSet.Edge x₀ x₁) (f : SSet.Edge y₀ y₁)
    (h : e.edge = f.edge) : EdgeIsEquivalence e ↔ EdgeIsEquivalence f := by
  constructor
  · intro he
    let e' := SSet.Edge.castEndpoints
      (f.src_eq.symm.trans (h ▸ e.src_eq)) (f.tgt_eq.symm.trans (h ▸ e.tgt_eq)) e
    have he' : EdgeIsEquivalence e' := he.castEndpoints
      (f.src_eq.symm.trans (h ▸ e.src_eq)) (f.tgt_eq.symm.trans (h ▸ e.tgt_eq))
    have hef : e' = f := by
      apply SSet.Edge.ext
      simp only [e', SSet.Edge.castEndpoints_edge, h]
    simpa only [hef] using he'
  · intro hf
    let f' := SSet.Edge.castEndpoints
      (e.src_eq.symm.trans (h.symm ▸ f.src_eq))
      (e.tgt_eq.symm.trans (h.symm ▸ f.tgt_eq)) f
    have hf' : EdgeIsEquivalence f' := hf.castEndpoints
      (e.src_eq.symm.trans (h.symm ▸ f.src_eq))
      (e.tgt_eq.symm.trans (h.symm ▸ f.tgt_eq))
    have hfe : f' = e := by
      apply SSet.Edge.ext
      simp only [f', SSet.Edge.castEndpoints_edge, h]
    simpa only [hfe] using hf'

/-- Evaluation at a weak-arrow component commutes with taking a vertex of an internal-hom
simplex. -/
theorem weakEquivalenceMappingComponent_vertexMap
    (Q : SSet.{max u v}) {U : SimplexCategoryᵒᵖ}
    (s : ((ihom (CategoryTheory.nerve C)).obj Q).obj U)
    (i : Fin (U.unop.len + 1)) (a : WeakEquivalenceArrow C R) :
    internalHomVertexMap (Δ[1] : SSet.{max u v}) Q
        (((ihom (Δ[1] : SSet.{max u v})).obj Q).map
          (SimplexCategory.const ⦋0⦌ U.unop i).op
          ((internalHomPrecomp (weakArrowSimplex R a) Q).app U s)) =
      weakArrowSimplex R a ≫
        internalHomVertexMap (CategoryTheory.nerve C) Q
          (((ihom (CategoryTheory.nerve C)).obj Q).map
            (SimplexCategory.const ⦋0⦌ U.unop i).op s) := by
  rw [← NatTrans.naturality_apply (internalHomPrecomp (weakArrowSimplex R a) Q)
    (SimplexCategory.const ⦋0⦌ U.unop i).op s]
  exact internalHomVertexMap_precomp (weakArrowSimplex R a) _

/-- A componentwise evaluation simplex lies in the equivalence-edge internal hom exactly
when the corresponding weak arrow satisfies the family condition at every vertex. -/
theorem weakEquivalenceMappingComponent_mem_equivalenceEdgeInternalHom_iff
    (Q : SSet.{max u v}) {U : SimplexCategoryᵒᵖ}
    (s : ((ihom (CategoryTheory.nerve C)).obj Q).obj U)
    (a : WeakEquivalenceArrow C R) :
    (internalHomPrecomp (weakArrowSimplex R a) Q).app U s ∈
        (equivalenceEdgeInternalHom Q).obj U ↔
      ∀ i : Fin (U.unop.len + 1),
        EdgeIsEquivalence
          ((SSet.Edge.mk' (CategoryTheory.nerve.edgeMk a.hom).edge).map
            (internalHomVertexMap (CategoryTheory.nerve C) Q
              (((ihom (CategoryTheory.nerve C)).obj Q).map
                (SimplexCategory.const ⦋0⦌ U.unop i).op s))) := by
  change (∀ i : Fin (U.unop.len + 1), EdgeIsEquivalence
    (SSet.Edge.mk' (SSet.yonedaEquiv
      (internalHomVertexMap (Δ[1] : SSet.{max u v}) Q
        (((ihom (Δ[1] : SSet.{max u v})).obj Q).map
          (SimplexCategory.const ⦋0⦌ U.unop i).op
          ((internalHomPrecomp (weakArrowSimplex R a) Q).app U s)))))) ↔ _
  apply forall_congr'
  intro i
  rw [weakEquivalenceMappingComponent_vertexMap R Q s i a]
  change EdgeIsEquivalence
    (SSet.Edge.mk' (SSet.yonedaEquiv
      (weakArrowSimplex R a ≫ _))) ↔ _
  rw [weakArrowSimplex_comp_edge R Q a]
  apply edgeIsEquivalence_iff_of_edge_eq (X := Q)
  simp only [SSet.Edge.mk'_edge]

/-- Simultaneous restriction of a map out of the ordinary nerve to every specified weak
arrow. -/
noncomputable def weakArrowEvaluationFamily (Q : SSet.{max u v}) :
    (ihom (CategoryTheory.nerve C)).obj Q ⟶
      ∏ᶜ fun _ : WeakEquivalenceArrow C R ↦ (ihom (Δ[1] : SSet.{max u v})).obj Q :=
  Limits.Pi.lift fun a ↦ internalHomPrecomp (weakArrowSimplex R a) Q

@[reassoc]
theorem weakArrowEvaluationFamily_π (Q : SSet.{max u v})
    (a : WeakEquivalenceArrow C R) :
    weakArrowEvaluationFamily R Q ≫
        Limits.Pi.π (fun _ : WeakEquivalenceArrow C R ↦
          (ihom (Δ[1] : SSet.{max u v})).obj Q) a =
      internalHomPrecomp (weakArrowSimplex R a) Q := by
  exact Limits.Pi.lift_π _ _

set_option maxHeartbeats 800000 in
-- Elaborating the full-subcomplex membership equivalence unfolds two internal homs.
theorem weakArrowEvaluationComponent_mem
    (Q : SSet.{max u v}) (a : WeakEquivalenceArrow C R)
    {U : SimplexCategoryᵒᵖ}
    (s : (relativeInternalHom (relativeNerveEdgeMarking R) Q : SSet.{max u v}).obj U) :
    (((relativeInternalHom (relativeNerveEdgeMarking R) Q).ι ≫
      internalHomPrecomp (weakArrowSimplex R a) Q).app U s) ∈
        (equivalenceEdgeInternalHom Q).obj U := by
  obtain ⟨s, hs⟩ := s
  have hfamily : WeakArrowFamilyEquivalenceCondition R Q s :=
    (mem_relativeInternalHom_iff_weakArrowFamily R Q s).1 hs
  apply (weakEquivalenceMappingComponent_mem_equivalenceEdgeInternalHom_iff R Q s a).2
  intro i
  exact hfamily i a

/-- Evaluation at one weak arrow, retaining the proof that the evaluated edge is an
equivalence. -/
noncomputable def weakArrowEvaluationComponentToEquivalenceEdges
    (Q : SSet.{max u v}) (a : WeakEquivalenceArrow C R) :
    (relativeInternalHom (relativeNerveEdgeMarking R) Q : SSet.{max u v}) ⟶
      (equivalenceEdgeInternalHom Q : SSet.{max u v}) :=
  SSet.Subcomplex.lift
    ((relativeInternalHom (relativeNerveEdgeMarking R) Q).ι ≫
      internalHomPrecomp (weakArrowSimplex R a) Q) (by
        rintro U _ ⟨s, rfl⟩
        exact weakArrowEvaluationComponent_mem R Q a s)

/-- Simultaneous weak-arrow evaluation, retaining the proof that every evaluated edge is an
equivalence. -/
noncomputable def weakArrowEvaluationToEquivalenceEdges (Q : SSet.{max u v}) :
    (relativeInternalHom (relativeNerveEdgeMarking R) Q : SSet.{max u v}) ⟶
      ∏ᶜ fun _ : WeakEquivalenceArrow C R ↦
        (equivalenceEdgeInternalHom Q : SSet.{max u v}) :=
  Limits.Pi.lift fun a ↦ weakArrowEvaluationComponentToEquivalenceEdges R Q a

@[reassoc]
theorem weakArrowEvaluationToEquivalenceEdges_π_comp_inclusion
    (Q : SSet.{max u v}) (a : WeakEquivalenceArrow C R) :
    weakArrowEvaluationToEquivalenceEdges R Q ≫
        Limits.Pi.π (fun _ : WeakEquivalenceArrow C R ↦
          (equivalenceEdgeInternalHom Q : SSet.{max u v})) a ≫
        (equivalenceEdgeInternalHom Q).ι =
      (relativeInternalHom (relativeNerveEdgeMarking R) Q).ι ≫
        internalHomPrecomp (weakArrowSimplex R a) Q := by
  rw [weakArrowEvaluationToEquivalenceEdges, ← Category.assoc, Limits.Pi.lift_π]
  exact SSet.Subcomplex.lift_ι _ _

/-- Product of the inclusions of the equivalence-edge subcomplexes. -/
noncomputable def equivalenceEdgeFamilyInclusion (Q : SSet.{max u v}) :
    (∏ᶜ fun _ : WeakEquivalenceArrow C R ↦
      (equivalenceEdgeInternalHom Q : SSet.{max u v})) ⟶
    (∏ᶜ fun _ : WeakEquivalenceArrow C R ↦
      (ihom (Δ[1] : SSet.{max u v})).obj Q) :=
  Limits.Pi.map fun _ ↦ (equivalenceEdgeInternalHom Q).ι

/-- The relative internal hom is precisely the inverse image of the product of
equivalence-edge subcomplexes under simultaneous weak-arrow evaluation. -/
theorem weakArrowEvaluation_isPullback (Q : SSet.{max u v}) :
    IsPullback
      (weakArrowEvaluationToEquivalenceEdges R Q)
      (relativeInternalHom (relativeNerveEdgeMarking R) Q).ι
      (equivalenceEdgeFamilyInclusion R Q)
      (weakArrowEvaluationFamily R Q) := by
  have hcomm : weakArrowEvaluationToEquivalenceEdges R Q ≫
        equivalenceEdgeFamilyInclusion R Q =
      (relativeInternalHom (relativeNerveEdgeMarking R) Q).ι ≫
        weakArrowEvaluationFamily R Q := by
    apply Limits.Pi.hom_ext
    intro a
    rw [Category.assoc, equivalenceEdgeFamilyInclusion, Limits.Pi.map_π,
      weakArrowEvaluationToEquivalenceEdges_π_comp_inclusion,
      Category.assoc, weakArrowEvaluationFamily_π]
  refine ⟨⟨hcomm⟩, ⟨PullbackCone.IsLimit.mk hcomm ?_ ?_ ?_ ?_⟩⟩
  · intro s
    exact SSet.Subcomplex.lift s.snd (by
      rintro U _ ⟨x, rfl⟩
      apply (mem_relativeInternalHom_iff_weakArrowFamily R Q _).2
      intro i a
      apply (weakEquivalenceMappingComponent_mem_equivalenceEdgeInternalHom_iff
        R Q (s.snd.app U x) a).1
      let y := (Limits.Pi.π (fun _ : WeakEquivalenceArrow C R ↦
        (equivalenceEdgeInternalHom Q : SSet.{max u v})) a).app U (s.fst.app U x)
      have hc := congrArg
        (fun k ↦ k.app U x)
        (congrArg (fun k ↦ k ≫ Limits.Pi.π
          (fun _ : WeakEquivalenceArrow C R ↦
            (ihom (Δ[1] : SSet.{max u v})).obj Q) a) s.condition)
      have hy : y.1 = (internalHomPrecomp (weakArrowSimplex R a) Q).app U
          (s.snd.app U x) := by
        simp only [Category.assoc, equivalenceEdgeFamilyInclusion, Limits.Pi.map_π,
          weakArrowEvaluationFamily_π, NatTrans.comp_app,
          ConcreteCategory.comp_apply] at hc
        change y.1 = _ at hc
        exact hc
      rw [← hy]
      exact y.2)
  · intro s
    apply Limits.Pi.hom_ext
    intro a
    apply (cancel_mono (equivalenceEdgeInternalHom Q).ι).1
    rw [Category.assoc, Category.assoc,
      weakArrowEvaluationToEquivalenceEdges_π_comp_inclusion,
      SSet.Subcomplex.lift_ι_assoc, ← weakArrowEvaluationFamily_π]
    have hc := congrArg (fun k ↦ k ≫ Limits.Pi.π
      (fun _ : WeakEquivalenceArrow C R ↦
        (ihom (Δ[1] : SSet.{max u v})).obj Q) a) s.condition
    simpa only [Category.assoc, equivalenceEdgeFamilyInclusion, Limits.Pi.map_π] using hc.symm
  · intro s
    exact SSet.Subcomplex.lift_ι _ _
  · intro s m _ hm
    apply (cancel_mono
      (relativeInternalHom (relativeNerveEdgeMarking R) Q).ι).1
    rw [hm, SSet.Subcomplex.lift_ι]

/-- On every coproduct component, restriction along the family of interval inclusions is
exactly restriction along the single free-equivalence interval. -/
theorem weakEquivalenceMappingComponent_restriction
    (Q : SSet.{max u v}) (a : WeakEquivalenceArrow C R) :
    internalHomPrecomp (weakIntervalsToEquivalences R) Q ≫
        weakIntervalMappingComponent R Q a =
      weakEquivalenceMappingComponent R Q a ≫
        internalHomPrecomp equivalenceIntervalInclusion Q := by
  rw [weakEquivalenceMappingComponent, weakIntervalMappingComponent,
    internalHomPrecomp_comp, internalHomPrecomp_comp]
  congr 1
  exact Sigma.ι_desc (fun a ↦ equivalenceIntervalInclusion ≫
    Sigma.ι (weakEquivalenceFamily R) a) a

/-- The preceding component factors through the equivalence-edge subcomplex by the genuine
single-interval restricted map. -/
theorem weakEquivalenceMappingComponent_restriction_to_equivalenceEdges
    (Q : SSet.{max u v}) (a : WeakEquivalenceArrow C R) :
    weakEquivalenceMappingComponent R Q a ≫
        equivalenceIntervalRestrictionToEquivalenceEdges Q ≫
          (equivalenceEdgeInternalHom Q).ι =
      internalHomPrecomp (weakIntervalsToEquivalences R) Q ≫
        weakIntervalMappingComponent R Q a := by
  simpa only [Category.assoc,
    equivalenceIntervalRestrictionToEquivalenceEdges_comp_inclusion] using
      (weakEquivalenceMappingComponent_restriction R Q a).symm

/-- Under the two coproduct-to-product comparisons, restriction along the family of free
equivalence inclusions is the product of the single-interval restriction maps. -/
theorem weakIntervalsMappingRestriction_productComparison
    (Q : SSet.{max u v}) :
    (internalHomCoproductIsoProduct (weakEquivalenceFamily R) Q).hom ≫
        Limits.Pi.map (fun _ : WeakEquivalenceArrow C R ↦
          internalHomPrecomp equivalenceIntervalInclusion Q) =
      internalHomPrecomp (weakIntervalsToEquivalences R) Q ≫
        (internalHomCoproductIsoProduct (weakIntervalFamily R) Q).hom := by
  apply Limits.Pi.hom_ext
  intro a
  simp only [Limits.Pi.map_π, Category.assoc,
    internalHomCoproductIsoProduct_hom_π_assoc,
    internalHomCoproductIsoProduct_hom_π]
  exact (weakEquivalenceMappingComponent_restriction R Q a).symm

theorem weakIntervalsToNerveMapping_productComparison
    (Q : SSet.{max u v}) :
    internalHomPrecomp (weakIntervalsToNerve R) Q ≫
        (internalHomCoproductIsoProduct (weakIntervalFamily R) Q).hom =
      weakArrowEvaluationFamily R Q := by
  apply Limits.Pi.hom_ext
  intro a
  rw [Category.assoc, internalHomCoproductIsoProduct_hom_π,
    internalHomPrecomp_comp, weakArrowEvaluationFamily_π]
  congr 1
  exact Sigma.ι_desc (fun a ↦ weakArrowSimplex R a) a

/-- Restriction from a product of free-equivalence mapping objects to the product of
equivalence-edge mapping objects. -/
noncomputable def equivalenceIntervalFamilyRestriction (Q : SSet.{max u v}) :
    (∏ᶜ fun _ : WeakEquivalenceArrow C R ↦
      (ihom (CategoryTheory.nerve EquivalenceInterval.{max u v})).obj Q) ⟶
    (∏ᶜ fun _ : WeakEquivalenceArrow C R ↦
      (equivalenceEdgeInternalHom Q : SSet.{max u v})) :=
  Limits.Pi.map fun _ ↦ equivalenceIntervalRestrictionToEquivalenceEdges Q

theorem equivalenceIntervalFamilyRestriction_comp_inclusion
    (Q : SSet.{max u v}) :
    equivalenceIntervalFamilyRestriction R Q ≫ equivalenceEdgeFamilyInclusion R Q =
      Limits.Pi.map (fun _ : WeakEquivalenceArrow C R ↦
        internalHomPrecomp equivalenceIntervalInclusion Q) := by
  apply Limits.Pi.hom_ext
  intro a
  simp [equivalenceIntervalFamilyRestriction, equivalenceEdgeFamilyInclusion]

/-- The presentation mapping object, identified with the standard pullback of the two family
restriction maps. -/
noncomputable def equivalenceForcingPresentationMappingPullbackIso
    (Q : SSet.{max u v}) :
    (ihom (equivalenceForcingPresentation R)).obj Q ≅
      pullback
        (internalHomPrecomp (weakIntervalsToEquivalences R) Q)
        (internalHomPrecomp (weakIntervalsToNerve R) Q) :=
  (equivalenceForcingPresentationMapping_isPullback R Q).isoPullback

/-- Under the standard pullback identification, the second projection is precomposition by
the map from the ordinary nerve to the equivalence-forcing presentation. -/
@[reassoc]
theorem equivalenceForcingPresentationMappingPullbackIso_hom_snd
    (Q : SSet.{max u v}) :
    (equivalenceForcingPresentationMappingPullbackIso R Q).hom ≫
        pullback.snd
          (internalHomPrecomp (weakIntervalsToEquivalences R) Q)
          (internalHomPrecomp (weakIntervalsToNerve R) Q) =
      internalHomPrecomp (toEquivalenceForcingPresentation R) Q :=
  (equivalenceForcingPresentationMapping_isPullback R Q).isoPullback_hom_snd

/-- Consequently, after forgetting the equivalence-edge witnesses, the genuine presentation
comparison is exactly the second projection of this pullback. -/
@[reassoc]
theorem equivalenceForcingPresentationMappingPullbackIso_hom_snd_eq_comparison
    (Q : SSet.QCat.{max u v}) :
    (equivalenceForcingPresentationMappingPullbackIso R Q.obj).hom ≫
        pullback.snd
          (internalHomPrecomp (weakIntervalsToEquivalences R) Q.obj)
          (internalHomPrecomp (weakIntervalsToNerve R) Q.obj) =
      equivalenceForcingPresentationMappingComparison R Q ≫
        (relativeInternalHom (relativeNerveEdgeMarking R) Q.obj).ι := by
  rw [equivalenceForcingPresentationMappingPullbackIso_hom_snd,
    equivalenceForcingPresentationMappingComparison_comp_inclusion]

noncomputable def equivalenceForcingPresentationToEquivalenceFamily
    (Q : SSet.{max u v}) :
    (ihom (equivalenceForcingPresentation R)).obj Q ⟶
      ∏ᶜ fun _ : WeakEquivalenceArrow C R ↦
        (ihom (CategoryTheory.nerve EquivalenceInterval.{max u v})).obj Q :=
  internalHomPrecomp
      (pushout.inr (weakIntervalsToNerve R) (weakIntervalsToEquivalences R)) Q ≫
    (internalHomCoproductIsoProduct (weakEquivalenceFamily R) Q).hom

theorem equivalenceForcingPresentationMappingComparison_isPullback
    (Q : SSet.QCat.{max u v}) :
    IsPullback
      (equivalenceForcingPresentationToEquivalenceFamily R Q.obj)
      (equivalenceForcingPresentationMappingComparison R Q)
      (equivalenceIntervalFamilyRestriction R Q.obj)
      (weakArrowEvaluationToEquivalenceEdges R Q.obj) := by
  have hiso : IsPullback
      (internalHomCoproductIsoProduct (weakEquivalenceFamily R) Q.obj).hom
      (internalHomPrecomp (weakIntervalsToEquivalences R) Q.obj)
      (Limits.Pi.map (fun _ : WeakEquivalenceArrow C R ↦
        internalHomPrecomp equivalenceIntervalInclusion Q.obj))
      (internalHomCoproductIsoProduct (weakIntervalFamily R) Q.obj).hom :=
    IsPullback.of_horiz_isIso
      ⟨weakIntervalsMappingRestriction_productComparison R Q.obj⟩
  have hraw := (equivalenceForcingPresentationMapping_isPullback R Q.obj).paste_horiz hiso
  have hcomposite : IsPullback
      (equivalenceForcingPresentationToEquivalenceFamily R Q.obj)
      (equivalenceForcingPresentationMappingComparison R Q ≫
        (relativeInternalHom (relativeNerveEdgeMarking R) Q.obj).ι)
      (equivalenceIntervalFamilyRestriction R Q.obj ≫
        equivalenceEdgeFamilyInclusion R Q.obj)
      (weakArrowEvaluationFamily R Q.obj) := by
    simpa only [equivalenceForcingPresentationToEquivalenceFamily,
      equivalenceForcingPresentationMappingComparison_comp_inclusion,
      equivalenceIntervalFamilyRestriction_comp_inclusion,
      weakIntervalsToNerveMapping_productComparison] using hraw
  have hdesired : equivalenceForcingPresentationToEquivalenceFamily R Q.obj ≫
        equivalenceIntervalFamilyRestriction R Q.obj =
      equivalenceForcingPresentationMappingComparison R Q ≫
        weakArrowEvaluationToEquivalenceEdges R Q.obj := by
    apply Limits.Pi.hom_ext
    intro a
    apply (cancel_mono (equivalenceEdgeInternalHom Q.obj).ι).1
    have hc := congrArg (fun k ↦ k ≫ Limits.Pi.π
      (fun _ : WeakEquivalenceArrow C R ↦
        (ihom (Δ[1] : SSet.{max u v})).obj Q.obj) a) hcomposite.w
    simp only [Category.assoc, weakArrowEvaluationFamily_π] at hc
    simpa only [Category.assoc, equivalenceEdgeFamilyInclusion, Limits.Pi.map_π,
      weakArrowEvaluationToEquivalenceEdges_π_comp_inclusion] using hc
  exact hcomposite.of_bot hdesired (weakArrowEvaluation_isPullback R Q.obj)

/-- Componentwise free-equivalence extension implies the required mono-RLP for the complete
equivalence-forcing presentation comparison. -/
theorem equivalenceForcingPresentationMappingComparison_mem_monomorphisms_rlp
    (Q : SSet.QCat.{max u v})
    (h : ∀ _ : WeakEquivalenceArrow C R,
      (monomorphisms SSet.{max u v}).rlp
        (equivalenceIntervalRestrictionToEquivalenceEdges Q.obj :
          (ihom (CategoryTheory.nerve EquivalenceInterval.{max u v})).obj Q.obj ⟶
            (equivalenceEdgeInternalHom Q.obj : SSet.{max u v}))) :
    (monomorphisms SSet.{max u v}).rlp
      (equivalenceForcingPresentationMappingComparison R Q) := by
  have hpi : (monomorphisms SSet.{max u v}).rlp
      (equivalenceIntervalFamilyRestriction R Q.obj) := by
    exact piMap_mem_monomorphisms_rlp
      (A := fun _ : WeakEquivalenceArrow C R ↦
        (ihom (CategoryTheory.nerve EquivalenceInterval.{max u v})).obj Q.obj)
      (B := fun _ : WeakEquivalenceArrow C R ↦
        (equivalenceEdgeInternalHom Q.obj : SSet.{max u v}))
      (fun _ : WeakEquivalenceArrow C R ↦
        (equivalenceIntervalRestrictionToEquivalenceEdges Q.obj :
          (ihom (CategoryTheory.nerve EquivalenceInterval.{max u v})).obj Q.obj ⟶
            (equivalenceEdgeInternalHom Q.obj : SSet.{max u v}))) h
  intro K L j hj
  letI : HasLiftingProperty j (equivalenceIntervalFamilyRestriction R Q.obj) := hpi j hj
  exact (equivalenceForcingPresentationMappingComparison_isPullback R Q).hasLiftingProperty j

end RelativeCategoryData
end Infinity
end LeanLCAExactChallenge
