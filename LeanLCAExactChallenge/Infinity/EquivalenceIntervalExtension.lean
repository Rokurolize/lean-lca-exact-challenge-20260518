/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.EquivalenceForcing
import Mathlib.AlgebraicTopology.Quasicategory.TwoTruncated
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
# Coherent extensions of equivalence edges

`EquivalenceForcing.lean` packages extensions of an edge along the inclusion of the standard
`1`-simplex into the nerve of the free-living equivalence and proves that an extension forces
the edge to be an equivalence. This file reformulates the vertex-level converse as a precise
surjectivity statement on maps. It also constructs the extension for an actual isomorphism in
an ordinary nerve, compares the two available homotopy-category presentations, extracts an
actual inverse edge with inverse triangles, and proves the two-dimensional special left and
right outer-horn fillers.

No converse for arbitrary quasicategories is asserted, and vertex-level surjectivity would not
by itself prove the required equivalence of mapping quasicategories. The pinned API supplies
inner-horn fillers, but not the all-dimensional parameterized outer-horn equivalence theorem
or the coherent free-living equivalence extension theorem needed for that converse.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge
namespace Infinity

open CategoryTheory
open Opposite
open Simplicial

/-- Restrict a coherent free-living equivalence to its distinguished forward edge. -/
def equivalenceIntervalRestriction {Q : SSet.{u}}
    (F : CategoryTheory.nerve EquivalenceInterval.{u} ⟶ Q) : Q _⦋1⦌ :=
  ((CategoryTheory.nerve.edgeMk equivalenceIntervalForward).map F).edge

/-- The distinguished edge of a coherent free-living equivalence is an equivalence. -/
theorem equivalenceIntervalRestriction_isEquivalence {Q : SSet.{u}}
    (F : CategoryTheory.nerve EquivalenceInterval.{u} ⟶ Q) :
    EdgeIsEquivalence (SSet.Edge.mk' (equivalenceIntervalRestriction F)) := by
  let ea := (CategoryTheory.nerve.edgeMk equivalenceIntervalForward).map F
  have hea : EdgeIsEquivalence ea :=
    (edgeIsEquivalence_nerve_of_isIso equivalenceIntervalForward).map F
  change EdgeIsEquivalence (SSet.Edge.mk' ea.edge)
  let ea' := SSet.Edge.castEndpoints ea.src_eq ea.tgt_eq ea
  have hea' : EdgeIsEquivalence ea' := hea.castEndpoints ea.src_eq ea.tgt_eq
  have heq : ea' = SSet.Edge.mk' ea.edge := by
    apply SSet.Edge.ext
    simp only [ea', SSet.Edge.castEndpoints_edge, SSet.Edge.mk'_edge]
  simpa only [heq] using hea'

/-- The subtype of `1`-simplices whose associated edge is an equivalence. -/
def EquivalenceOneSimplex (Q : SSet.{u}) :=
  {s : Q _⦋1⦌ // EdgeIsEquivalence (SSet.Edge.mk' s)}

/-- The full internal-hom subcomplex spanned by maps whose represented
`1`-simplex is an equivalence edge. -/
def equivalenceEdgeInternalHom (Q : SSet.{u}) :
    ((ihom (Δ[1] : SSet.{u})).obj Q).Subcomplex :=
  fullSubcomplexOnVertices ((ihom (Δ[1] : SSet.{u})).obj Q) fun v ↦
    EdgeIsEquivalence
      (SSet.Edge.mk' (SSet.yonedaEquiv
        (internalHomVertexMap (Δ[1] : SSet.{u}) Q v)))

/-- The equivalence-edge internal hom is a quasicategory whenever the target is. -/
theorem equivalenceEdgeInternalHom_quasicategory
    (Q : SSet.{u}) [SSet.Quasicategory Q] :
    SSet.Quasicategory (equivalenceEdgeInternalHom Q : SSet.{u}) := by
  letI : SSet.Quasicategory ((ihom (Δ[1] : SSet.{u})).obj Q) := quasicategory_ihom
  exact fullSubcomplexOnVertices_quasicategory _ _

/-- Restrict a coherent free-living equivalence to its forward edge, with the
fact that every vertex lands in the equivalence-edge full subcomplex retained. -/
def equivalenceIntervalRestrictionToEquivalenceEdges (Q : SSet.{u}) :
    (ihom (CategoryTheory.nerve EquivalenceInterval.{u})).obj Q ⟶
      (equivalenceEdgeInternalHom Q : SSet.{u}) :=
  SSet.Subcomplex.lift
    (internalHomPrecomp equivalenceIntervalInclusion Q) (by
      rintro U _ ⟨s, rfl⟩ i
      rw [← NatTrans.naturality_apply
        (internalHomPrecomp equivalenceIntervalInclusion Q)
        (SimplexCategory.const ⦋0⦌ U.unop i).op s]
      rw [internalHomVertexMap_precomp]
      let F := internalHomVertexMap
        (CategoryTheory.nerve EquivalenceInterval.{u}) Q
        (((ihom (CategoryTheory.nerve EquivalenceInterval.{u})).obj Q).map
          (SimplexCategory.const ⦋0⦌ U.unop i).op s)
      change EdgeIsEquivalence
        (SSet.Edge.mk' (SSet.yonedaEquiv (equivalenceIntervalInclusion ≫ F)))
      have hF := equivalenceIntervalRestriction_isEquivalence F
      have hedge : SSet.yonedaEquiv (equivalenceIntervalInclusion ≫ F) =
          equivalenceIntervalRestriction F := by
        change F.app _ (SSet.yonedaEquiv equivalenceIntervalInclusion) =
          ((CategoryTheory.nerve.edgeMk equivalenceIntervalForward).map F).edge
        rw [equivalenceIntervalInclusion]
        simp only [Equiv.apply_symm_apply]
        rfl
      rw [hedge]
      exact hF)

/-- Forgetting the equivalence-edge witness recovers ordinary precomposition. -/
@[reassoc (attr := simp)]
theorem equivalenceIntervalRestrictionToEquivalenceEdges_comp_inclusion
    (Q : SSet.{u}) :
    equivalenceIntervalRestrictionToEquivalenceEdges Q ≫
        (equivalenceEdgeInternalHom Q).ι =
      internalHomPrecomp equivalenceIntervalInclusion Q :=
  SSet.Subcomplex.lift_ι _ _

/-- The distinguished `0 → 1` edge of a left outer `2`-horn. -/
def leftOuterHorn₂FirstEdge {Q : SSet.{u}} (h : (Λ[2, 0] : SSet.{u}) ⟶ Q) :
    Q _⦋1⦌ :=
  SSet.yonedaEquiv (SSet.horn₂₀.ι₀₁ ≫ h)

/-- The `0 → 2` edge of a left outer `2`-horn. -/
def leftOuterHorn₂LongEdge {Q : SSet.{u}} (h : (Λ[2, 0] : SSet.{u}) ⟶ Q) :
    Q _⦋1⦌ :=
  SSet.yonedaEquiv (SSet.horn₂₀.ι₀₂ ≫ h)

/-- The distinguished `1 → 2` edge of a right outer `2`-horn. -/
def rightOuterHorn₂LastEdge {Q : SSet.{u}} (h : (Λ[2, 2] : SSet.{u}) ⟶ Q) :
    Q _⦋1⦌ :=
  SSet.yonedaEquiv (SSet.horn₂₂.ι₁₂ ≫ h)

/-- The `0 → 2` edge of a right outer `2`-horn. -/
def rightOuterHorn₂LongEdge {Q : SSet.{u}} (h : (Λ[2, 2] : SSet.{u}) ⟶ Q) :
    Q _⦋1⦌ :=
  SSet.yonedaEquiv (SSet.horn₂₂.ι₀₂ ≫ h)

/-- Restriction from coherent free-living equivalences to equivalence `1`-simplices. -/
def coherentEquivalenceRestriction {Q : SSet.{u}} :
    (CategoryTheory.nerve EquivalenceInterval.{u} ⟶ Q) →
      EquivalenceOneSimplex Q :=
  fun F ↦ ⟨equivalenceIntervalRestriction F,
    equivalenceIntervalRestriction_isEquivalence F⟩

/-- Extension data is equivalent to a map with the specified restricted `1`-simplex. -/
theorem nonempty_extension_iff_exists_restriction
    {Q : SSet.{u}} {x y : Q _⦋0⦌} (e : SSet.Edge x y) :
    Nonempty (EquivalenceIntervalExtension e) ↔
      ∃ F : CategoryTheory.nerve EquivalenceInterval.{u} ⟶ Q,
        equivalenceIntervalRestriction F = e.edge := by
  constructor
  · rintro ⟨h⟩
    refine ⟨h.map, ?_⟩
    have hr := congrArg SSet.yonedaEquiv h.restrict
    simpa [equivalenceIntervalInclusion, equivalenceIntervalRestriction,
      SSet.yonedaEquiv_comp] using hr
  · rintro ⟨F, hF⟩
    refine ⟨⟨F, ?_⟩⟩
    apply SSet.yonedaEquiv.injective
    simpa [equivalenceIntervalInclusion, equivalenceIntervalRestriction,
      SSet.yonedaEquiv_comp] using hF

/-- The still-unproved vertex-level assertion that every equivalence edge has an extension. -/
def EveryEquivalenceEdgeExtends (Q : SSet.{u}) : Prop :=
  ∀ s : Q _⦋1⦌, EdgeIsEquivalence (SSet.Edge.mk' s) →
    ∃ F : CategoryTheory.nerve EquivalenceInterval.{u} ⟶ Q,
      equivalenceIntervalRestriction F = s

/-- Extending every equivalence edge is exactly surjectivity of coherent restriction. -/
theorem everyEquivalenceEdgeExtends_iff_surjective (Q : SSet.{u}) :
    EveryEquivalenceEdgeExtends Q ↔
      Function.Surjective (coherentEquivalenceRestriction (Q := Q)) := by
  constructor
  · intro h s
    obtain ⟨F, hF⟩ := h s.1 s.2
    refine ⟨F, ?_⟩
    apply Subtype.ext
    exact hF
  · intro h s hs
    obtain ⟨F, hF⟩ := h ⟨s, hs⟩
    refine ⟨F, ?_⟩
    exact congrArg Subtype.val hF

/-- The raw-simplex and endpoint-indexed formulations of coherent extension agree. -/
theorem everyEquivalenceEdgeExtends_iff_dependent (Q : SSet.{u}) :
    EveryEquivalenceEdgeExtends Q ↔
      ∀ {x y : Q _⦋0⦌} (e : SSet.Edge x y), EdgeIsEquivalence e →
        Nonempty (EquivalenceIntervalExtension e) := by
  constructor
  · intro h x y e he
    let e' := SSet.Edge.castEndpoints e.src_eq e.tgt_eq e
    have he' : EdgeIsEquivalence e' := he.castEndpoints e.src_eq e.tgt_eq
    have heq : e' = SSet.Edge.mk' e.edge := by
      apply SSet.Edge.ext
      simp only [e', SSet.Edge.castEndpoints_edge, SSet.Edge.mk'_edge]
    have hs : EdgeIsEquivalence (SSet.Edge.mk' e.edge) := by
      simpa only [heq] using he'
    obtain ⟨F, hF⟩ := h e.edge hs
    exact (nonempty_extension_iff_exists_restriction e).2 ⟨F, hF⟩
  · intro h s hs
    exact (nonempty_extension_iff_exists_restriction (SSet.Edge.mk' s)).1
      (h (SSet.Edge.mk' s) hs)

section NerveTarget

variable {C : Type u} [Category.{0} C]
variable {X Y : C} (f : X ⟶ Y) [IsIso f]

/-- The functor from the free-living equivalence determined by an actual isomorphism. -/
def equivalenceIntervalFunctorOfIso : EquivalenceInterval.{u} ⥤ C where
  obj
    | .zero => X
    | .one => Y
  map {A B} _ := by
    cases A <;> cases B
    · exact 𝟙 X
    · exact f
    · exact inv f
    · exact 𝟙 Y
  map_id A := by
    cases A <;> rfl
  map_comp {A B D} _ _ := by
    cases A <;> cases B <;> cases D <;> simp

@[simp]
theorem equivalenceIntervalFunctorOfIso_map_forward :
    (equivalenceIntervalFunctorOfIso f).map equivalenceIntervalForward = f :=
  rfl

/-- The nerve map determined by an actual isomorphism. -/
def nerveEquivalenceIntervalExtension :
    CategoryTheory.nerve EquivalenceInterval.{u} ⟶ CategoryTheory.nerve C :=
  CategoryTheory.nerveMap (equivalenceIntervalFunctorOfIso f)

/-- The nerve extension restricts to the original isomorphism edge. -/
theorem nerveEquivalenceIntervalExtension_restrict :
    equivalenceIntervalInclusion.{u} ≫ nerveEquivalenceIntervalExtension f =
      SSet.yonedaEquiv.symm (CategoryTheory.nerve.edgeMk f).edge := by
  apply SSet.yonedaEquiv.injective
  simp only [equivalenceIntervalInclusion, nerveEquivalenceIntervalExtension,
    SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  change ((CategoryTheory.nerve.edgeMk equivalenceIntervalForward).map
      (CategoryTheory.nerveMap (equivalenceIntervalFunctorOfIso f))).edge =
    (CategoryTheory.nerve.edgeMk f).edge
  apply congrArg SSet.Edge.edge
  apply CategoryTheory.nerve.homEquiv.injective
  rw [CategoryTheory.nerve.homEquiv_edgeMk_map_nerveMap]
  exact (CategoryTheory.nerve.homEquiv_edgeMk f).symm

/-- An actual isomorphism edge in an ordinary nerve has a coherent extension. -/
def nerveEdgeEquivalenceIntervalExtension :
    EquivalenceIntervalExtension (CategoryTheory.nerve.edgeMk f) where
  map := nerveEquivalenceIntervalExtension f
  restrict := nerveEquivalenceIntervalExtension_restrict f

end NerveTarget

namespace Truncated

open SSet.Truncated
open SimplicialObject.Truncated

private lemma yonedaEquiv_delta_comp
    {Q : SSet.{u}} {n : ℕ} (i : Fin (n + 2)) (σ : Δ[n + 1] ⟶ Q) :
    SSet.yonedaEquiv (SSet.stdSimplex.δ i ≫ σ) =
      Q.δ i (SSet.yonedaEquiv σ) := by
  change σ.app _ (Δ[n + 1].δ i (SSet.yonedaEquiv (𝟙 Δ[n + 1]))) =
    Q.δ i (σ.app _ (SSet.yonedaEquiv (𝟙 Δ[n + 1])))
  exact SSet.δ_naturality_apply σ i (SSet.yonedaEquiv (𝟙 Δ[n + 1]))

@[implicit_reducible]
private noncomputable def quasicategoryFill21
    {Q : SSet.{u}} [SSet.Quasicategory Q]
    {x₀ x₁ x₂ : Q _⦋0⦌}
    (e₀₁ : SSet.Edge x₀ x₁) (e₁₂ : SSet.Edge x₁ x₂) :
    Nonempty (Σ e₀₂ : SSet.Edge x₀ x₂, SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂) := by
  let f₀₁ : Δ[1] ⟶ Q := SSet.yonedaEquiv.symm e₀₁.edge
  let f₁₂ : Δ[1] ⟶ Q := SSet.yonedaEquiv.symm e₁₂.edge
  have hcompat : SSet.stdSimplex.δ 0 ≫ f₀₁ = SSet.stdSimplex.δ 1 ≫ f₁₂ := by
    apply SSet.yonedaEquiv.injective
    simp only [SSet.yonedaEquiv_comp, f₀₁, f₁₂]
    exact e₀₁.tgt_eq.trans e₁₂.src_eq.symm
  let h : (Λ[2, 1] : SSet) ⟶ Q := SSet.horn₂₁.isPushout.desc f₀₁ f₁₂ hcompat
  obtain ⟨σ, hσ⟩ := SSet.Quasicategory.hornFilling (by simp) (by simp) h
  let s : Q _⦋2⦌ := SSet.yonedaEquiv σ
  have hd₂ : Q.δ 2 s = e₀₁.edge := by
    have hface := congrArg (fun k ↦ SSet.horn₂₁.ι₀₁ ≫ k) hσ
    have hmap : f₀₁ = SSet.stdSimplex.δ 2 ≫ σ := by
      simpa [h, ← Category.assoc] using hface
    calc
      Q.δ 2 s = SSet.yonedaEquiv (SSet.stdSimplex.δ 2 ≫ σ) :=
        (yonedaEquiv_delta_comp 2 σ).symm
      _ = SSet.yonedaEquiv f₀₁ := congrArg SSet.yonedaEquiv hmap.symm
      _ = e₀₁.edge := Equiv.apply_symm_apply _ _
  have hd₀ : Q.δ 0 s = e₁₂.edge := by
    have hface := congrArg (fun k ↦ SSet.horn₂₁.ι₁₂ ≫ k) hσ
    have hmap : f₁₂ = SSet.stdSimplex.δ 0 ≫ σ := by
      simpa [h, ← Category.assoc] using hface
    calc
      Q.δ 0 s = SSet.yonedaEquiv (SSet.stdSimplex.δ 0 ≫ σ) :=
        (yonedaEquiv_delta_comp 0 σ).symm
      _ = SSet.yonedaEquiv f₁₂ := congrArg SSet.yonedaEquiv hmap.symm
      _ = e₁₂.edge := Equiv.apply_symm_apply _ _
  let e₀₂ : SSet.Edge x₀ x₂ := SSet.Edge.mk (Q.δ 1 s) (by
    rw [← e₀₁.src_eq, ← hd₂]
    exact (Q.δ_comp_δ_apply (i := 1) (j := 1) le_rfl s).symm) (by
    rw [← e₁₂.tgt_eq, ← hd₀]
    exact Q.δ_comp_δ_apply (i := 0) (j := 0) le_rfl s)
  exact ⟨⟨e₀₂, SSet.Edge.CompStruct.mk s hd₂ hd₀ rfl⟩⟩

@[implicit_reducible]
private noncomputable def quasicategoryFill31
    {Q : SSet.{u}} [SSet.Quasicategory Q]
    {x₀ x₁ x₂ x₃ : Q _⦋0⦌}
    {e₀₁ : SSet.Edge x₀ x₁} {e₁₂ : SSet.Edge x₁ x₂}
    {e₂₃ : SSet.Edge x₂ x₃} {e₀₂ : SSet.Edge x₀ x₂}
    {e₁₃ : SSet.Edge x₁ x₃} {e₀₃ : SSet.Edge x₀ x₃}
    (f₃ : SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂)
    (f₀ : SSet.Edge.CompStruct e₁₂ e₂₃ e₁₃)
    (f₂ : SSet.Edge.CompStruct e₀₁ e₁₃ e₀₃) :
    Nonempty (SSet.Edge.CompStruct e₀₂ e₂₃ e₀₃) := by
  let p₀ : Δ[2] ⟶ Q := SSet.yonedaEquiv.symm f₀.simplex
  let p₂ : Δ[2] ⟶ Q := SSet.yonedaEquiv.symm f₂.simplex
  let p₃ : Δ[2] ⟶ Q := SSet.yonedaEquiv.symm f₃.simplex
  have h₁₂ : SSet.stdSimplex.δ 2 ≫ p₀ = SSet.stdSimplex.δ 0 ≫ p₃ := by
    apply SSet.yonedaEquiv.injective
    simp [yonedaEquiv_delta_comp, p₀, p₃]
  have h₁₃ : SSet.stdSimplex.δ 1 ≫ p₀ = SSet.stdSimplex.δ 0 ≫ p₂ := by
    apply SSet.yonedaEquiv.injective
    simp [yonedaEquiv_delta_comp, p₀, p₂]
  have h₂₃ : SSet.stdSimplex.δ 2 ≫ p₂ = SSet.stdSimplex.δ 2 ≫ p₃ := by
    apply SSet.yonedaEquiv.injective
    simp [yonedaEquiv_delta_comp, p₂, p₃]
  let h : (Λ[3, 1] : SSet) ⟶ Q := SSet.horn₃₁.desc p₀ p₂ p₃ h₁₂ h₁₃ h₂₃
  obtain ⟨σ, hσ⟩ := SSet.Quasicategory.hornFilling (by simp) (by simp) h
  let s : Q _⦋3⦌ := SSet.yonedaEquiv σ
  have hd₀ : Q.δ 0 s = f₀.simplex := by
    have hface := congrArg (fun k ↦ SSet.horn₃₁.ι₀ ≫ k) hσ
    have hmap : p₀ = SSet.stdSimplex.δ 0 ≫ σ := by
      simpa [h, ← Category.assoc] using hface
    calc
      Q.δ 0 s = SSet.yonedaEquiv (SSet.stdSimplex.δ 0 ≫ σ) :=
        (yonedaEquiv_delta_comp 0 σ).symm
      _ = SSet.yonedaEquiv p₀ := congrArg SSet.yonedaEquiv hmap.symm
      _ = f₀.simplex := Equiv.apply_symm_apply _ _
  have hd₂ : Q.δ 2 s = f₂.simplex := by
    have hface := congrArg (fun k ↦ SSet.horn₃₁.ι₂ ≫ k) hσ
    have hmap : p₂ = SSet.stdSimplex.δ 2 ≫ σ := by
      simpa [h, ← Category.assoc] using hface
    calc
      Q.δ 2 s = SSet.yonedaEquiv (SSet.stdSimplex.δ 2 ≫ σ) :=
        (yonedaEquiv_delta_comp 2 σ).symm
      _ = SSet.yonedaEquiv p₂ := congrArg SSet.yonedaEquiv hmap.symm
      _ = f₂.simplex := Equiv.apply_symm_apply _ _
  have hd₃ : Q.δ 3 s = f₃.simplex := by
    have hface := congrArg (fun k ↦ SSet.horn₃₁.ι₃ ≫ k) hσ
    have hmap : p₃ = SSet.stdSimplex.δ 3 ≫ σ := by
      simpa [h, ← Category.assoc] using hface
    calc
      Q.δ 3 s = SSet.yonedaEquiv (SSet.stdSimplex.δ 3 ≫ σ) :=
        (yonedaEquiv_delta_comp 3 σ).symm
      _ = SSet.yonedaEquiv p₃ := congrArg SSet.yonedaEquiv hmap.symm
      _ = f₃.simplex := Equiv.apply_symm_apply _ _
  refine ⟨SSet.Edge.CompStruct.mk (Q.δ 1 s) ?_ ?_ ?_⟩
  · rw [← f₃.d₁, ← hd₃]
    exact (Q.δ_comp_δ_apply (i := 1) (j := 2) (by simp) s).symm
  · rw [← f₀.d₀, ← hd₀]
    exact Q.δ_comp_δ_apply (i := 0) (j := 0) le_rfl s
  · rw [← f₂.d₁, ← hd₂]
    exact (Q.δ_comp_δ_apply (i := 1) (j := 1) le_rfl s).symm

@[implicit_reducible]
private noncomputable def quasicategoryFill32
    {Q : SSet.{u}} [SSet.Quasicategory Q]
    {x₀ x₁ x₂ x₃ : Q _⦋0⦌}
    {e₀₁ : SSet.Edge x₀ x₁} {e₁₂ : SSet.Edge x₁ x₂}
    {e₂₃ : SSet.Edge x₂ x₃} {e₀₂ : SSet.Edge x₀ x₂}
    {e₁₃ : SSet.Edge x₁ x₃} {e₀₃ : SSet.Edge x₀ x₃}
    (f₃ : SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂)
    (f₀ : SSet.Edge.CompStruct e₁₂ e₂₃ e₁₃)
    (f₁ : SSet.Edge.CompStruct e₀₂ e₂₃ e₀₃) :
    Nonempty (SSet.Edge.CompStruct e₀₁ e₁₃ e₀₃) := by
  let p₀ : Δ[2] ⟶ Q := SSet.yonedaEquiv.symm f₀.simplex
  let p₁ : Δ[2] ⟶ Q := SSet.yonedaEquiv.symm f₁.simplex
  let p₃ : Δ[2] ⟶ Q := SSet.yonedaEquiv.symm f₃.simplex
  have h₀₂ : SSet.stdSimplex.δ 2 ≫ p₁ = SSet.stdSimplex.δ 1 ≫ p₃ := by
    apply SSet.yonedaEquiv.injective
    simp [yonedaEquiv_delta_comp, p₁, p₃]
  have h₁₂ : SSet.stdSimplex.δ 2 ≫ p₀ = SSet.stdSimplex.δ 0 ≫ p₃ := by
    apply SSet.yonedaEquiv.injective
    simp [yonedaEquiv_delta_comp, p₀, p₃]
  have h₂₃ : SSet.stdSimplex.δ 0 ≫ p₀ = SSet.stdSimplex.δ 0 ≫ p₁ := by
    apply SSet.yonedaEquiv.injective
    simp [yonedaEquiv_delta_comp, p₀, p₁]
  let h : (Λ[3, 2] : SSet) ⟶ Q := SSet.horn₃₂.desc p₀ p₁ p₃ h₀₂ h₁₂ h₂₃
  obtain ⟨σ, hσ⟩ := SSet.Quasicategory.hornFilling (by simp) (by simp) h
  let s : Q _⦋3⦌ := SSet.yonedaEquiv σ
  have hd₀ : Q.δ 0 s = f₀.simplex := by
    have hface := congrArg (fun k ↦ SSet.horn₃₂.ι₀ ≫ k) hσ
    have hmap : p₀ = SSet.stdSimplex.δ 0 ≫ σ := by
      simpa [h, ← Category.assoc] using hface
    calc
      Q.δ 0 s = SSet.yonedaEquiv (SSet.stdSimplex.δ 0 ≫ σ) :=
        (yonedaEquiv_delta_comp 0 σ).symm
      _ = SSet.yonedaEquiv p₀ := congrArg SSet.yonedaEquiv hmap.symm
      _ = f₀.simplex := Equiv.apply_symm_apply _ _
  have hd₁ : Q.δ 1 s = f₁.simplex := by
    have hface := congrArg (fun k ↦ SSet.horn₃₂.ι₁ ≫ k) hσ
    have hmap : p₁ = SSet.stdSimplex.δ 1 ≫ σ := by
      simpa [h, ← Category.assoc] using hface
    calc
      Q.δ 1 s = SSet.yonedaEquiv (SSet.stdSimplex.δ 1 ≫ σ) :=
        (yonedaEquiv_delta_comp 1 σ).symm
      _ = SSet.yonedaEquiv p₁ := congrArg SSet.yonedaEquiv hmap.symm
      _ = f₁.simplex := Equiv.apply_symm_apply _ _
  have hd₃ : Q.δ 3 s = f₃.simplex := by
    have hface := congrArg (fun k ↦ SSet.horn₃₂.ι₃ ≫ k) hσ
    have hmap : p₃ = SSet.stdSimplex.δ 3 ≫ σ := by
      simpa [h, ← Category.assoc] using hface
    calc
      Q.δ 3 s = SSet.yonedaEquiv (SSet.stdSimplex.δ 3 ≫ σ) :=
        (yonedaEquiv_delta_comp 3 σ).symm
      _ = SSet.yonedaEquiv p₃ := congrArg SSet.yonedaEquiv hmap.symm
      _ = f₃.simplex := Equiv.apply_symm_apply _ _
  refine ⟨SSet.Edge.CompStruct.mk (Q.δ 2 s) ?_ ?_ ?_⟩
  · rw [← f₃.d₂, ← hd₃]
    exact (Q.δ_comp_δ_apply (i := 2) (j := 2) le_rfl s).symm
  · rw [← f₀.d₁, ← hd₀]
    exact Q.δ_comp_δ_apply (i := 0) (j := 1) (by simp) s
  · rw [← f₁.d₁, ← hd₁]
    exact Q.δ_comp_δ_apply (i := 1) (j := 1) le_rfl s

/-- The `2`-truncation of a quasicategory has the three low-dimensional
horn fillers used by the edge-quotient homotopy-category API. -/
noncomputable instance truncationQuasicategory₂
    (Q : SSet.{u}) [SSet.Quasicategory Q] :
    SSet.Truncated.Quasicategory₂ ((SSet.truncation 2).obj Q) where
  fill21 e₀₁ e₁₂ := by
    obtain ⟨⟨e₀₂, h⟩⟩ := quasicategoryFill21
      (SSet.Edge.ofTruncated e₀₁) (SSet.Edge.ofTruncated e₁₂)
    exact ⟨⟨e₀₂.toTruncated, h.toTruncated⟩⟩
  fill31 f₃ f₀ f₂ := by
    exact (quasicategoryFill31
      (SSet.Edge.CompStruct.ofTruncated f₃)
      (SSet.Edge.CompStruct.ofTruncated f₀)
      (SSet.Edge.CompStruct.ofTruncated f₂)).map
        SSet.Edge.CompStruct.toTruncated
  fill32 f₃ f₀ f₁ := by
    exact (quasicategoryFill32
      (SSet.Edge.CompStruct.ofTruncated f₃)
      (SSet.Edge.CompStruct.ofTruncated f₀)
      (SSet.Edge.CompStruct.ofTruncated f₁)).map
        SSet.Edge.CompStruct.toTruncated

/-- The comparison from the path presentation of the homotopy category to the
edge-quotient presentation. -/
noncomputable def homotopyCategoryToHomotopyCategory₂
    (A : SSet.Truncated 2) [SSet.Truncated.Quasicategory₂ A] :
    A.HomotopyCategory ⥤ SSet.Truncated.HomotopyCategory₂ A :=
  SSet.Truncated.HomotopyCategory.lift
    (fun x ↦ SSet.Truncated.HomotopyCategory₂.mk x)
    (fun e ↦ SSet.Truncated.HomotopyCategory₂.homMk e)
    (fun x ↦ SSet.Truncated.HomotopyCategory₂.homMk_id
      (SSet.Truncated.HomotopyCategory₂.mk x))
    (fun h ↦ h.homotopyCategory₂_fac)

@[simp]
theorem homotopyCategoryToHomotopyCategory₂_map_homMk
    {A : SSet.Truncated 2} [SSet.Truncated.Quasicategory₂ A]
    {x y : A _⦋0⦌₂} (e : SSet.Truncated.Edge x y) :
    (homotopyCategoryToHomotopyCategory₂ A).map
        (SSet.Truncated.HomotopyCategory.homMk e) =
      SSet.Truncated.HomotopyCategory₂.homMk e :=
  SSet.Truncated.HomotopyCategory.lift_map_homMk _ _ _ _ e

/-- A representative inverse edge and the two triangles witnessing its inverse laws. -/
structure InverseTriangleData {A : SSet.Truncated 2}
    {x y : A _⦋0⦌₂} (e : SSet.Truncated.Edge x y) where
  inverse : SSet.Truncated.Edge y x
  rightTriangle :
    SSet.Truncated.Edge.CompStruct e inverse (SSet.Truncated.Edge.id x)
  leftTriangle :
    SSet.Truncated.Edge.CompStruct inverse e (SSet.Truncated.Edge.id y)

/-- An isomorphism represented by an edge in `HomotopyCategory₂` has inverse triangles. -/
noncomputable def inverseTriangleDataOfIsIso
    {A : SSet.Truncated 2} [SSet.Truncated.Quasicategory₂ A]
    {x y : A _⦋0⦌₂} (e : SSet.Truncated.Edge x y)
    [IsIso (SSet.Truncated.HomotopyCategory₂.homMk e)] :
    InverseTriangleData e := by
  let einv := inv (SSet.Truncated.HomotopyCategory₂.homMk e)
  let g := Classical.choose
    (SSet.Truncated.HomotopyCategory₂.homMk_surjective einv)
  have hg : SSet.Truncated.HomotopyCategory₂.homMk g = einv :=
    Classical.choose_spec
      (SSet.Truncated.HomotopyCategory₂.homMk_surjective einv)
  refine ⟨g, ?_, ?_⟩
  · apply SSet.Truncated.Edge.CompStruct.ofHomotopyCategory₂Fac
    rw [hg]
    exact (IsIso.hom_inv_id (SSet.Truncated.HomotopyCategory₂.homMk e)).trans
      (SSet.Truncated.HomotopyCategory₂.homMk_id
        (SSet.Truncated.HomotopyCategory₂.mk x)).symm
  · apply SSet.Truncated.Edge.CompStruct.ofHomotopyCategory₂Fac
    rw [hg]
    exact (IsIso.inv_hom_id (SSet.Truncated.HomotopyCategory₂.homMk e)).trans
      (SSet.Truncated.HomotopyCategory₂.homMk_id
        (SSet.Truncated.HomotopyCategory₂.mk y)).symm

/-- Invertibility in the path presentation of the homotopy category already gives
representative inverse triangles in the edge-quotient presentation. -/
noncomputable def inverseTriangleDataOfPathIsIso
    {A : SSet.Truncated 2} [SSet.Truncated.Quasicategory₂ A]
    {x y : A _⦋0⦌₂} (e : SSet.Truncated.Edge x y)
    [IsIso (SSet.Truncated.HomotopyCategory.homMk e)] :
    InverseTriangleData e := by
  letI : IsIso (SSet.Truncated.HomotopyCategory₂.homMk e) := by
    let hmap : IsIso ((homotopyCategoryToHomotopyCategory₂ A).map
        (SSet.Truncated.HomotopyCategory.homMk e)) :=
      Functor.map_isIso (homotopyCategoryToHomotopyCategory₂ A) _
    rw [homotopyCategoryToHomotopyCategory₂_map_homMk] at hmap
    exact hmap
  exact inverseTriangleDataOfIsIso e

/-- An equivalence edge in a quasicategory has an actual inverse edge and two
`2`-simplices witnessing the inverse laws. -/
noncomputable def inverseTriangleDataOfEdgeIsEquivalence
    {Q : SSet.{u}} [SSet.Quasicategory Q]
    {x y : Q _⦋0⦌} (e : SSet.Edge x y) (he : EdgeIsEquivalence e) :
    InverseTriangleData e.toTruncated := by
  letI : IsIso (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) := he
  exact inverseTriangleDataOfPathIsIso e.toTruncated

/-- The two-dimensional special left outer horn filler.  If the leading edge is
an equivalence, then it can be completed against any edge with the same source.

The construction composes with a representative inverse and uses a single
inner `3`-horn to cancel the resulting inverse pair. -/
@[implicit_reducible]
noncomputable def specialOuterCompStruct₂₀
    {Q : SSet.{u}} [SSet.Quasicategory Q]
    {x₀ x₁ x₂ : Q _⦋0⦌}
    (e₀₁ : SSet.Edge x₀ x₁) (e₀₂ : SSet.Edge x₀ x₂)
    (he : EdgeIsEquivalence e₀₁) :
    Nonempty (Σ e₁₂ : SSet.Edge x₁ x₂, SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂) := by
  let d := inverseTriangleDataOfEdgeIsEquivalence e₀₁ he
  let e₁₀ : SSet.Edge x₁ x₀ := SSet.Edge.ofTruncated d.inverse
  let rightTriangle : SSet.Edge.CompStruct e₀₁ e₁₀ (SSet.Edge.id x₀) :=
    SSet.Edge.CompStruct.ofTruncated d.rightTriangle
  obtain ⟨⟨e₁₂, inverseThenEdge⟩⟩ := quasicategoryFill21 e₁₀ e₀₂
  exact (quasicategoryFill32 rightTriangle inverseThenEdge
    (SSet.Edge.CompStruct.idComp e₀₂)).map (fun triangle ↦ ⟨e₁₂, triangle⟩)

/-- The two-dimensional special right outer horn filler.  If the trailing edge
is an equivalence, then it can be completed against any edge with the same
target. -/
@[implicit_reducible]
noncomputable def specialOuterCompStruct₂₂
    {Q : SSet.{u}} [SSet.Quasicategory Q]
    {x₀ x₁ x₂ : Q _⦋0⦌}
    (e₁₂ : SSet.Edge x₁ x₂) (e₀₂ : SSet.Edge x₀ x₂)
    (he : EdgeIsEquivalence e₁₂) :
    Nonempty (Σ e₀₁ : SSet.Edge x₀ x₁, SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂) := by
  let d := inverseTriangleDataOfEdgeIsEquivalence e₁₂ he
  let e₂₁ : SSet.Edge x₂ x₁ := SSet.Edge.ofTruncated d.inverse
  let leftTriangle : SSet.Edge.CompStruct e₂₁ e₁₂ (SSet.Edge.id x₂) :=
    SSet.Edge.CompStruct.ofTruncated d.leftTriangle
  obtain ⟨⟨e₀₁, edgeThenInverse⟩⟩ := quasicategoryFill21 e₀₂ e₂₁
  exact (quasicategoryFill31 edgeThenInverse leftTriangle
    (SSet.Edge.CompStruct.compId e₀₂)).map (fun triangle ↦ ⟨e₀₁, triangle⟩)

/-- Joyal's special left outer horn theorem in dimension `2`. -/
theorem specialLeftOuterHorn₂_filling
    {Q : SSet.{u}} [SSet.Quasicategory Q]
    (h : (Λ[2, 0] : SSet.{u}) ⟶ Q)
    (he : EdgeIsEquivalence (SSet.Edge.mk' (leftOuterHorn₂FirstEdge h))) :
    ∃ σ : Δ[2] ⟶ Q, (SSet.horn 2 0).ι ≫ σ = h := by
  let f₀₁ : Δ[1] ⟶ Q := SSet.horn₂₀.ι₀₁ ≫ h
  let f₀₂ : Δ[1] ⟶ Q := SSet.horn₂₀.ι₀₂ ≫ h
  let e₀₁ := SSet.Edge.mk' (SSet.yonedaEquiv f₀₁)
  let e₀₂' := SSet.Edge.mk' (SSet.yonedaEquiv f₀₂)
  have hsrc : Q.δ 1 (SSet.yonedaEquiv f₀₁) =
      Q.δ 1 (SSet.yonedaEquiv f₀₂) := by
    have hv := congrArg SSet.yonedaEquiv SSet.horn₂₀.isPushout.w
    change (Λ[2, 0] : SSet.{u}).δ 1 (SSet.yonedaEquiv SSet.horn₂₀.ι₀₁) =
      (Λ[2, 0] : SSet.{u}).δ 1 (SSet.yonedaEquiv SSet.horn₂₀.ι₀₂) at hv
    calc
      Q.δ 1 (SSet.yonedaEquiv f₀₁) =
          Q.δ 1 (h.app _ (SSet.yonedaEquiv SSet.horn₂₀.ι₀₁)) := rfl
      _ = h.app _ ((Λ[2, 0] : SSet.{u}).δ 1
          (SSet.yonedaEquiv SSet.horn₂₀.ι₀₁)) :=
        (SSet.δ_naturality_apply h 1 _).symm
      _ = h.app _ ((Λ[2, 0] : SSet.{u}).δ 1
          (SSet.yonedaEquiv SSet.horn₂₀.ι₀₂)) := congrArg (h.app _) hv
      _ = Q.δ 1 (h.app _ (SSet.yonedaEquiv SSet.horn₂₀.ι₀₂)) :=
        SSet.δ_naturality_apply h 1 _
      _ = Q.δ 1 (SSet.yonedaEquiv f₀₂) := rfl
  let e₀₂ : SSet.Edge (Q.δ 1 (SSet.yonedaEquiv f₀₁))
      (Q.δ 0 (SSet.yonedaEquiv f₀₂)) :=
    SSet.Edge.castEndpoints hsrc rfl e₀₂'
  have he' : EdgeIsEquivalence e₀₁ := by
    simpa [leftOuterHorn₂FirstEdge, e₀₁, f₀₁] using he
  obtain ⟨⟨e₁₂, triangle⟩⟩ := specialOuterCompStruct₂₀ e₀₁ e₀₂ he'
  refine ⟨SSet.yonedaEquiv.symm triangle.simplex, ?_⟩
  apply SSet.horn₂₀.isPushout.hom_ext
  · apply SSet.yonedaEquiv.injective
    simp [f₀₁, yonedaEquiv_delta_comp, triangle.d₂, e₀₁, SSet.Edge.mk'_edge]
  · apply SSet.yonedaEquiv.injective
    simp [f₀₂, yonedaEquiv_delta_comp, triangle.d₁, e₀₂, e₀₂',
      SSet.Edge.castEndpoints_edge, SSet.Edge.mk'_edge]

/-- Joyal's special right outer horn theorem in dimension `2`. -/
theorem specialRightOuterHorn₂_filling
    {Q : SSet.{u}} [SSet.Quasicategory Q]
    (h : (Λ[2, 2] : SSet.{u}) ⟶ Q)
    (he : EdgeIsEquivalence (SSet.Edge.mk' (rightOuterHorn₂LastEdge h))) :
    ∃ σ : Δ[2] ⟶ Q, (SSet.horn 2 2).ι ≫ σ = h := by
  let f₀₂ : Δ[1] ⟶ Q := SSet.horn₂₂.ι₀₂ ≫ h
  let f₁₂ : Δ[1] ⟶ Q := SSet.horn₂₂.ι₁₂ ≫ h
  let e₀₂' := SSet.Edge.mk' (SSet.yonedaEquiv f₀₂)
  let e₁₂ := SSet.Edge.mk' (SSet.yonedaEquiv f₁₂)
  have htgt : Q.δ 0 (SSet.yonedaEquiv f₁₂) =
      Q.δ 0 (SSet.yonedaEquiv f₀₂) := by
    have hv := congrArg SSet.yonedaEquiv SSet.horn₂₂.isPushout.w
    change (Λ[2, 2] : SSet.{u}).δ 0 (SSet.yonedaEquiv SSet.horn₂₂.ι₀₂) =
      (Λ[2, 2] : SSet.{u}).δ 0 (SSet.yonedaEquiv SSet.horn₂₂.ι₁₂) at hv
    calc
      Q.δ 0 (SSet.yonedaEquiv f₁₂) =
          Q.δ 0 (h.app _ (SSet.yonedaEquiv SSet.horn₂₂.ι₁₂)) := rfl
      _ = h.app _ ((Λ[2, 2] : SSet.{u}).δ 0
          (SSet.yonedaEquiv SSet.horn₂₂.ι₁₂)) :=
        (SSet.δ_naturality_apply h 0 _).symm
      _ = h.app _ ((Λ[2, 2] : SSet.{u}).δ 0
          (SSet.yonedaEquiv SSet.horn₂₂.ι₀₂)) := congrArg (h.app _) hv.symm
      _ = Q.δ 0 (h.app _ (SSet.yonedaEquiv SSet.horn₂₂.ι₀₂)) :=
        SSet.δ_naturality_apply h 0 _
      _ = Q.δ 0 (SSet.yonedaEquiv f₀₂) := rfl
  let e₀₂ : SSet.Edge (Q.δ 1 (SSet.yonedaEquiv f₀₂))
      (Q.δ 0 (SSet.yonedaEquiv f₁₂)) :=
    SSet.Edge.castEndpoints rfl htgt e₀₂'
  have he' : EdgeIsEquivalence e₁₂ := by
    simpa [rightOuterHorn₂LastEdge, e₁₂, f₁₂] using he
  obtain ⟨⟨e₀₁, triangle⟩⟩ := specialOuterCompStruct₂₂ e₁₂ e₀₂ he'
  refine ⟨SSet.yonedaEquiv.symm triangle.simplex, ?_⟩
  apply SSet.horn₂₂.isPushout.hom_ext
  · apply SSet.yonedaEquiv.injective
    simp [f₀₂, yonedaEquiv_delta_comp, triangle.d₁, e₀₂, e₀₂',
      SSet.Edge.castEndpoints_edge, SSet.Edge.mk'_edge]
  · apply SSet.yonedaEquiv.injective
    simp [f₁₂, yonedaEquiv_delta_comp, triangle.d₀, e₁₂, SSet.Edge.mk'_edge]

end Truncated

end Infinity
end LeanLCAExactChallenge
