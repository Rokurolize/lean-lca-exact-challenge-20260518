import LeanLCAExactChallenge.Infinity.EquivalenceForcing
import Mathlib.AlgebraicTopology.Quasicategory.TwoTruncated

/-!
# Coherent extensions of equivalence edges

`EquivalenceForcing.lean` packages extensions of an edge along the inclusion of the standard
`1`-simplex into the nerve of the free-living equivalence and proves that an extension forces
the edge to be an equivalence. This file reformulates the vertex-level converse as a precise
surjectivity statement on maps. It also constructs the extension for an actual isomorphism in
an ordinary nerve and extracts the two inverse triangles available in the separate
`2`-truncated API.

No converse for arbitrary quasicategories is asserted, and vertex-level surjectivity would not
by itself prove the required equivalence of mapping quasicategories. The pinned API supplies
inner-horn fillers, but not the outer-horn equivalence theorem or the coherent free-living
equivalence extension theorem needed for that converse. The generic simplicial homotopy
category used by `EdgeIsEquivalence` is also not yet compared with the edge-quotient homotopy
category in `Quasicategory.TwoTruncated`.
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
  let ea' := SSet.Edge.castEndpoints ea.src_eq ea.tgt_eq ea
  have hea' : EdgeIsEquivalence ea' := hea.castEndpoints ea.src_eq ea.tgt_eq
  have heq : ea' = SSet.Edge.mk' (equivalenceIntervalRestriction F) := by
    apply SSet.Edge.ext
    simp only [ea', SSet.Edge.castEndpoints_edge, SSet.Edge.mk'_edge,
      equivalenceIntervalRestriction]
    rfl
  simpa only [heq] using hea'

/-- The subtype of `1`-simplices whose associated edge is an equivalence. -/
def EquivalenceOneSimplex (Q : SSet.{u}) :=
  {s : Q _⦋1⦌ // EdgeIsEquivalence (SSet.Edge.mk' s)}

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

end Truncated

end Infinity
end LeanLCAExactChallenge
