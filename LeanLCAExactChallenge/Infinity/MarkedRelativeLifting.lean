import LeanLCAExactChallenge.Infinity.Localization
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import Mathlib.CategoryTheory.LiftingProperties.Limits
import Mathlib.CategoryTheory.LiftingProperties.PushoutProduct

/-!
# Relative lifting through marked equivalences

This file records categorical closure steps used in a marked proof of Joyal's equivalence
extension theorem.  It deliberately does not identify a special outer horn with an unmarked
inner-anodyne map.

For the actual equivalence-extension problem, the boundary condition is imposed directly on
the already restricted map `Map(J,Q) ⟶ EqEdge(Q)`.  It is essential not to first claim a right
lifting property for `Map(J,Q) ⟶ Map(Δ[1],Q)`: that raw map need not even lift vertices.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge
namespace Infinity

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MorphismProperty
open Simplicial

/-- The raw family of lifting problems produced by tensoring two maps with all boundary
inclusions.  This generic notion is not the marked equivalence-extension hypothesis. -/
def HasRawBoundaryBoxLifts {A B X Y : SSet.{u}}
    (i : A ⟶ B) (p : X ⟶ Y) : Prop :=
  ∀ n : ℕ,
    HasLiftingProperty
      (Arrow.mk i □ Arrow.mk (SSet.boundary.{u} n).ι).hom p

/-- Boundary-box lifting is precisely boundary lifting against the Leibniz pullback-hom. -/
lemma hasRawBoundaryBoxLifts_iff_boundary_rlp_pullbackHom
    {A B X Y : SSet.{u}} (i : A ⟶ B) (p : X ⟶ Y) :
    HasRawBoundaryBoxLifts i p ↔
      SSet.modelCategoryQuillen.I.rlp ((Opposite.op (Arrow.mk i)) ⋔ Arrow.mk p).hom := by
  constructor
  · intro h K L j hj
    obtain ⟨n⟩ := hj
    rw [← Arrow.PushoutProduct.hasLiftingProperty_mk_iff]
    exact h n
  · intro h n
    rw [Arrow.PushoutProduct.hasLiftingProperty_mk_iff]
    exact h _ (SSet.modelCategoryQuillen.boundary_ι_mem_I n)

/-- The special-outer-horn boundary boxes imply lifting against every monomorphism for the
Leibniz pullback-hom.  This is the marked closure theorem needed after the filtration step. -/
theorem pullbackHom_mem_monomorphisms_rlp_of_rawBoundaryBoxes
    {A B X Y : SSet.{u}} {i : A ⟶ B} {p : X ⟶ Y}
    (h : HasRawBoundaryBoxLifts i p) :
    (monomorphisms SSet.{u}).rlp ((Opposite.op (Arrow.mk i)) ⋔ Arrow.mk p).hom := by
  rw [SSet.rlp_monomorphisms,
    ← hasRawBoundaryBoxLifts_iff_boundary_rlp_pullbackHom]
  exact h

/-- The constrained boundary problems for an already restricted mapping map.

When `r : Map(J,Q) ⟶ EqEdge(Q)`, a square in this definition includes, in its type, the
requirement that the whole `Δ[n]`-family of restricted edges lies in `EqEdge(Q)`.  Thus its
`n = 0` case asks only for extension of an equivalence edge, not extension of an arbitrary
edge of `Q`. -/
def HasMarkedRestrictedBoundaryLifts {M E : SSet.{u}} (r : M ⟶ E) : Prop :=
  ∀ n : ℕ, HasLiftingProperty (SSet.boundary.{u} n).ι r

/-- Constrained boundary lifting is exactly lifting against the generating cofibrations. -/
lemma hasMarkedRestrictedBoundaryLifts_iff_generating_rlp
    {M E : SSet.{u}} (r : M ⟶ E) :
    HasMarkedRestrictedBoundaryLifts r ↔ SSet.modelCategoryQuillen.I.rlp r := by
  constructor
  · intro h K L j hj
    obtain ⟨n⟩ := hj
    exact h n
  · intro h n
    exact h _ (SSet.modelCategoryQuillen.boundary_ι_mem_I n)

/-- Once the special-outer-horn construction solves every constrained boundary square for
`Map(J,Q) ⟶ EqEdge(Q)`, the restricted map has the RLP against every monomorphism. -/
theorem markedRestricted_mem_monomorphisms_rlp
    {M E : SSet.{u}} {r : M ⟶ E} (h : HasMarkedRestrictedBoundaryLifts r) :
    (monomorphisms SSet.{u}).rlp r := by
  rw [SSet.rlp_monomorphisms, ← hasMarkedRestrictedBoundaryLifts_iff_generating_rlp]
  exact h

/-- Pulling back a map preserves each specified right lifting property. -/
lemma hasLiftingProperty_pullback_snd
    {K L X Y Z : SSet.{u}} {j : K ⟶ L} {p : X ⟶ Z} (q : Y ⟶ Z)
    [HasLiftingProperty j p] :
    HasLiftingProperty j (pullback.snd p q) :=
  (IsPullback.of_hasPullback p q).hasLiftingProperty j

/-- A base change of a map with the RLP against all monomorphisms again has that RLP. -/
theorem pullback_snd_mem_monomorphisms_rlp
    {X Y Z : SSet.{u}} {p : X ⟶ Z} (q : Y ⟶ Z)
    (hp : (monomorphisms SSet.{u}).rlp p) :
    (monomorphisms SSet.{u}).rlp (pullback.snd p q) := by
  intro K L j hj
  letI : HasLiftingProperty j p := hp j hj
  exact hasLiftingProperty_pullback_snd q

/-- A generic raw pullback-hom lifting result remains true under base change.  This lemma does
not assert that the unrestricted mapping map in the Joyal application satisfies its premise. -/
theorem pullback_pullbackHom_mem_monomorphisms_rlp_of_rawBoundaryBoxes
    {A B X Y T : SSet.{u}} {i : A ⟶ B} {p : X ⟶ Y}
    (q : T ⟶ ((Opposite.op (Arrow.mk i)) ⋔ Arrow.mk p).right)
    (h : HasRawBoundaryBoxLifts i p) :
    (monomorphisms SSet.{u}).rlp
      (pullback.snd ((Opposite.op (Arrow.mk i)) ⋔ Arrow.mk p).hom q) :=
  pullback_snd_mem_monomorphisms_rlp q
    (pullbackHom_mem_monomorphisms_rlp_of_rawBoundaryBoxes h)

end Infinity
end LeanLCAExactChallenge
