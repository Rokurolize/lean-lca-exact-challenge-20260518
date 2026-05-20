import LeanLCAExactChallenge.Derived.BoundedFiniteProducts

/-!
Boundary audit for transporting exact acyclicity along homotopy equivalences.

W221 reduced the homotopy-category iso-collapse to the theorem that exact acyclicity of
selected cochain complexes is invariant under `HomotopyEquiv`. This file records that
theorem as the minimal missing input and shows it is equivalent, for local consumers, to
the existing `IsClosedUnderIsomorphisms` bridge for `exactAcyclicHomotopyObject C`.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace ExactAcyclicHomotopyEquivTransportW225

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]

/-- Exact acyclicity transported along homotopy equivalences of selected cochain complexes. -/
abbrev ExactAcyclicTransportOfHomotopyEquiv : Prop :=
  ∀ {K L : CochainComplex C ℤ},
    exactAcyclic C K → HomotopyEquiv K L → exactAcyclic C L

/-- The W221 iso-closure collapse target. -/
abbrev ExactAcyclicIsoClosureCollapse : Prop :=
  exactAcyclicHomotopyIsoClosure C ≤ exactAcyclicHomotopyObject C

/--
If exact-acyclic homotopy objects are iso-closed, then a strict `HomotopyEquiv` transports
exact acyclicity through its associated homotopy-category isomorphism.
-/
theorem exactAcyclicTransportOfHomotopyEquiv_of_isClosedUnderIsomorphisms
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms] :
    ExactAcyclicTransportOfHomotopyEquiv C := by
  intro K L hK e
  have hL :
      exactAcyclicHomotopyObject C
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L) :=
    (exactAcyclicHomotopyObject C).prop_of_iso
      (HomotopyCategory.isoOfHomotopyEquiv e) hK
  exact hL

/-- The homotopy-equivalence transport theorem collapses the explicit iso-closure. -/
theorem exactAcyclicIsoClosureCollapse_of_homotopyEquivTransport
    (transport : ExactAcyclicTransportOfHomotopyEquiv C) :
    ExactAcyclicIsoClosureCollapse C := by
  intro X hX
  rcases hX with ⟨Y, hY, ⟨e⟩⟩
  obtain ⟨X₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨Y₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  exact transport hY (HomotopyCategory.homotopyEquivOfIso e.symm)

/-- The collapse is exactly the existing typeclass bridge used by direct bounded consumers. -/
theorem exactAcyclicHomotopyObject_isClosedUnderIsomorphisms_of_isoClosureCollapse
    (h : ExactAcyclicIsoClosureCollapse C) :
    (exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms := by
  rw [ObjectProperty.isClosedUnderIsomorphisms_iff_isoClosure_eq_self]
  apply le_antisymm
  · exact h
  · exact ObjectProperty.le_isoClosure (exactAcyclicHomotopyObject C)

/-- W221's collapse bridge restated with the exact homotopy-invariance input isolated. -/
theorem exactAcyclicHomotopyObject_isClosedUnderIsomorphisms_of_homotopyEquivTransport
    (transport : ExactAcyclicTransportOfHomotopyEquiv C) :
    (exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms :=
  exactAcyclicHomotopyObject_isClosedUnderIsomorphisms_of_isoClosureCollapse C
    (exactAcyclicIsoClosureCollapse_of_homotopyEquivTransport C transport)

/-- Conversely, the iso-closure collapse recovers transport along `HomotopyEquiv`. -/
theorem exactAcyclicTransportOfHomotopyEquiv_of_isoClosureCollapse
    (h : ExactAcyclicIsoClosureCollapse C) :
    ExactAcyclicTransportOfHomotopyEquiv C := by
  letI : (exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms :=
    exactAcyclicHomotopyObject_isClosedUnderIsomorphisms_of_isoClosureCollapse C h
  intro K L hK e
  exact exactAcyclicTransportOfHomotopyEquiv_of_isClosedUnderIsomorphisms C hK e

/--
Named missing theorem for a full product-success route.

The local exact-category API has `exactAcyclic_of_iso` for strict cochain isomorphisms, but
no theorem currently upgrades a chain homotopy equivalence to degreewise conflations.
-/
def exactAcyclicHomotopyInvarianceTheoremNeeded : String :=
  "exactAcyclic_of_homotopyEquiv : exactAcyclic C K -> HomotopyEquiv K L -> exactAcyclic C L"

/-- Compact route status for external review. -/
def exactAcyclicHomotopyEquivTransportStatus : List String :=
  ["proved: transport is enough for W221 iso-closure collapse",
    "proved: iso-closed exactAcyclicHomotopyObject recovers transport along HomotopyEquiv",
    "missing: exactAcyclic_of_homotopyEquiv for the local Quillen exact-category API"]

theorem exactAcyclicHomotopyEquivTransportStatus_count :
    exactAcyclicHomotopyEquivTransportStatus.length = 3 := rfl

section Checks

#check ExactAcyclicTransportOfHomotopyEquiv
#check ExactAcyclicIsoClosureCollapse
#check exactAcyclicTransportOfHomotopyEquiv_of_isClosedUnderIsomorphisms
#check exactAcyclicIsoClosureCollapse_of_homotopyEquivTransport
#check exactAcyclicHomotopyObject_isClosedUnderIsomorphisms_of_isoClosureCollapse
#check exactAcyclicHomotopyObject_isClosedUnderIsomorphisms_of_homotopyEquivTransport
#check exactAcyclicTransportOfHomotopyEquiv_of_isoClosureCollapse
#check exactAcyclicHomotopyInvarianceTheoremNeeded
#check exactAcyclicHomotopyEquivTransportStatus
#check exactAcyclicHomotopyEquivTransportStatus_count
#check exactAcyclic_of_iso
#check HomotopyCategory.isoOfHomotopyEquiv
#check HomotopyCategory.homotopyEquivOfIso

end Checks

end ExactAcyclicHomotopyEquivTransportW225

end LeanLCAExactChallenge
