import LeanLCAExactChallenge.Derived.BoundedFiniteProducts

/-!
W273 boundary for the exact-acyclic homotopy-object iso-closed input.

The v291 identity-containment frontier names
`(exactAcyclicHomotopyObject MetrizableLCA).IsClosedUnderIsomorphisms` as the remaining
input. W221/W225 reduce that input to transport of `exactAcyclic` along strict homotopy
equivalences of selected cochain complexes; W229 identifies a homology/quasi-isomorphism
route toward that transport theorem. This file keeps the target concrete for
`MetrizableLCA` and records the smallest checked consumer of the remaining input.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace ExactAcyclicIsoClosedW273

/-- The exact v291 iso-closed input, specialized to the concrete `MetrizableLCA` target. -/
abbrev MetrizableLCAIsoClosedInput : Prop :=
  (exactAcyclicHomotopyObject MetrizableLCA.{0}).IsClosedUnderIsomorphisms

/-- Exact acyclicity transported along homotopy equivalences of selected cochain complexes. -/
abbrev MetrizableLCAExactAcyclicTransportOfHomotopyEquiv : Prop :=
  ∀ {K L : CochainComplex MetrizableLCA.{0} ℤ},
    exactAcyclic MetrizableLCA K → HomotopyEquiv K L → exactAcyclic MetrizableLCA L

/-- The explicit iso-closure collapse for the concrete `MetrizableLCA` target. -/
abbrev MetrizableLCAExactAcyclicIsoClosureCollapse : Prop :=
  exactAcyclicHomotopyIsoClosure MetrizableLCA.{0} ≤
    exactAcyclicHomotopyObject MetrizableLCA.{0}

/-- Homotopy-equivalence transport collapses the explicit homotopy-category iso-closure. -/
theorem metrizableLCA_exactAcyclicIsoClosureCollapse_of_homotopyEquivTransport
    (transport : MetrizableLCAExactAcyclicTransportOfHomotopyEquiv) :
    MetrizableLCAExactAcyclicIsoClosureCollapse := by
  change exactAcyclicHomotopyIsoClosure MetrizableLCA.{0} ≤
    exactAcyclicHomotopyObject MetrizableLCA.{0}
  intro X hX
  rcases hX with ⟨Y, hY, ⟨e⟩⟩
  obtain ⟨X₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨Y₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  exact transport hY (HomotopyCategory.homotopyEquivOfIso e.symm)

/-- The iso-closure collapse is exactly the requested `IsClosedUnderIsomorphisms` input. -/
theorem metrizableLCA_isoClosedInput_of_isoClosureCollapse
    (h : MetrizableLCAExactAcyclicIsoClosureCollapse) :
    MetrizableLCAIsoClosedInput := by
  change (exactAcyclicHomotopyObject MetrizableLCA.{0}).IsClosedUnderIsomorphisms
  rw [ObjectProperty.isClosedUnderIsomorphisms_iff_isoClosure_eq_self]
  apply le_antisymm
  · exact h
  · exact ObjectProperty.le_isoClosure (exactAcyclicHomotopyObject MetrizableLCA.{0})

/--
Checked reduction of the v291 input: homotopy-equivalence transport supplies the exact
`MetrizableLCA` iso-closed instance.
-/
theorem metrizableLCA_isoClosedInput_of_homotopyEquivTransport
    (transport : MetrizableLCAExactAcyclicTransportOfHomotopyEquiv) :
    MetrizableLCAIsoClosedInput :=
  metrizableLCA_isoClosedInput_of_isoClosureCollapse
    (metrizableLCA_exactAcyclicIsoClosureCollapse_of_homotopyEquivTransport transport)

/--
Minimal consumer for the current frontier. If the v291 input is supplied under the named
alias, this theorem returns the exact instance wanted by downstream identity-containment
lemmas.
-/
theorem metrizableLCA_exactAcyclicHomotopyObject_isClosedUnderIsomorphisms
    (h : MetrizableLCAIsoClosedInput) :
    (exactAcyclicHomotopyObject MetrizableLCA.{0}).IsClosedUnderIsomorphisms :=
  h

/-- Remaining declaration names for turning this boundary into an unconditional result. -/
def remainingInputs : List String :=
  ["exactAcyclic_of_homotopyEquiv_metrizableLCA : exactAcyclic MetrizableLCA K -> HomotopyEquiv K L -> exactAcyclic MetrizableLCA L"]

theorem remainingInputs_count : remainingInputs.length = 1 := rfl

section Checks

#check MetrizableLCAIsoClosedInput
#check MetrizableLCAExactAcyclicTransportOfHomotopyEquiv
#check MetrizableLCAExactAcyclicIsoClosureCollapse
#check metrizableLCA_exactAcyclicIsoClosureCollapse_of_homotopyEquivTransport
#check metrizableLCA_isoClosedInput_of_isoClosureCollapse
#check metrizableLCA_isoClosedInput_of_homotopyEquivTransport
#check metrizableLCA_exactAcyclicHomotopyObject_isClosedUnderIsomorphisms
#check remainingInputs
#check remainingInputs_count
#check HomotopyCategory.homotopyEquivOfIso

end Checks

end ExactAcyclicIsoClosedW273

end LeanLCAExactChallenge
