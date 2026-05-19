import LeanLCAExactChallenge.Derived.Bounded

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]

/-- The direct transport theorem tested by the counterexample probe.

This is deliberately stronger than the currently implemented strict-isomorphism transport
for `boundedCochainComplex`: it asks strict cochain boundedness to survive an arbitrary
homotopy equivalence. -/
abbrev boundedCochainComplex_transportOfHomotopyEquivUnsafe : Prop :=
  ∀ {K L : CochainComplex C ℤ},
    boundedCochainComplex C K →
    HomotopyEquiv K L →
    boundedCochainComplex C L

/-- Minimal formal shape of a counterexample to homotopy-equivalence transport of strict
boundedness: a bounded complex homotopy equivalent to an unbounded selected complex. -/
abbrev boundedHomotopyTransportCounterexample : Prop :=
  ∃ (K L : CochainComplex C ℤ),
    boundedCochainComplex C K ∧
    ¬ boundedCochainComplex C L ∧
    Nonempty (HomotopyEquiv K L)

omit [QuillenExactCategory C] in
/-- Any bounded/unbounded homotopy-equivalence counterexample refutes the direct transport
theorem. -/
theorem not_transport_of_boundedHomotopyTransportCounterexample
    (h : boundedHomotopyTransportCounterexample C) :
    ¬ boundedCochainComplex_transportOfHomotopyEquivUnsafe C := by
  intro transport
  rcases h with ⟨K, L, hK, hL, ⟨η⟩⟩
  exact hL (transport hK η)

/-- Contractible-tail shape behind the expected example.

The intended model takes `L` to be `K` plus a contractible tail with nonzero terms outside
every finite cochain range. The local API already gives strict-isomorphism transport for
boundedness, so such a tail cannot be removed by `ObjectProperty.prop_of_iso`; it must be
removed only up to homotopy. The final field records that homotopy-equivalence removal. -/
abbrev unboundedContractibleTailSketch [HasZeroObject C] : Prop :=
  ∃ (K Tail L : CochainComplex C ℤ),
    boundedCochainComplex C K ∧
    ¬ boundedCochainComplex C L ∧
    Nonempty (HomotopyEquiv Tail (0 : CochainComplex C ℤ)) ∧
    Nonempty (HomotopyEquiv K L)

omit [QuillenExactCategory C] in
/-- A contractible unbounded tail sketch specializes to the minimal counterexample shape. -/
theorem boundedHomotopyTransportCounterexample_of_unboundedContractibleTailSketch
    [HasZeroObject C] (h : unboundedContractibleTailSketch C) :
    boundedHomotopyTransportCounterexample C := by
  rcases h with ⟨K, _Tail, L, hK, hL, _hTail, η⟩
  exact ⟨K, L, hK, hL, η⟩

omit [QuillenExactCategory C] in
/-- Consequently, the contractible-tail shape also refutes direct boundedness transport
along `HomotopyEquiv`. -/
theorem not_transport_of_unboundedContractibleTailSketch
    [HasZeroObject C] (h : unboundedContractibleTailSketch C) :
    ¬ boundedCochainComplex_transportOfHomotopyEquivUnsafe C :=
  not_transport_of_boundedHomotopyTransportCounterexample C
    (boundedHomotopyTransportCounterexample_of_unboundedContractibleTailSketch C h)

#check boundedCochainComplex_isClosedUnderIsomorphisms
#check boundedCochainComplex_transportOfHomotopyEquivUnsafe
#check boundedHomotopyTransportCounterexample
#check not_transport_of_boundedHomotopyTransportCounterexample
#check unboundedContractibleTailSketch
#check boundedHomotopyTransportCounterexample_of_unboundedContractibleTailSketch
#check not_transport_of_unboundedContractibleTailSketch
#check HomotopyEquiv
#check HomotopyCategory.homotopyEquivOfIso

end LeanLCAExactChallenge
