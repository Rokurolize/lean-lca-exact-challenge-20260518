import LeanLCAExactChallenge.AlternatingTailExtendTransport

/-!
Concrete contractible right-tail evidence for strict boundedness checks.

This module records the selected-complex phenomenon behind the alternating tail:
a cochain complex may be homotopy equivalent to zero while still having nonzero
terms arbitrarily far to the right. The statement is intentionally about
strict support of the chosen cochain complex, not about equality in a localized
or homotopy category.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- Degreewise evidence that a cochain complex has nonzero terms arbitrarily far to the right. -/
abbrev RightUnboundedNonzeroTerms (K : CochainComplex C ℤ) : Prop :=
  ∀ b : ℤ, ∃ i : ℤ, b < i ∧ ¬ IsZero (K.X i)

/-- A cochain complex with nonzero terms arbitrarily far to the right is not strictly bounded. -/
theorem not_boundedCochainComplex_of_rightUnboundedNonzeroTerms
    {K : CochainComplex C ℤ} (hK : RightUnboundedNonzeroTerms C K) :
    ¬ boundedCochainComplex C K := by
  intro hBounded
  rcases hBounded with ⟨_a, b, _hge, hle⟩
  rcases hK b with ⟨i, hi, hNotZero⟩
  letI : K.IsStrictlyLE b := hle
  exact hNotZero (K.isZero_of_isStrictlyLE b i hi)

/-- The zero cochain complex is strictly bounded. -/
theorem boundedCochainComplex_zero [HasZeroObject C] :
    boundedCochainComplex C (0 : CochainComplex C ℤ) :=
  ⟨0, 0, inferInstance, inferInstance⟩

/-- A single selected complex that is right-unbounded but homotopy equivalent to zero. -/
structure RightUnboundedContractibleComplex [HasZeroObject C] where
  complex : CochainComplex C ℤ
  rightUnbounded : RightUnboundedNonzeroTerms C complex
  equivalentZero : Nonempty (HomotopyEquiv complex (0 : CochainComplex C ℤ))

/-- A contracting homotopy from the identity to zero gives a homotopy equivalence to zero. -/
noncomputable def homotopyEquivZeroOfContractingHomotopy {ι : Type*} {C : Type*}
    [Category C] [Preadditive C] [HasZeroObject C]
    {c : ComplexShape ι} (K : HomologicalComplex C c)
    (h : Homotopy (𝟙 K) (0 : K ⟶ K)) :
    HomotopyEquiv K (0 : HomologicalComplex C c) where
  hom := 0
  inv := 0
  homotopyHomInvId := by
    simpa using h.symm
  homotopyInvHomId := Homotopy.ofEq (by simp)

/-- Nonempty wrapper for consumers that only need existence of a zero equivalence. -/
theorem nonemptyHomotopyEquivZeroOfContractingHomotopy {ι : Type*} {C : Type*}
    [Category C] [Preadditive C] [HasZeroObject C]
    {c : ComplexShape ι} (K : HomologicalComplex C c)
    (h : Homotopy (𝟙 K) (0 : K ⟶ K)) :
    Nonempty (HomotopyEquiv K (0 : HomologicalComplex C c)) :=
  ⟨homotopyEquivZeroOfContractingHomotopy K h⟩

/-- The over-strong statement that strict boundedness transports along arbitrary
homotopy equivalence. -/
abbrev StrictBoundednessTransportOfHomotopyEquiv : Prop :=
  ∀ {K L : CochainComplex C ℤ},
    boundedCochainComplex C K →
    HomotopyEquiv K L →
    boundedCochainComplex C L

/-- A right-unbounded contractible selected complex refutes transport of strict support. -/
theorem not_strictBoundednessTransport_of_rightUnboundedContractibleComplex
    [HasZeroObject C] (T : RightUnboundedContractibleComplex C) :
    ¬ StrictBoundednessTransportOfHomotopyEquiv C := by
  intro transport
  rcases T.equivalentZero with ⟨e⟩
  exact not_boundedCochainComplex_of_rightUnboundedNonzeroTerms C T.rightUnbounded
    (transport (boundedCochainComplex_zero C) e.symm)

namespace AlternatingTailExtendTransport

/-- The transported alternating tail is a concrete right-unbounded contractible complex. -/
noncomputable def intAlternatingTailGERightUnboundedContractible (p : ℤ) :
    RightUnboundedContractibleComplex IntModuleCat where
  complex := intAlternatingTailGE p
  rightUnbounded := intAlternatingTailGE_hasUpperUnboundedNonzeroTerms p
  equivalentZero :=
    nonemptyHomotopyEquivZeroOfContractingHomotopy (intAlternatingTailGE p)
      (intAlternatingTailGEContractingHomotopy p)

/-- The concrete transported alternating tail refutes over-strong strict-support transport. -/
theorem not_strictBoundednessTransport_intAlternatingTailGE (p : ℤ) :
    ¬ StrictBoundednessTransportOfHomotopyEquiv IntModuleCat :=
  not_strictBoundednessTransport_of_rightUnboundedContractibleComplex IntModuleCat
    (intAlternatingTailGERightUnboundedContractible p)

#check intAlternatingTailGERightUnboundedContractible
#check not_strictBoundednessTransport_intAlternatingTailGE
#check homotopyEquivZeroOfContractingHomotopy
#check nonemptyHomotopyEquivZeroOfContractingHomotopy

end AlternatingTailExtendTransport

end LeanLCAExactChallenge
