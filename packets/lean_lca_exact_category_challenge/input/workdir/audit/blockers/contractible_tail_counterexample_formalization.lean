import LeanLCAExactChallenge.Derived.Bounded

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]

/-- Degreewise evidence that a cochain representative has nonzero terms arbitrarily far to
the right. This is the strict support obstruction expected from an unbounded contractible
tail. -/
abbrev HasUpperUnboundedNonzeroTerms (K : CochainComplex C ℤ) : Prop :=
  ∀ b : ℤ, ∃ i : ℤ, b < i ∧ ¬ IsZero (K.X i)

omit [QuillenExactCategory C] in
/-- A representative with nonzero terms arbitrarily far to the right is not strictly
bounded as a cochain complex. -/
theorem not_boundedCochainComplex_of_hasUpperUnboundedNonzeroTerms
    {K : CochainComplex C ℤ} (hK : HasUpperUnboundedNonzeroTerms C K) :
    ¬ boundedCochainComplex C K := by
  intro hBounded
  rcases hBounded with ⟨_a, b, _hge, hle⟩
  rcases hK b with ⟨i, hi, hNotZero⟩
  letI : K.IsStrictlyLE b := hle
  exact hNotZero (K.isZero_of_isStrictlyLE b i hi)

/-- The direct theorem shape that would incorrectly transport strict boundedness across an
arbitrary homotopy equivalence. -/
abbrev StrictBoundednessTransportOfHomotopyEquiv : Prop :=
  ∀ {K L : CochainComplex C ℤ},
    boundedCochainComplex C K →
    HomotopyEquiv K L →
    boundedCochainComplex C L

omit [QuillenExactCategory C] in
/-- The zero cochain complex is strictly bounded. This gives the bounded representative
for the smaller w86 counterexample shape. -/
theorem boundedCochainComplex_zero [HasZeroObject C] :
    boundedCochainComplex C (0 : CochainComplex C ℤ) :=
  ⟨0, 0, inferInstance, inferInstance⟩

/-- Minimal tail instance needed to refute bare strict-boundedness transport along
`HomotopyEquiv`: a single right-unbounded selected complex homotopy equivalent to zero. -/
structure UnboundedContractibleTailInstance [HasZeroObject C] where
  tail : CochainComplex C ℤ
  tail_upper_unbounded : HasUpperUnboundedNonzeroTerms C tail
  tail_contractible : Nonempty (HomotopyEquiv tail (0 : CochainComplex C ℤ))

omit [QuillenExactCategory C] in
/-- A single unbounded contractible selected tail already refutes bare strict-boundedness
transport along homotopy equivalence, using the zero complex as the bounded source. -/
theorem not_strictBoundednessTransport_of_unboundedContractibleTailInstance
    [HasZeroObject C] (T : UnboundedContractibleTailInstance C) :
    ¬ StrictBoundednessTransportOfHomotopyEquiv C := by
  intro transport
  rcases T.tail_contractible with ⟨e⟩
  exact not_boundedCochainComplex_of_hasUpperUnboundedNonzeroTerms C
    T.tail_upper_unbounded (transport (boundedCochainComplex_zero C) e.symm)

/-- Formal data required from a concrete contractible-tail construction.

The intended example takes `modelWithTail` to be a bounded representative with an attached
contractible tail. The tail itself is recorded as contractible, while the selected
representative `modelWithTail` has explicit degreewise nonzero terms arbitrarily far to
the right. -/
structure ContractibleTailCounterexampleData [HasZeroObject C] where
  boundedRepresentative : CochainComplex C ℤ
  contractibleTail : CochainComplex C ℤ
  modelWithTail : CochainComplex C ℤ
  boundedRepresentative_bounded : boundedCochainComplex C boundedRepresentative
  tail_contractible : Nonempty (HomotopyEquiv contractibleTail (0 : CochainComplex C ℤ))
  modelWithTail_upper_unbounded : HasUpperUnboundedNonzeroTerms C modelWithTail
  boundedRepresentative_homotopy_equiv :
    Nonempty (HomotopyEquiv boundedRepresentative modelWithTail)

omit [QuillenExactCategory C] in
/-- The explicit right-unbounded support field converts the tail package into a strict
boundedness failure for the selected representative. -/
theorem ContractibleTailCounterexampleData.modelWithTail_not_bounded
    [HasZeroObject C] (D : ContractibleTailCounterexampleData C) :
    ¬ boundedCochainComplex C D.modelWithTail :=
  not_boundedCochainComplex_of_hasUpperUnboundedNonzeroTerms C
    D.modelWithTail_upper_unbounded

omit [QuillenExactCategory C] in
/-- Any concrete contractible-tail package refutes bare strict-boundedness transport along
`HomotopyEquiv`. -/
theorem not_strictBoundednessTransport_of_contractibleTailCounterexampleData
    [HasZeroObject C] (D : ContractibleTailCounterexampleData C) :
    ¬ StrictBoundednessTransportOfHomotopyEquiv C := by
  intro transport
  rcases D.boundedRepresentative_homotopy_equiv with ⟨e⟩
  exact ContractibleTailCounterexampleData.modelWithTail_not_bounded C D
    (transport D.boundedRepresentative_bounded e)

/-- Minimal API still needed to construct the concrete example rather than only consume
its data: attach a contractible tail to a bounded representative, prove the resulting
selected complex is right-unbounded, and produce the homotopy equivalence back to the
bounded representative. -/
structure ContractibleTailAttachmentAPI [HasZeroObject C] where
  attach : CochainComplex C ℤ → CochainComplex C ℤ → CochainComplex C ℤ
  attach_upper_unbounded :
    ∀ {K Tail : CochainComplex C ℤ},
      HasUpperUnboundedNonzeroTerms C Tail →
      HasUpperUnboundedNonzeroTerms C (attach K Tail)
  attach_contractible_equiv :
    ∀ {K Tail : CochainComplex C ℤ},
      Nonempty (HomotopyEquiv Tail (0 : CochainComplex C ℤ)) →
      Nonempty (HomotopyEquiv K (attach K Tail))

omit [QuillenExactCategory C] in
/-- The missing attachment API would turn an unbounded contractible tail and any bounded
representative into counterexample data. -/
def ContractibleTailAttachmentAPI.counterexampleData
    [HasZeroObject C] (A : ContractibleTailAttachmentAPI C)
    {K Tail : CochainComplex C ℤ}
    (hK : boundedCochainComplex C K)
    (hTailUnbounded : HasUpperUnboundedNonzeroTerms C Tail)
    (hTailContractible : Nonempty (HomotopyEquiv Tail (0 : CochainComplex C ℤ))) :
    ContractibleTailCounterexampleData C where
  boundedRepresentative := K
  contractibleTail := Tail
  modelWithTail := A.attach K Tail
  boundedRepresentative_bounded := hK
  tail_contractible := hTailContractible
  modelWithTail_upper_unbounded := A.attach_upper_unbounded hTailUnbounded
  boundedRepresentative_homotopy_equiv :=
    A.attach_contractible_equiv hTailContractible

omit [QuillenExactCategory C] in
/-- The general attachment API specializes to the minimal w86 tail instance by attaching
an unbounded contractible tail to the zero complex. -/
noncomputable def ContractibleTailAttachmentAPI.unboundedTailInstance
    [HasZeroObject C] (A : ContractibleTailAttachmentAPI C)
    {Tail : CochainComplex C ℤ}
    (hTailUnbounded : HasUpperUnboundedNonzeroTerms C Tail)
    (hTailContractible : Nonempty (HomotopyEquiv Tail (0 : CochainComplex C ℤ))) :
    UnboundedContractibleTailInstance C where
  tail := A.attach (0 : CochainComplex C ℤ) Tail
  tail_upper_unbounded := A.attach_upper_unbounded hTailUnbounded
  tail_contractible := by
    rcases A.attach_contractible_equiv (K := (0 : CochainComplex C ℤ)) hTailContractible with ⟨e⟩
    exact ⟨e.symm⟩

#check HasUpperUnboundedNonzeroTerms
#check not_boundedCochainComplex_of_hasUpperUnboundedNonzeroTerms
#check StrictBoundednessTransportOfHomotopyEquiv
#check boundedCochainComplex_zero
#check UnboundedContractibleTailInstance
#check not_strictBoundednessTransport_of_unboundedContractibleTailInstance
#check ContractibleTailCounterexampleData
#check ContractibleTailCounterexampleData.modelWithTail_not_bounded
#check not_strictBoundednessTransport_of_contractibleTailCounterexampleData
#check ContractibleTailAttachmentAPI
#check ContractibleTailAttachmentAPI.counterexampleData
#check ContractibleTailAttachmentAPI.unboundedTailInstance
#check HomotopyEquiv
#check HomotopyEquiv.symm

end LeanLCAExactChallenge
