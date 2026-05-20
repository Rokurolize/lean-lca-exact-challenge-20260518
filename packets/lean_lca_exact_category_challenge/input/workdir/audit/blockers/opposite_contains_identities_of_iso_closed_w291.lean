import LeanLCAExactChallenge.Derived.Bounded

/-!
W291 audit: opposite bounded weak equivalences contain identities under the
existing exact-acyclic homotopy iso-closed input.

The W266 opposite finite-limit assembly kept
`((boundedExactWeakEquivalence MetrizableLCA).op).ContainsIdentities` as an
explicit field.  The new source instance
`boundedExactWeakEquivalence_containsIdentities_of_isoClosed` reduces that field
to the already-known exact-acyclic homotopy isomorphism-closure input.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace OppositeContainsIdentitiesOfIsoClosedW291

theorem boundedExactWeakEquivalence_containsIdentities_from_isoClosed
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms] :
    (boundedExactWeakEquivalence C).ContainsIdentities := by
  infer_instance

theorem boundedExactWeakEquivalence_op_containsIdentities_from_isoClosed
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms] :
    ((boundedExactWeakEquivalence C).op).ContainsIdentities := by
  infer_instance

theorem metrizableLCA_oppositeContainsIdentities_from_isoClosed
    [(exactAcyclicHomotopyObject MetrizableLCA.{0}).IsClosedUnderIsomorphisms] :
    ((boundedExactWeakEquivalence MetrizableLCA.{0}).op).ContainsIdentities :=
  boundedExactWeakEquivalence_op_containsIdentities_from_isoClosed
    (C := MetrizableLCA.{0})

structure OppositeContainsIdentitiesState : Type where
  reducedInput : String
  remainingInput : String
  productSuccessClaimed : Bool

def currentOppositeContainsIdentitiesState : OppositeContainsIdentitiesState where
  reducedInput :=
    "((boundedExactWeakEquivalence MetrizableLCA).op).ContainsIdentities"
  remainingInput :=
    "(exactAcyclicHomotopyObject MetrizableLCA).IsClosedUnderIsomorphisms"
  productSuccessClaimed := false

theorem currentOppositeContainsIdentitiesState_productSuccess :
    currentOppositeContainsIdentitiesState.productSuccessClaimed = false := rfl

section Checks

#check boundedExactWeakEquivalence_containsIdentities_of_isoClosed
#check boundedExactWeakEquivalence_containsIdentities_from_isoClosed
#check boundedExactWeakEquivalence_op_containsIdentities_from_isoClosed
#check metrizableLCA_oppositeContainsIdentities_from_isoClosed
#check currentOppositeContainsIdentitiesState_productSuccess

end Checks

end OppositeContainsIdentitiesOfIsoClosedW291

end LeanLCAExactChallenge
