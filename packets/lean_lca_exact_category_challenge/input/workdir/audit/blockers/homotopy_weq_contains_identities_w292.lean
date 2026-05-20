import LeanLCAExactChallenge.Derived.Bounded

/-!
W292 audit: the isomorphism-closed homotopy/Verdier bounded weak-equivalence
class contains identities unconditionally.

This is not the same as the direct mapping-cone class
`boundedExactWeakEquivalence`.  It records a stronger ready-to-use identity
input for routes that are allowed to work with
`boundedHomotopyExactWeakEquivalence`; the W266 direct opposite finite-limit
assembly still needs either direct identity containment or a formal bridge that
replaces the direct class by this isomorphism-closed Verdier class.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace HomotopyWeqContainsIdentitiesW292

theorem boundedHomotopyExactWeakEquivalence_containsIdentities_direct
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] :
    (boundedHomotopyExactWeakEquivalence C).ContainsIdentities := by
  infer_instance

theorem boundedHomotopyExactWeakEquivalence_op_containsIdentities
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] :
    ((boundedHomotopyExactWeakEquivalence C).op).ContainsIdentities := by
  infer_instance

theorem metrizableLCA_homotopyWeq_op_containsIdentities :
    ((boundedHomotopyExactWeakEquivalence MetrizableLCA.{0}).op).ContainsIdentities :=
  boundedHomotopyExactWeakEquivalence_op_containsIdentities
    (C := MetrizableLCA.{0})

structure HomotopyIdentityState : Type where
  solvedInput : String
  remainingDirectInput : String
  productSuccessClaimed : Bool

def currentHomotopyIdentityState : HomotopyIdentityState where
  solvedInput :=
    "((boundedHomotopyExactWeakEquivalence MetrizableLCA).op).ContainsIdentities"
  remainingDirectInput :=
    "((boundedExactWeakEquivalence MetrizableLCA).op).ContainsIdentities or a checked replacement of W266 by the homotopy/Verdier class"
  productSuccessClaimed := false

theorem currentHomotopyIdentityState_productSuccess :
    currentHomotopyIdentityState.productSuccessClaimed = false := rfl

section Checks

#check boundedHomotopyExactWeakEquivalence_containsIdentities
#check boundedHomotopyExactWeakEquivalence_containsIdentities_direct
#check boundedHomotopyExactWeakEquivalence_op_containsIdentities
#check metrizableLCA_homotopyWeq_op_containsIdentities
#check currentHomotopyIdentityState_productSuccess

end Checks

end HomotopyWeqContainsIdentitiesW292

end LeanLCAExactChallenge
