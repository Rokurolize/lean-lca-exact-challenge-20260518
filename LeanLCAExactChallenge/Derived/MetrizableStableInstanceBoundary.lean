import LeanLCAExactChallenge.Derived.BoundedFiniteProducts

/-!
Canonical boundary for the default-universe `Dbounded MetrizableLCA` stable package.

This module does not add a new route. It exposes the current shortest source-facing boundary:
direct bounded left calculus plus walking-parallel-pair transfer-stable inputs produce the
bounded-derived infinity-category package.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- Boundary inputs that remain for the canonical `Dbounded MetrizableLCA` stable package. -/
def metrizableStableInstanceBoundaryRemainingInputNames : List String :=
  Dbounded.metrizableWppTransferStableSemanticInputNames

/-- The stable-instance boundary has four remaining input families. -/
theorem metrizableStableInstanceBoundaryRemainingInputNames_count :
    Dbounded.metrizableStableInstanceBoundaryRemainingInputNames.length = 4 :=
  Dbounded.metrizableWppTransferStableSemanticInputNames_count

/-- Semantic fields produced once the stable-instance boundary inputs are supplied. -/
def metrizableStableInstanceBoundaryDerivedFieldNames : List String :=
  ["Preadditive (Dbounded MetrizableLCA)",
    "HasZeroObject (Dbounded MetrizableLCA)",
    "forall n, (shiftFunctor (Dbounded MetrizableLCA) n).Additive",
    "HasFiniteProducts (Dbounded MetrizableLCA)",
    "HasFiniteLimits (Dbounded MetrizableLCA)",
    "HasFiniteColimits (Dbounded MetrizableLCA)",
    "BoundedDerivedInfinityCategory MetrizableLCA"]

/-- The boundary supplies seven derived semantic or package fields once its inputs exist. -/
theorem metrizableStableInstanceBoundaryDerivedFieldNames_count :
    Dbounded.metrizableStableInstanceBoundaryDerivedFieldNames.length = 7 :=
  rfl

/--
The canonical bounded-derived infinity-category package from direct bounded left calculus and
walking-parallel-pair transfer-stable inputs.
-/
noncomputable def boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundary
    [(boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions]
    (inputs :
      Dbounded.MetrizableWalkingParallelPairTransferStableSemanticInputs
        Dbounded.metrizableLeftCalculusSemanticFields) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  Dbounded.boundedDerivedInfinityCategoryOfMetrizableOrdinaryInput
    (Dbounded.metrizableOrdinaryStableSemanticInputOfWalkingParallelPairTransfer
      inputs)

/-- Current boundary marker: the source exposes the path, but no input inhabitant is supplied. -/
def currentMetrizableStableInstanceBoundaryProductSuccessClaimed : Bool :=
  false

theorem currentMetrizableStableInstanceBoundary_productSuccess :
    Dbounded.currentMetrizableStableInstanceBoundaryProductSuccessClaimed = false :=
  rfl

section Checks

#check Dbounded.metrizableStableInstanceBoundaryRemainingInputNames
#check Dbounded.metrizableStableInstanceBoundaryRemainingInputNames_count
#check Dbounded.metrizableStableInstanceBoundaryDerivedFieldNames
#check Dbounded.metrizableStableInstanceBoundaryDerivedFieldNames_count
#check Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundary
#check Dbounded.currentMetrizableStableInstanceBoundary_productSuccess

end Checks

end Dbounded

end LeanLCAExactChallenge
