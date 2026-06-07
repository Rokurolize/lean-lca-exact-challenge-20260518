import LeanLCAExactChallenge.BoundedDerived.Basic

/-!
Bounded proof-search probe for the original task 4 final surface.

This file is expected to fail until the concrete stable categorical instances for
`Dbounded MetrizableLCA` are available. It is a source-patch-needed witness, not
a repository source module.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

#check Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstances
#check Dbounded.metrizableStableInstanceFieldNames_count

noncomputable def attemptedOriginalFourTaskStablePackage :
    BoundedDerived.Metrizable.StablePackage :=
  Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstances

#check (inferInstance : Preadditive (Dbounded MetrizableLCA.{0}))
#check (inferInstance : HasFiniteLimits (Dbounded MetrizableLCA.{0}))
#check (inferInstance : HasFiniteColimits (Dbounded MetrizableLCA.{0}))
#check (inferInstance : HasZeroObject (Dbounded MetrizableLCA.{0}))
#check (inferInstance :
    ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive)
#check (inferInstance : Pretriangulated (Dbounded MetrizableLCA.{0}))
#check (inferInstance : IsTriangulated (Dbounded MetrizableLCA.{0}))

end LeanLCAExactChallenge
