import LeanLCAExactChallenge.Derived.Bounded

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

#check Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstances
#check Dbounded.metrizableStableInstanceFieldNames
#check Dbounded.metrizableStableInstanceFieldNames_count

#synth Preadditive (Dbounded MetrizableLCA.{0})
#synth HasFiniteLimits (Dbounded MetrizableLCA.{0})
#synth HasFiniteColimits (Dbounded MetrizableLCA.{0})
#synth HasZeroObject (Dbounded MetrizableLCA.{0})
#synth ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive
#synth Pretriangulated (Dbounded MetrizableLCA.{0})
#synth IsTriangulated (Dbounded MetrizableLCA.{0})

example :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstances

end LeanLCAExactChallenge
