import LeanLCAExactChallenge.Derived.Bounded

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

/--
Resolved local API boundary: a bounded derived localization is available for
Quillen exact categories whose underlying category has binary biproducts, so
mapping cones can be formed.
-/
def bounded_derived_localization_family
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] :=
  BoundedDerivedInfinityCategory C

#check bounded_derived_localization_family
#check boundedExactWeakEquivalence
#check (Dbounded (C := MetrizableLCA))
#check Dbounded.localization

end LeanLCAExactChallenge
