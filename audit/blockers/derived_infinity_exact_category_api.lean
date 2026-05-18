import LeanLCAExactChallenge.Derived.Bounded

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

/--
Missing local theorem/API: a bounded derived infinity-category construction for
an arbitrary Quillen exact category.
-/
def missing_bounded_derived_infinity_statement
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C] : Prop :=
  Nonempty (BoundedDerivedInfinityCategory C)

end LeanLCAExactChallenge
