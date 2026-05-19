import LeanLCAExactChallenge.Derived.Bounded

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

/--
Resolved local API boundary: bounded derived localization and its quasicategory
nerve are available for Quillen exact categories whose underlying category has
binary biproducts, so mapping cones can be formed and the localized category can
be read as a quasicategory.
-/
def bounded_derived_localization_family
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] :=
  BoundedDerivedCategory C

noncomputable def bounded_derived_quasicategory_family
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] :=
  BoundedDerivedInfinityCategory C

#check bounded_derived_localization_family
#check bounded_derived_quasicategory_family
#check boundedExactWeakEquivalence
#check (Dbounded (C := MetrizableLCA))
#check Dbounded.localization
#check Dbounded.infinityCategory
#check Dbounded.infinityNerve
#check Dbounded.infinityNerve_quasicategory
#check Dbounded.homotopyCategoryIso

end LeanLCAExactChallenge
