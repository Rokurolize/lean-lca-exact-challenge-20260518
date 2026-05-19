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

Current product boundary: mathlib also has ordinary triangulated-localization
machinery, but the local `Dbounded` construction has not supplied the
preadditive, zero-object, shift, pretriangulated, and triangulated structures
needed to use that machinery, and mathlib does not provide a stable
infinity-category API that would turn this ordinary nerve into a stable
enhancement.
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
#check CategoryTheory.Triangulated.Localization.pretriangulated
#check CategoryTheory.Triangulated.Localization.isTriangulated

end LeanLCAExactChallenge
