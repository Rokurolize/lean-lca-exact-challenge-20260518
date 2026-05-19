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

Incremental v76 progress: the bounded cochain-complex full subcategory is now
closed under isomorphism and cochain shift, so it has the shift and additive
shift functors needed as prerequisites for a homotopy-category/Verdier route.
This is only groundwork; it is not yet a stable infinity-category certificate.
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
#check BoundedComplexCategory
#check BoundedComplexCategory.ι
#check boundedCochainComplex_isClosedUnderIsomorphisms
#check boundedCochainComplex_isStableUnderShift
#check boundedExactWeakEquivalence
#check exactAcyclic_of_iso

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C] :
    HasShift (BoundedComplexCategory C) ℤ := by
  infer_instance

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C] :
    (shiftFunctor (BoundedComplexCategory C) (1 : ℤ)).Additive := by
  infer_instance

#check (Dbounded (C := MetrizableLCA))
#check Dbounded.localization
#check Dbounded.infinityCategory
#check Dbounded.infinityNerve
#check Dbounded.infinityNerve_quasicategory
#check Dbounded.homotopyCategoryIso
#check CategoryTheory.Triangulated.Localization.pretriangulated
#check CategoryTheory.Triangulated.Localization.isTriangulated

end LeanLCAExactChallenge
