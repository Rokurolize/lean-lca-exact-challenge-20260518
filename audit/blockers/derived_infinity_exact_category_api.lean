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
preadditive, zero-object, pretriangulated, and triangulated structures
needed to use that machinery, and mathlib does not provide a stable
infinity-category API that would turn this ordinary nerve into a stable
enhancement.

Incremental v76 progress: the bounded cochain-complex full subcategory is now
closed under isomorphism and cochain shift, so it has the shift and additive
shift functors needed as prerequisites for a homotopy-category/Verdier route.
Incremental v77 progress: exact acyclicity, exact cone weak equivalences, and
the bounded exact weak-equivalence class are now invariant under cochain shifts,
so the ordinary localized category inherits the shift from mathlib's
localization API. This is still not a stable infinity-category certificate.
Incremental v78 progress: `MetrizableLCA` and the bounded complex full
subcategory now expose zero objects, and the derived file records that a real
left calculus of fractions for the exact weak equivalences would make mathlib
provide preadditivity, additivity of the localization functor, zero objects, and
additive localized shifts. The missing left-calculus/Verdier work is still a
product blocker.
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
#check boundedCochainComplex_containsZero
#check boundedComplexCategory_hasZeroObject
#check boundedExactWeakEquivalence
#check exactAcyclic_of_iso
#check exactAcyclic_shift
#check exactAcyclic_shift_iff
#check exactAcyclic_mappingCone_shift_iff
#check mappingConeIsoOfCommIso
#check exactAcyclic_mappingCone_congr_iff
#check exactAcyclicHomotopyObject
#check exactAcyclicHomotopyObject_quotient_obj_iff
#check exactAcyclicHomotopyObject_trW_quotient_map_of_exactAcyclic_mappingCone
#check boundedExactWeakEquivalence_shift_iff
#check boundedExactWeakEquivalence_isCompatibleWithShift
#check BoundedComplexCategory.homotopyQuotient
#check boundedExactWeakEquivalence_le_exactAcyclicHomotopy_trW_inverseImage
#check boundedExactWeakEquivalence_eq_exactAcyclicHomotopy_trW_inverseImage
#check exactAcyclicHomotopyObject_trW_hasLeftCalculusOfFractions_of_isTriangulated
#check Dbounded.preadditiveOfHasLeftCalculusOfFractions
#check Dbounded.localization_additiveOfHasLeftCalculusOfFractions
#check Dbounded.hasZeroObjectOfHasLeftCalculusOfFractions
#check Dbounded.shiftFunctor_additiveOfHasLeftCalculusOfFractions

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C] :
    HasShift (BoundedComplexCategory C) ℤ := by
  infer_instance

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] :
    HasZeroObject (BoundedComplexCategory C) := by
  infer_instance

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C] :
    (shiftFunctor (BoundedComplexCategory C) (1 : ℤ)).Additive := by
  infer_instance

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] :
    HasShift (Dbounded C) ℤ := by
  infer_instance

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] :
    (Dbounded.localization C).CommShift ℤ := by
  infer_instance

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    Preadditive (Dbounded C) :=
  Dbounded.preadditiveOfHasLeftCalculusOfFractions C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    (Dbounded.localization C).Additive :=
  Dbounded.localization_additiveOfHasLeftCalculusOfFractions C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] [HasZeroObject C]
    [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    HasZeroObject (Dbounded C) :=
  Dbounded.hasZeroObjectOfHasLeftCalculusOfFractions C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    (shiftFunctor (Dbounded C) (1 : ℤ)).Additive :=
  Dbounded.shiftFunctor_additiveOfHasLeftCalculusOfFractions C 1

#check (Dbounded (C := MetrizableLCA))
#check Dbounded.localization
#check Dbounded.infinityCategory
#check Dbounded.infinityNerve
#check Dbounded.infinityNerve_quasicategory
#check Dbounded.homotopyCategoryIso
#check CategoryTheory.Triangulated.Localization.pretriangulated
#check CategoryTheory.Triangulated.Localization.isTriangulated

end LeanLCAExactChallenge
