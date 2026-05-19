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
Incremental v80 progress: exact acyclic homotopy objects now contain a zero
object, and their shift stability follows once homotopy-category isomorphism
invariance is proved. Thus the remaining path to `IsTriangulated` is narrowed to
isomorphism invariance plus distinguished-triangle closure, after which mathlib
supplies the Verdier left calculus of fractions for `trW`.
Incremental v82 progress: the direct bounded weak-equivalence class now maps by
the identity functor to the bounded pullback of the homotopy/Verdier `trW` class
for the isomorphism closure of exact acyclic homotopy objects. This pullback
class is shift-compatible and has its own ordinary localization, quasicategory
nerve, and comparison functor from `Dbounded`. This is still not a proof that the
direct weak-equivalence class has left calculus of fractions or that the
ordinary nerve is a stable infinity-category.
Incremental v83 progress: under the precise hypothesis that the isomorphism
closure of exact acyclic homotopy objects is `IsTriangulatedClosed₂`, mathlib's
Verdier localization API now supplies left calculus of fractions, triangulation
compatibility, preadditivity, a zero object, shifts, additive localized shifts,
and an ordinary triangulated category structure on the homotopy-category Verdier
quotient. This still does not prove that the direct bounded weak-equivalence
class has left calculus of fractions, nor does it produce a stable
infinity-category enhancement.
Incremental v84 progress: bounded cochain complexes are now closed under
mapping cones, and bounded objects are exposed as an isomorphism-closed, zero-
containing, shift-stable full subcategory of the homotopy category. This makes
the Verdier route's bounded ambient category more explicit, but it still does
not prove the exact-acyclic isomorphism closure is `IsTriangulatedClosed₂` or
produce a stable infinity-category enhancement.
Incremental v85 progress: under homotopy-category isomorphism invariance of
exact acyclicity, the identity localizer morphism from direct bounded exact weak
equivalences to homotopy/Verdier pullback weak equivalences is now a localized
equivalence, yielding an ordinary categorical equivalence from `Dbounded` to the
homotopy/Verdier pullback localization. This still depends on the isomorphism
invariance hypothesis and is not yet a stable infinity-category enhancement.
Incremental v86 progress: complexes whose every degreewise short complex
splits are exact acyclic, so bounded morphisms with degreewise split mapping
cones are weak equivalences for both the direct and homotopy/Verdier pullback
classes.
Incremental v87 progress: if a mapping cone is bounded, then both its source
and target complexes are bounded, and the corresponding homotopy-category
objects are bounded. This helps expose the bounded ambient part of cone
triangles but does not prove the exact-acyclic closure is triangulated.
Incremental v95 progress: the bounded homotopy/Verdier pullback localization
now has a comparison functor into the ordinary homotopy Verdier quotient, and
`Dbounded` has the composed comparison. This aligns the localization route but
does not transfer the conditional triangulated Verdier structure back to
`Dbounded`, nor produce a stable infinity-category enhancement.
Incremental v96 progress: the direct bounded exact weak-equivalence class now
has its own localizer morphism to the ordinary homotopy Verdier quotient, a
direct comparison functor, and canonical `CatCommSq` witnesses that the bounded
localization functors commute with these comparison routes. This still does not
prove the required calculus of fractions or stable infinity-category
enhancement.
Incremental v97 progress: the homotopy-route and direct-route comparisons from
`Dbounded` to the ordinary homotopy Verdier quotient are now connected by a
canonical localization uniqueness isomorphism. This removes a comparison-route
ambiguity but still does not construct the stable infinity-category structure.
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
#check boundedCochainComplex_mappingCone
#check boundedComplexCategory_hasZeroObject
#check boundedExactWeakEquivalence
#check exactAcyclic_of_iso
#check exactAcyclic_of_splittings
#check exactAcyclic_shift
#check exactAcyclic_shift_iff
#check exactAcyclic_zero
#check exactAcyclic_mappingCone_shift_iff
#check mappingConeIsoOfCommIso
#check exactAcyclic_mappingCone_congr_iff
#check boundedCochainComplex_mappingCone_congr_iff
#check exactAcyclicHomotopyObject
#check exactAcyclicHomotopyObject_quotient_obj_iff
#check exactAcyclicHomotopyObject_containsZero
#check exactAcyclicHomotopyIsoClosure
#check exactAcyclicHomotopyIsoClosure_isStableUnderShift
#check exactAcyclicHomotopyIsoClosure_isTriangulated_of_isTriangulatedClosed2
#check exactAcyclicHomotopyIsoClosure_isTriangulatedClosed2_of_homotopyObject
#check exactAcyclicHomotopyIsoClosure_trW
#check exactAcyclicHomotopyObject_isStableUnderShift_of_isClosedUnderIsomorphisms
#check exactAcyclicHomotopyObject_isTriangulated_of_isTriangulatedClosed2
#check exactAcyclicHomotopyObject_trW_quotient_map_of_exactAcyclic_mappingCone
#check exactAcyclicHomotopyObject_trW_quotient_map_iff_exactAcyclic_mappingCone
#check exactAcyclicHomotopyIsoClosure_trW_quotient_map_of_exactAcyclic_mappingCone
#check exactAcyclicHomotopyIsoClosure_trW_quotient_map_iff_mappingCone
#check exactAcyclicHomotopyIsoClosure_trW_quotient_map_iff_exactAcyclic_mappingCone
#check exactAcyclicHomotopyObject_triangleh_ext3
#check exactAcyclicHomotopyObject_triangleh_ext2
#check exactAcyclicHomotopyObject_triangleh_ext1
#check exactAcyclicHomotopyObject_triangleh_iso_ext3
#check exactAcyclicHomotopyObject_triangleh_iso_ext2
#check exactAcyclicHomotopyObject_triangleh_iso_ext1
#check exactAcyclicHomotopyObject_distinguished_ext3_of_triangleh_iso12
#check exactAcyclicHomotopyObject_distinguished_ext2_of_triangleh_iso13
#check exactAcyclicHomotopyObject_distinguished_ext1_of_triangleh_iso23
#check exactAcyclicHomotopyObject_isTriangulatedClosed2_of_triangleh_iso13_realization
#check exactAcyclicHomotopyIsoClosure_isTriangulatedClosed2_of_triangleh_iso13_realization
#check exactAcyclicHomotopyIsoClosureTrianglehIso13Realization
#check exactAcyclicHomotopyIsoClosure_isTriangulated_of_triangleh_iso13_realization
#check boundedExactWeakEquivalence_shift_iff
#check boundedExactWeakEquivalence_isCompatibleWithShift
#check BoundedComplexCategory.homotopyQuotient
#check boundedHomotopyObject
#check boundedHomotopyObject_quotient_obj
#check LeanLCAExactChallenge.boundedCochainComplex_of_mappingCone_right
#check LeanLCAExactChallenge.boundedCochainComplex_of_mappingCone_left
#check boundedHomotopyObject_mappingCone
#check boundedHomotopyObject_mappingCone_congr_iff
#check LeanLCAExactChallenge.boundedHomotopyObject_of_mappingCone_right
#check LeanLCAExactChallenge.boundedHomotopyObject_of_mappingCone_left
#check boundedHomotopyObject_triangleh_ext3
#check boundedHomotopyObject_triangleh_ext2
#check boundedHomotopyObject_triangleh_ext1
#check boundedHomotopyObject_triangleh_iso_ext3
#check boundedHomotopyObject_triangleh_iso_ext2
#check boundedHomotopyObject_triangleh_iso_ext1
#check boundedHomotopyObject_distinguished_ext3_of_triangleh_iso12
#check boundedHomotopyObject_distinguished_ext2_of_triangleh_iso13
#check boundedHomotopyObject_distinguished_ext1_of_triangleh_iso23
#check boundedHomotopyObject_isTriangulatedClosed2_of_triangleh_iso13_realization
#check BoundedHomotopyCategory
#check BoundedHomotopyCategory.ι
#check boundedExactWeakEquivalence_le_exactAcyclicHomotopy_trW_inverseImage
#check boundedExactWeakEquivalence_eq_exactAcyclicHomotopy_trW_inverseImage
#check boundedHomotopyExactWeakEquivalence
#check boundedExactWeakEquivalence_le_boundedHomotopyExactWeakEquivalence
#check boundedHomotopyExactWeakEquivalence_of_exactAcyclic_mappingCone
#check boundedHomotopyExactWeakEquivalence_iff_mappingCone_isoClosure
#check boundedExactWeakEquivalence_of_mappingCone_splittings
#check boundedHomotopyExactWeakEquivalence_of_mappingCone_splittings
#check boundedExactWeakEquivalence_eq_boundedHomotopyExactWeakEquivalence_of_isoClosed
#check boundedExactWeakEquivalence_iff_boundedHomotopyExactWeakEquivalence_of_isoClosed
#check boundedExactWeakEquivalence_hasLeftCalculusOfFractions_of_isoClosed
#check boundedExactWeakEquivalence_hasRightCalculusOfFractions_of_isoClosed
#check boundedHomotopyExactWeakEquivalence_iff_exactAcyclic_mappingCone_of_isoClosed
#check boundedHomotopyExactWeakEquivalence_isCompatibleWithShift
#check boundedExactWeakEquivalenceToHomotopyExactWeakEquivalence
#check boundedExactWeakEquivalenceToHomotopyExactWeakEquivalenceOfIsoClosed
#check boundedExactWeakEquivalenceToHomotopyExactWeakEquivalenceOfIsoClosed_localizedEquivalence
#check exactAcyclicHomotopyObject_trW_hasLeftCalculusOfFractions_of_isTriangulated
#check exactAcyclicHomotopyObject_trW_hasRightCalculusOfFractions_of_isTriangulated
#check exactAcyclicHomotopyObject_trW_hasLeftCalculusOfFractions_of_isTriangulatedClosed2
#check exactAcyclicHomotopyObject_trW_hasRightCalculusOfFractions_of_isTriangulatedClosed2
#check exactAcyclicHomotopyObject_trW_hasLeftCalculusOfFractions_of_isoClosureClosed2
#check exactAcyclicHomotopyObject_trW_hasRightCalculusOfFractions_of_isoClosureClosed2
#check exactAcyclicHomotopyObject_trW_hasLeftCalculusOfFractions_of_homotopyObjectClosed2
#check exactAcyclicHomotopyObject_trW_hasRightCalculusOfFractions_of_homotopyObjectClosed2
#check exactAcyclicHomotopyIsoClosure_trW_hasLeftCalculusOfFractions_of_isTriangulatedClosed2
#check exactAcyclicHomotopyIsoClosure_trW_hasRightCalculusOfFractions_of_isTriangulatedClosed2
#check exactAcyclicHomotopyIsoClosure_trW_hasLeftCalculusOfFractions_of_homotopyObjectClosed2
#check exactAcyclicHomotopyIsoClosure_trW_hasRightCalculusOfFractions_of_homotopyObjectClosed2
#check exactAcyclicHomotopyIsoClosure_trW_isCompatibleWithTriangulation_of_isTriangulatedClosed2
#check exactAcyclicHomotopyIsoClosure_trW_isCompatibleWithTriangulation_of_homotopyObjectClosed2
#check exactAcyclicHomotopyIsoClosure_trW_hasLeftCalculusOfFractions_of_triangleh_iso13_realization
#check exactAcyclicHomotopyIsoClosure_trW_hasRightCalculusOfFractions_of_triangleh_iso13_realization
#check exactAcyclicHomotopyIsoClosure_trW_isCompatibleWithTriangulation_of_triangleh_iso13_realization
#check ExactAcyclicHomotopyVerdierCategory
#check ExactAcyclicHomotopyVerdierQuasicategory
#check ExactAcyclicHomotopyVerdierQuasicategory.homotopyCategoryIso
#check exactAcyclicHomotopyVerdierCategory_preadditive_of_isTriangulatedClosed2
#check exactAcyclicHomotopyVerdierCategory_localization_additive_of_isTriangulatedClosed2
#check exactAcyclicHomotopyVerdierCategory_hasZeroObject_of_isTriangulatedClosed2
#check exactAcyclicHomotopyVerdierCategory_hasShift_of_isTriangulatedClosed2
#check exactAcyclicHomotopyVerdierCategory_localization_commShift_of_isTriangulatedClosed2
#check exactAcyclicHomotopyVerdierCategory_shiftFunctor_additive_of_isTriangulatedClosed2
#check exactAcyclicHomotopyVerdierCategory_pretriangulated_of_isTriangulatedClosed2
#check exactAcyclicHomotopyVerdierCategory_isTriangulated_of_isTriangulatedClosed2
#check exactAcyclicHomotopyVerdierCategory_preadditive_of_homotopyObjectClosed2
#check exactAcyclicHomotopyVerdierCategory_localization_additive_of_homotopyObjectClosed2
#check exactAcyclicHomotopyVerdierCategory_hasZeroObject_of_homotopyObjectClosed2
#check exactAcyclicHomotopyVerdierCategory_hasShift_of_homotopyObjectClosed2
#check exactAcyclicHomotopyVerdierCategory_localization_commShift_of_homotopyObjectClosed2
#check exactAcyclicHomotopyVerdierCategory_shiftFunctor_additive_of_homotopyObjectClosed2
#check exactAcyclicHomotopyVerdierCategory_pretriangulated_of_homotopyObjectClosed2
#check exactAcyclicHomotopyVerdierCategory_isTriangulated_of_homotopyObjectClosed2
#check exactAcyclicHomotopyVerdierCategory_preadditive_of_triangleh_iso13_realization
#check exactAcyclicHomotopyVerdierCategory_localization_additive_of_triangleh_iso13_realization
#check exactAcyclicHomotopyVerdierCategory_hasZeroObject_of_triangleh_iso13_realization
#check exactAcyclicHomotopyVerdierCategory_hasShift_of_triangleh_iso13_realization
#check exactAcyclicHomotopyVerdierCategory_localization_commShift_of_triangleh_iso13_realization
#check exactAcyclicHomotopyVerdierCategory_shiftFunctor_additive_of_triangleh_iso13_realization
#check exactAcyclicHomotopyVerdierCategory_pretriangulated_of_triangleh_iso13_realization
#check exactAcyclicHomotopyVerdierCategory_isTriangulated_of_triangleh_iso13_realization
#check BoundedHomotopyDerivedCategory
#check BoundedHomotopyDerivedQuasicategory
#check BoundedHomotopyDerivedQuasicategory.homotopyCategoryIso
#check boundedHomotopyExactWeakEquivalenceToExactAcyclicHomotopyIsoClosure_trW
#check BoundedHomotopyDerivedCategory.verdierComparison
#check Dbounded.homotopyComparison
#check Dbounded.verdierComparison
#check Dbounded.preadditiveOfHasLeftCalculusOfFractions
#check Dbounded.localization_additiveOfHasLeftCalculusOfFractions
#check Dbounded.hasZeroObjectOfHasLeftCalculusOfFractions
#check Dbounded.shiftFunctor_additiveOfHasLeftCalculusOfFractions
#check BoundedHomotopyDerivedCategory.preadditiveOfHasLeftCalculusOfFractions
#check BoundedHomotopyDerivedCategory.localization_additiveOfHasLeftCalculusOfFractions
#check BoundedHomotopyDerivedCategory.hasZeroObjectOfHasLeftCalculusOfFractions
#check BoundedHomotopyDerivedCategory.shiftFunctor_additiveOfHasLeftCalculusOfFractions
#check Dbounded.preadditiveOfHomotopyLeftCalculusOfIsoClosed
#check Dbounded.localization_additiveOfHomotopyLeftCalculusOfIsoClosed
#check Dbounded.hasZeroObjectOfHomotopyLeftCalculusOfIsoClosed
#check Dbounded.shiftFunctor_additiveOfHomotopyLeftCalculusOfIsoClosed

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
    [HasZeroObject C] [HasBinaryBiproducts C] :
    (boundedHomotopyExactWeakEquivalence C).IsCompatibleWithShift ℤ := by
  infer_instance

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] :
    HasShift (BoundedHomotopyDerivedCategory C) ℤ := by
  infer_instance

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] :
    BoundedHomotopyDerivedCategory C ⥤ ExactAcyclicHomotopyVerdierCategory C :=
  BoundedHomotopyDerivedCategory.verdierComparison C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] :
    Dbounded C ⥤ ExactAcyclicHomotopyVerdierCategory C :=
  Dbounded.verdierComparison C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C]
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ} {φ₁ : K₁ ⟶ L₁} {φ₂ : K₂ ⟶ L₂}
    (eK : K₁ ≅ K₂) (eL : L₁ ≅ L₂)
    (comm : φ₁ ≫ eL.hom = eK.hom ≫ φ₂) :
    boundedCochainComplex C (CochainComplex.mappingCone φ₁) ↔
      boundedCochainComplex C (CochainComplex.mappingCone φ₂) :=
  boundedCochainComplex_mappingCone_congr_iff C eK eL comm

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C]
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ} {φ₁ : K₁ ⟶ L₁} {φ₂ : K₂ ⟶ L₂}
    (eK : K₁ ≅ K₂) (eL : L₁ ≅ L₂)
    (comm : φ₁ ≫ eL.hom = eK.hom ≫ φ₂) :
    boundedHomotopyObject C
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
          (CochainComplex.mappingCone φ₁)) ↔
      boundedHomotopyObject C
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
          (CochainComplex.mappingCone φ₂)) :=
  boundedHomotopyObject_mappingCone_congr_iff C eK eL comm

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hCone : exactAcyclic C (CochainComplex.mappingCone f)) :
    exactAcyclicHomotopyObject C (CochainComplex.mappingCone.triangleh f).obj₃ :=
  exactAcyclicHomotopyObject_triangleh_ext3 C f hCone

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] {T : Pretriangulated.Triangle (HomotopyCategory C (ComplexShape.up ℤ))}
    {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (e : T ≅ CochainComplex.mappingCone.triangleh f)
    (hL : exactAcyclic C L) :
    exactAcyclicHomotopyIsoClosure C T.obj₂ :=
  exactAcyclicHomotopyObject_triangleh_iso_ext2 C f e hL

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    {T : Pretriangulated.Triangle (HomotopyCategory C (ComplexShape.up ℤ))}
    (hT : T ∈ distTriang (HomotopyCategory C (ComplexShape.up ℤ)))
    {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (e₂ : (CochainComplex.mappingCone.triangleh f).obj₂ ≅ T.obj₂)
    (e₃ : (CochainComplex.mappingCone.triangleh f).obj₃ ≅ T.obj₃)
    (comm : (CochainComplex.mappingCone.triangleh f).mor₂ ≫ e₃.hom =
      e₂.hom ≫ T.mor₂)
    (hK : exactAcyclic C K) :
    exactAcyclicHomotopyIsoClosure C T.obj₁ :=
  exactAcyclicHomotopyObject_distinguished_ext1_of_triangleh_iso23 C hT f e₂ e₃ comm hK

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (realize :
      ∀ {T : Pretriangulated.Triangle (HomotopyCategory C (ComplexShape.up ℤ))},
        T ∈ distTriang (HomotopyCategory C (ComplexShape.up ℤ)) →
        exactAcyclicHomotopyIsoClosure C T.obj₁ →
        exactAcyclicHomotopyIsoClosure C T.obj₃ →
        ∃ (K L : CochainComplex C ℤ) (f : K ⟶ L)
          (e₁ : (CochainComplex.mappingCone.triangleh f).obj₁ ≅ T.obj₁)
          (e₃ : (CochainComplex.mappingCone.triangleh f).obj₃ ≅ T.obj₃),
            (CochainComplex.mappingCone.triangleh f).mor₃ ≫
                (shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) (1 : ℤ)).map e₁.hom =
              e₃.hom ≫ T.mor₃ ∧
            exactAcyclic C L) :
    (exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂ :=
  exactAcyclicHomotopyIsoClosure_isTriangulatedClosed2_of_triangleh_iso13_realization C
    realize

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (realize : exactAcyclicHomotopyIsoClosureTrianglehIso13Realization C) :
    (exactAcyclicHomotopyIsoClosure C).IsTriangulated :=
  exactAcyclicHomotopyIsoClosure_isTriangulated_of_triangleh_iso13_realization C realize

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (realize : exactAcyclicHomotopyIsoClosureTrianglehIso13Realization C) :
    (exactAcyclicHomotopyIsoClosure C).trW.HasRightCalculusOfFractions :=
  exactAcyclicHomotopyIsoClosure_trW_hasRightCalculusOfFractions_of_triangleh_iso13_realization
    C realize

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (realize : exactAcyclicHomotopyIsoClosureTrianglehIso13Realization C) :
    Preadditive (ExactAcyclicHomotopyVerdierCategory C) :=
  exactAcyclicHomotopyVerdierCategory_preadditive_of_triangleh_iso13_realization C realize

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hK : boundedCochainComplex C K) (hL : boundedCochainComplex C L) :
    boundedHomotopyObject C (CochainComplex.mappingCone.triangleh f).obj₃ :=
  boundedHomotopyObject_triangleh_ext3 C f hK hL

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hK : boundedCochainComplex C K)
    (hCone : boundedCochainComplex C (CochainComplex.mappingCone f)) :
    boundedHomotopyObject C (CochainComplex.mappingCone.triangleh f).obj₂ :=
  boundedHomotopyObject_triangleh_ext2 C f hK hCone

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hL : boundedCochainComplex C L)
    (hCone : boundedCochainComplex C (CochainComplex.mappingCone f)) :
    boundedHomotopyObject C (CochainComplex.mappingCone.triangleh f).obj₁ :=
  boundedHomotopyObject_triangleh_ext1 C f hL hCone

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] {T : Pretriangulated.Triangle (HomotopyCategory C (ComplexShape.up ℤ))}
    {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (e : T ≅ CochainComplex.mappingCone.triangleh f)
    (hK : boundedCochainComplex C K) (hL : boundedCochainComplex C L) :
    boundedHomotopyObject C T.obj₃ :=
  boundedHomotopyObject_triangleh_iso_ext3 C f e hK hL

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] {T : Pretriangulated.Triangle (HomotopyCategory C (ComplexShape.up ℤ))}
    {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (e : T ≅ CochainComplex.mappingCone.triangleh f)
    (hK : boundedCochainComplex C K)
    (hCone : boundedCochainComplex C (CochainComplex.mappingCone f)) :
    boundedHomotopyObject C T.obj₂ :=
  boundedHomotopyObject_triangleh_iso_ext2 C f e hK hCone

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] {T : Pretriangulated.Triangle (HomotopyCategory C (ComplexShape.up ℤ))}
    {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (e : T ≅ CochainComplex.mappingCone.triangleh f)
    (hL : boundedCochainComplex C L)
    (hCone : boundedCochainComplex C (CochainComplex.mappingCone f)) :
    boundedHomotopyObject C T.obj₁ :=
  boundedHomotopyObject_triangleh_iso_ext1 C f e hL hCone

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    {T : Pretriangulated.Triangle (HomotopyCategory C (ComplexShape.up ℤ))}
    (hT : T ∈ distTriang (HomotopyCategory C (ComplexShape.up ℤ)))
    {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (e₁ : (CochainComplex.mappingCone.triangleh f).obj₁ ≅ T.obj₁)
    (e₂ : (CochainComplex.mappingCone.triangleh f).obj₂ ≅ T.obj₂)
    (comm : (CochainComplex.mappingCone.triangleh f).mor₁ ≫ e₂.hom =
      e₁.hom ≫ T.mor₁)
    (hK : boundedCochainComplex C K) (hL : boundedCochainComplex C L) :
    boundedHomotopyObject C T.obj₃ :=
  boundedHomotopyObject_distinguished_ext3_of_triangleh_iso12 C hT f e₁ e₂ comm hK hL

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    {T : Pretriangulated.Triangle (HomotopyCategory C (ComplexShape.up ℤ))}
    (hT : T ∈ distTriang (HomotopyCategory C (ComplexShape.up ℤ)))
    {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (e₁ : (CochainComplex.mappingCone.triangleh f).obj₁ ≅ T.obj₁)
    (e₃ : (CochainComplex.mappingCone.triangleh f).obj₃ ≅ T.obj₃)
    (comm : (CochainComplex.mappingCone.triangleh f).mor₃ ≫
        (shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) (1 : ℤ)).map e₁.hom =
      e₃.hom ≫ T.mor₃)
    (hK : boundedCochainComplex C K)
    (hCone : boundedCochainComplex C (CochainComplex.mappingCone f)) :
    boundedHomotopyObject C T.obj₂ :=
  boundedHomotopyObject_distinguished_ext2_of_triangleh_iso13 C hT f e₁ e₃ comm hK hCone

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    {T : Pretriangulated.Triangle (HomotopyCategory C (ComplexShape.up ℤ))}
    (hT : T ∈ distTriang (HomotopyCategory C (ComplexShape.up ℤ)))
    {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (e₂ : (CochainComplex.mappingCone.triangleh f).obj₂ ≅ T.obj₂)
    (e₃ : (CochainComplex.mappingCone.triangleh f).obj₃ ≅ T.obj₃)
    (comm : (CochainComplex.mappingCone.triangleh f).mor₂ ≫ e₃.hom =
      e₂.hom ≫ T.mor₂)
    (hL : boundedCochainComplex C L)
    (hCone : boundedCochainComplex C (CochainComplex.mappingCone f)) :
    boundedHomotopyObject C T.obj₁ :=
  boundedHomotopyObject_distinguished_ext1_of_triangleh_iso23 C hT f e₂ e₃ comm hL hCone

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (realize :
      ∀ {T : Pretriangulated.Triangle (HomotopyCategory C (ComplexShape.up ℤ))},
        T ∈ distTriang (HomotopyCategory C (ComplexShape.up ℤ)) →
        boundedHomotopyObject C T.obj₁ →
        boundedHomotopyObject C T.obj₃ →
        ∃ (K L : CochainComplex C ℤ) (f : K ⟶ L)
          (e₁ : (CochainComplex.mappingCone.triangleh f).obj₁ ≅ T.obj₁)
          (e₃ : (CochainComplex.mappingCone.triangleh f).obj₃ ≅ T.obj₃),
            (CochainComplex.mappingCone.triangleh f).mor₃ ≫
                (shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) (1 : ℤ)).map e₁.hom =
              e₃.hom ≫ T.mor₃ ∧
            boundedCochainComplex C K ∧
            boundedCochainComplex C (CochainComplex.mappingCone f)) :
    (boundedHomotopyObject C).IsTriangulatedClosed₂ :=
  boundedHomotopyObject_isTriangulatedClosed2_of_triangleh_iso13_realization C realize

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    Preadditive (ExactAcyclicHomotopyVerdierCategory C) := by
  infer_instance

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    ((exactAcyclicHomotopyIsoClosure C).trW.Q).Additive := by
  infer_instance

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    HasZeroObject (ExactAcyclicHomotopyVerdierCategory C) := by
  infer_instance

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    HasShift (ExactAcyclicHomotopyVerdierCategory C) ℤ := by
  infer_instance

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    ((exactAcyclicHomotopyIsoClosure C).trW.Q).CommShift ℤ := by
  infer_instance

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    (shiftFunctor (ExactAcyclicHomotopyVerdierCategory C) (1 : ℤ)).Additive := by
  infer_instance

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    Pretriangulated (ExactAcyclicHomotopyVerdierCategory C) := by
  infer_instance

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    IsTriangulated (ExactAcyclicHomotopyVerdierCategory C) := by
  infer_instance

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsTriangulatedClosed₂] :
    Preadditive (ExactAcyclicHomotopyVerdierCategory C) :=
  exactAcyclicHomotopyVerdierCategory_preadditive_of_homotopyObjectClosed2 C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsTriangulatedClosed₂] :
    IsTriangulated (ExactAcyclicHomotopyVerdierCategory C) :=
  exactAcyclicHomotopyVerdierCategory_isTriangulated_of_homotopyObjectClosed2 C

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

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    Preadditive (BoundedHomotopyDerivedCategory C) :=
  BoundedHomotopyDerivedCategory.preadditiveOfHasLeftCalculusOfFractions C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    ((boundedHomotopyExactWeakEquivalence C).Q).Additive :=
  BoundedHomotopyDerivedCategory.localization_additiveOfHasLeftCalculusOfFractions C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    HasZeroObject (BoundedHomotopyDerivedCategory C) :=
  BoundedHomotopyDerivedCategory.hasZeroObjectOfHasLeftCalculusOfFractions C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    (shiftFunctor (BoundedHomotopyDerivedCategory C) (1 : ℤ)).Additive :=
  BoundedHomotopyDerivedCategory.shiftFunctor_additiveOfHasLeftCalculusOfFractions C 1

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    (boundedExactWeakEquivalence C).HasLeftCalculusOfFractions :=
  boundedExactWeakEquivalence_hasLeftCalculusOfFractions_of_isoClosed C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalence C).HasRightCalculusOfFractions] :
    (boundedExactWeakEquivalence C).HasRightCalculusOfFractions :=
  boundedExactWeakEquivalence_hasRightCalculusOfFractions_of_isoClosed C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsTriangulatedClosed₂] :
    (exactAcyclicHomotopyIsoClosure C).trW.HasRightCalculusOfFractions :=
  exactAcyclicHomotopyIsoClosure_trW_hasRightCalculusOfFractions_of_homotopyObjectClosed2 C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    Preadditive (Dbounded C) :=
  Dbounded.preadditiveOfHomotopyLeftCalculusOfIsoClosed C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    letI : (boundedExactWeakEquivalence C).HasLeftCalculusOfFractions :=
      boundedExactWeakEquivalence_hasLeftCalculusOfFractions_of_isoClosed C
    (Dbounded.localization C).Additive :=
  Dbounded.localization_additiveOfHomotopyLeftCalculusOfIsoClosed C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    HasZeroObject (Dbounded C) :=
  Dbounded.hasZeroObjectOfHomotopyLeftCalculusOfIsoClosed C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    letI : (boundedExactWeakEquivalence C).HasLeftCalculusOfFractions :=
      boundedExactWeakEquivalence_hasLeftCalculusOfFractions_of_isoClosed C
    (shiftFunctor (Dbounded C) (1 : ℤ)).Additive :=
  Dbounded.shiftFunctor_additiveOfHomotopyLeftCalculusOfIsoClosed C 1

#check (Dbounded (C := MetrizableLCA))
#check Dbounded.localization
#check BoundedHomotopyDerivedCategory
#check BoundedHomotopyDerivedQuasicategory
#check BoundedHomotopyDerivedQuasicategory.homotopyCategoryIso
#check boundedExactWeakEquivalenceToExactAcyclicHomotopyIsoClosure_trW
#check BoundedHomotopyDerivedCategory.verdierComparison
#check BoundedHomotopyDerivedCategory.verdierComparisonLocalizationIso
#check Dbounded.homotopyComparison
#check Dbounded.homotopyComparisonLocalizationIso
#check Dbounded.verdierComparison
#check Dbounded.verdierComparisonLocalizationIso
#check Dbounded.verdierComparisonDirect
#check Dbounded.verdierComparisonDirectLocalizationIso
#check Dbounded.verdierComparisonDirectIso
#check Dbounded.homotopyComparisonEquivalenceOfIsoClosed
#check boundedHomotopyObject_isTriangulated_of_isTriangulatedClosed2
#check boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2
#check boundedHomotopyCategory_isTriangulated_of_isTriangulatedClosed2
#check boundedExactAcyclicHomotopyObject
#check boundedExactAcyclicHomotopyObject_isTriangulated_of_closed2
#check BoundedExactAcyclicHomotopyVerdierCategory
#check BoundedExactAcyclicHomotopyVerdierQuasicategory
#check boundedExactAcyclicHomotopyVerdierCategory_preadditive_of_closed2
#check boundedExactAcyclicHomotopyVerdierCategory_localization_additive_of_closed2
#check boundedExactAcyclicHomotopyVerdierCategory_hasZeroObject_of_closed2
#check boundedExactAcyclicHomotopyVerdierCategory_hasShift_of_closed2
#check boundedExactAcyclicHomotopyVerdierCategory_localization_commShift_of_closed2
#check boundedExactAcyclicHomotopyVerdierCategory_shiftFunctor_additive_of_closed2
#check boundedExactAcyclicHomotopyVerdierCategory_pretriangulated_of_closed2
#check boundedExactAcyclicHomotopyVerdierCategory_isTriangulated_of_closed2
#check Dbounded.infinityCategory
#check Dbounded.infinityNerve
#check Dbounded.infinityNerve_quasicategory
#check Dbounded.homotopyCategoryIso
#check CategoryTheory.Triangulated.Localization.pretriangulated
#check CategoryTheory.Triangulated.Localization.isTriangulated

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] :
    LocalizerMorphism (boundedExactWeakEquivalence C)
      (exactAcyclicHomotopyIsoClosure C).trW :=
  boundedExactWeakEquivalenceToExactAcyclicHomotopyIsoClosure_trW C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] :
    BoundedComplexCategory.homotopyQuotient C ⋙
        (exactAcyclicHomotopyIsoClosure C).trW.Q ≅
      Dbounded.localization C ⋙ Dbounded.verdierComparisonDirect C :=
  Dbounded.verdierComparisonDirectLocalizationIso C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] :
    Dbounded.verdierComparison C ≅ Dbounded.verdierComparisonDirect C :=
  Dbounded.verdierComparisonDirectIso C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    Pretriangulated (BoundedExactAcyclicHomotopyVerdierCategory C) :=
  boundedExactAcyclicHomotopyVerdierCategory_pretriangulated_of_closed2 (C := C)

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    IsTriangulated (BoundedExactAcyclicHomotopyVerdierCategory C) :=
  boundedExactAcyclicHomotopyVerdierCategory_isTriangulated_of_closed2 (C := C)

end LeanLCAExactChallenge
