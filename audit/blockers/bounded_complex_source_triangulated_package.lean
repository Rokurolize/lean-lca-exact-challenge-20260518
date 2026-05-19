import LeanLCAExactChallenge.Derived.Bounded

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

/--
Exact theorem shape for the missing direct source-side compatibility input.

Mathlib's triangulated-localization API does not ask merely for shift compatibility of the
bounded exact weak equivalences. It asks for a completion principle for morphisms between
distinguished triangles in the source `BoundedComplexCategory C`: if the first two
vertical arrows are bounded exact weak equivalences and the first square commutes, then
the third vertical arrow can be chosen as a bounded exact weak equivalence and completes
the morphism of triangles.
-/
theorem boundedExactWeakEquivalence_isCompatibleWithTriangulation_of_triangle_completion
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [Preadditive (BoundedComplexCategory C)]
    [HasZeroObject (BoundedComplexCategory C)]
    [HasShift (BoundedComplexCategory C) ℤ]
    [∀ (n : ℤ), (shiftFunctor (BoundedComplexCategory C) n).Additive]
    [Pretriangulated (BoundedComplexCategory C)]
    [(boundedExactWeakEquivalence C).IsCompatibleWithShift ℤ]
    (complete :
      ∀ (T₁ T₂ : Pretriangulated.Triangle (BoundedComplexCategory C)),
        T₁ ∈ distTriang (BoundedComplexCategory C) →
        T₂ ∈ distTriang (BoundedComplexCategory C) →
        ∀ (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂),
          boundedExactWeakEquivalence C a →
          boundedExactWeakEquivalence C b →
          T₁.mor₁ ≫ b = a ≫ T₂.mor₁ →
          ∃ (c : T₁.obj₃ ⟶ T₂.obj₃), ∃ (_ : boundedExactWeakEquivalence C c),
            (T₁.mor₂ ≫ c = b ≫ T₂.mor₂) ∧
            (T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃)) :
    (boundedExactWeakEquivalence C).IsCompatibleWithTriangulation := by
  exact
    { compatible_with_triangulation := by
        intro T₁ T₂ hT₁ hT₂ a b ha hb hcomm
        exact complete T₁ T₂ hT₁ hT₂ a b ha hb hcomm }

namespace Dbounded

/--
Conditional direct source-side package for `Dbounded`.

Once the source `BoundedComplexCategory C` has ordinary triangulated structure, the bounded
exact weak equivalences have left fractions and the compatibility theorem above, and the
localized target has the standard additive/shift infrastructure, mathlib supplies
`IsTriangulated (Dbounded C)` directly.
-/
noncomputable abbrev isTriangulatedOfBoundedComplexSourcePackage
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [Preadditive (BoundedComplexCategory C)]
    [HasZeroObject (BoundedComplexCategory C)]
    [HasShift (BoundedComplexCategory C) ℤ]
    [∀ (n : ℤ), (shiftFunctor (BoundedComplexCategory C) n).Additive]
    [Pretriangulated (BoundedComplexCategory C)]
    [IsTriangulated (BoundedComplexCategory C)]
    [Preadditive (Dbounded C)]
    [HasZeroObject (Dbounded C)]
    [HasShift (Dbounded C) ℤ]
    [∀ (n : ℤ), (shiftFunctor (Dbounded C) n).Additive]
    [(Dbounded.localization C).CommShift ℤ]
    [(Dbounded.localization C).Additive]
    [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions]
    [(boundedExactWeakEquivalence C).IsCompatibleWithTriangulation] :
    letI : Pretriangulated (Dbounded C) :=
      Triangulated.Localization.pretriangulated
        (Dbounded.localization C) (boundedExactWeakEquivalence C)
    IsTriangulated (Dbounded C) := by
  letI : Pretriangulated (Dbounded C) :=
    Triangulated.Localization.pretriangulated
      (Dbounded.localization C) (boundedExactWeakEquivalence C)
  exact Triangulated.Localization.isTriangulated
    (Dbounded.localization C) (boundedExactWeakEquivalence C)

end Dbounded

section Checks

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
  [HasZeroObject C] [HasBinaryBiproducts C]

#check boundedExactWeakEquivalence_isCompatibleWithShift C
#check boundedExactWeakEquivalence_isCompatibleWithTriangulation_of_triangle_completion
#check Dbounded.isTriangulatedOfBoundedComplexSourcePackage
#check BoundedComplexCategory.homotopyQuotientBounded C
#check boundedHomotopyCategory_pretriangulated_of_triangleh_iso13_realization C
#check CategoryTheory.MorphismProperty.compatible_with_triangulation
#check CategoryTheory.Triangulated.Localization.pretriangulated
#check CategoryTheory.Triangulated.Localization.isTriangulated

end Checks

end LeanLCAExactChallenge
