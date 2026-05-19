import LeanLCAExactChallenge.Derived.Bounded

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
  [HasBinaryBiproducts C]

omit [QuillenExactCategory C] in
/-- Every morphism in the bounded homotopy category between objects coming from bounded
complexes has a strict bounded-complex representative.

This is the easy part of the w74 lift/reflection frontier: it follows from fullness of
`BoundedComplexCategory.homotopyQuotientBounded`. It does not by itself recover strict
source-side commutative triangle equations; it only represents the target homotopy
category morphism. -/
theorem boundedHomotopyQuotientBounded_strictRepresentative
    {K L : BoundedComplexCategory C}
    (cH :
      (BoundedComplexCategory.homotopyQuotientBounded C).obj K ⟶
        (BoundedComplexCategory.homotopyQuotientBounded C).obj L) :
    ∃ c : K ⟶ L, (BoundedComplexCategory.homotopyQuotientBounded C).map c = cH :=
  ⟨(BoundedComplexCategory.homotopyQuotientBounded C).preimage cH,
    (BoundedComplexCategory.homotopyQuotientBounded C).map_preimage cH⟩

omit [QuillenExactCategory C] in
/--
If a target-side equation holds in the bounded homotopy category, choosing the strict
preimage of the final arrow only gives a mapped equation after applying
`homotopyQuotientBounded`.

The missing product proof still needs a way to turn such mapped equalities into the
strict source equations required by `boundedExactWeakEquivalenceHomotopyLiftReflection`.
-/
theorem boundedHomotopyQuotientBounded_preimage_sourceEquation_mapped
    {K₂ K₃ L₂ L₃ : BoundedComplexCategory C}
    (u : K₂ ⟶ K₃) (b : K₂ ⟶ L₂) (v : L₂ ⟶ L₃)
    (cH :
      (BoundedComplexCategory.homotopyQuotientBounded C).obj K₃ ⟶
        (BoundedComplexCategory.homotopyQuotientBounded C).obj L₃)
    (h :
      (BoundedComplexCategory.homotopyQuotientBounded C).map u ≫ cH =
        (BoundedComplexCategory.homotopyQuotientBounded C).map b ≫
          (BoundedComplexCategory.homotopyQuotientBounded C).map v) :
    (BoundedComplexCategory.homotopyQuotientBounded C).map
      (u ≫ (BoundedComplexCategory.homotopyQuotientBounded C).preimage cH) =
      (BoundedComplexCategory.homotopyQuotientBounded C).map (b ≫ v) := by
  calc
    (BoundedComplexCategory.homotopyQuotientBounded C).map
        (u ≫ (BoundedComplexCategory.homotopyQuotientBounded C).preimage cH) =
        (BoundedComplexCategory.homotopyQuotientBounded C).map u ≫
          (BoundedComplexCategory.homotopyQuotientBounded C).map
            ((BoundedComplexCategory.homotopyQuotientBounded C).preimage cH) := by
      rw [Functor.map_comp]
    _ = (BoundedComplexCategory.homotopyQuotientBounded C).map u ≫ cH := by
      rw [(BoundedComplexCategory.homotopyQuotientBounded C).map_preimage cH]
    _ = (BoundedComplexCategory.homotopyQuotientBounded C).map b ≫
          (BoundedComplexCategory.homotopyQuotientBounded C).map v := h
    _ = (BoundedComplexCategory.homotopyQuotientBounded C).map (b ≫ v) := by
      rw [Functor.map_comp]

section Checks

#check boundedHomotopyQuotientBounded_strictRepresentative
#check boundedHomotopyQuotientBounded_preimage_sourceEquation_mapped
#check BoundedComplexCategory.homotopyQuotientBounded
#check Functor.map_preimage

end Checks

end LeanLCAExactChallenge
