import LeanLCAExactChallenge.Derived.Bounded

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

/--
Audit theorem for the homotopy-transport route to the missing direct source-side
`boundedExactWeakEquivalence` triangle compatibility.

The target triangulated category can complete the mapped square after
`BoundedComplexCategory.homotopyQuotientBounded C`, but that is not yet enough for
mathlib's source-side localization theorem. The remaining strict API is precisely the
`lift_completion` argument: it must lift the target third vertical arrow back to an actual
morphism of bounded complexes, prove it is a direct bounded exact weak equivalence, and
recover the two strict triangle-commutativity equations.
-/
theorem boundedExactWeakEquivalence_isCompatibleWithTriangulation_of_homotopy_transport_lift
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [Preadditive (BoundedComplexCategory C)]
    [HasZeroObject (BoundedComplexCategory C)]
    [HasShift (BoundedComplexCategory C) ℤ]
    [∀ (n : ℤ), (shiftFunctor (BoundedComplexCategory C) n).Additive]
    [Pretriangulated (BoundedComplexCategory C)]
    [(boundedExactWeakEquivalence C).IsCompatibleWithShift ℤ]
    [Preadditive (BoundedHomotopyCategory C)]
    [HasZeroObject (BoundedHomotopyCategory C)]
    [HasShift (BoundedHomotopyCategory C) ℤ]
    [∀ (n : ℤ), (shiftFunctor (BoundedHomotopyCategory C) n).Additive]
    [Pretriangulated (BoundedHomotopyCategory C)]
    [(BoundedComplexCategory.homotopyQuotientBounded C).CommShift ℤ]
    (targetWeak : MorphismProperty (BoundedHomotopyCategory C))
    [targetWeak.IsCompatibleWithTriangulation]
    (map_distinguished :
      ∀ (T : Pretriangulated.Triangle (BoundedComplexCategory C)),
        T ∈ distTriang (BoundedComplexCategory C) →
          (BoundedComplexCategory.homotopyQuotientBounded C).mapTriangle.obj T ∈
            distTriang (BoundedHomotopyCategory C))
    (map_weak :
      ∀ {K L : BoundedComplexCategory C} (f : K ⟶ L),
        boundedExactWeakEquivalence C f →
          targetWeak ((BoundedComplexCategory.homotopyQuotientBounded C).map f))
    (lift_completion :
      ∀ (T₁ T₂ : Pretriangulated.Triangle (BoundedComplexCategory C))
        (_ : T₁ ∈ distTriang (BoundedComplexCategory C))
        (_ : T₂ ∈ distTriang (BoundedComplexCategory C))
        (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂),
        boundedExactWeakEquivalence C a →
        boundedExactWeakEquivalence C b →
        T₁.mor₁ ≫ b = a ≫ T₂.mor₁ →
        ∀ (cH :
          (BoundedComplexCategory.homotopyQuotientBounded C).obj T₁.obj₃ ⟶
            (BoundedComplexCategory.homotopyQuotientBounded C).obj T₂.obj₃),
          ((BoundedComplexCategory.homotopyQuotientBounded C).mapTriangle.obj T₁).mor₂ ≫ cH =
            (BoundedComplexCategory.homotopyQuotientBounded C).map b ≫
              ((BoundedComplexCategory.homotopyQuotientBounded C).mapTriangle.obj T₂).mor₂ →
          ((BoundedComplexCategory.homotopyQuotientBounded C).mapTriangle.obj T₁).mor₃ ≫
              ((BoundedComplexCategory.homotopyQuotientBounded C).map a)⟦(1 : ℤ)⟧' =
            cH ≫
              ((BoundedComplexCategory.homotopyQuotientBounded C).mapTriangle.obj T₂).mor₃ →
          ∃ (c : T₁.obj₃ ⟶ T₂.obj₃), ∃ (_ : boundedExactWeakEquivalence C c),
            (T₁.mor₂ ≫ c = b ≫ T₂.mor₂) ∧
            (T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃)) :
    (boundedExactWeakEquivalence C).IsCompatibleWithTriangulation := by
  let H : BoundedComplexCategory C ⥤ BoundedHomotopyCategory C :=
    BoundedComplexCategory.homotopyQuotientBounded C
  refine
    { compatible_with_triangulation := ?_ }
  intro T₁ T₂ hT₁ hT₂ a b ha hb hcomm
  have hcommH :
      (H.mapTriangle.obj T₁).mor₁ ≫ H.map b =
        H.map a ≫ (H.mapTriangle.obj T₂).mor₁ := by
    simpa [H] using H.congr_map hcomm
  obtain ⟨cH, _hcH, hcH₂, hcH₃⟩ :=
    MorphismProperty.compatible_with_triangulation
      (W := targetWeak)
      (H.mapTriangle.obj T₁) (H.mapTriangle.obj T₂)
      (map_distinguished T₁ hT₁) (map_distinguished T₂ hT₂)
      (H.map a) (H.map b) (map_weak a ha) (map_weak b hb) hcommH
  exact lift_completion T₁ T₂ hT₁ hT₂ a b ha hb hcomm cH
    (by simpa [H] using hcH₂) (by simpa [H] using hcH₃)

section Checks

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
  [HasZeroObject C] [HasBinaryBiproducts C]
  [(boundedHomotopyObject C).IsTriangulatedClosed₂]
  [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂]

#check boundedExactWeakEquivalence_isCompatibleWithTriangulation_of_homotopy_transport_lift
#check BoundedComplexCategory.homotopyQuotientBounded C
#check BoundedComplexCategory.homotopyQuotientBounded_comp_ι_iso C
#check boundedExactWeakEquivalenceToBoundedExactAcyclicHomotopy_trW C
#check boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
#check boundedExactAcyclicHomotopyObject_isTriangulated_of_closed2 C
#check CategoryTheory.MorphismProperty.compatible_with_triangulation
#check CategoryTheory.Functor.mapTriangle

end Checks

end LeanLCAExactChallenge
