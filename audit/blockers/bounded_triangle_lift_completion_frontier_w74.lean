import LeanLCAExactChallenge.Derived.Bounded

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

/--
The exact `lift_completion` shape needed by the w69 homotopy-transport theorem.

After `BoundedComplexCategory.homotopyQuotientBounded C`, target-side triangulated
compatibility gives a third vertical arrow `cH` in the bounded homotopy category. This
input asks for the strict source arrow `c`, direct bounded exact weak equivalence of `c`,
and the two strict source triangle equations.
-/
abbrev boundedExactWeakEquivalenceLiftCompletionInput
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [Preadditive (BoundedComplexCategory C)]
    [HasShift (BoundedComplexCategory C) ℤ]
    [∀ (n : ℤ), (shiftFunctor (BoundedComplexCategory C) n).Additive]
    [Pretriangulated (BoundedComplexCategory C)]
    [HasShift (BoundedHomotopyCategory C) ℤ]
    [(BoundedComplexCategory.homotopyQuotientBounded C).CommShift ℤ] : Prop :=
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
        (T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃)

/--
Route-1 frontier: the target third arrow must be lifted to a strict source arrow and the
direct bounded exact weak-equivalence property must be reflected back to that strict
representative.

The equality `map c = cH` is deliberately retained as evidence. It is stronger than the
w69 `lift_completion` input consumes, but it records the representative-level datum that
is absent if mathlib only supplies a homotopy-category morphism up to isomorphism.
-/
abbrev boundedExactWeakEquivalenceHomotopyLiftReflection
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [Preadditive (BoundedComplexCategory C)]
    [HasShift (BoundedComplexCategory C) ℤ]
    [∀ (n : ℤ), (shiftFunctor (BoundedComplexCategory C) n).Additive]
    [Pretriangulated (BoundedComplexCategory C)]
    [HasShift (BoundedHomotopyCategory C) ℤ]
    [(BoundedComplexCategory.homotopyQuotientBounded C).CommShift ℤ] : Prop :=
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
      ∃ (c : T₁.obj₃ ⟶ T₂.obj₃),
        (BoundedComplexCategory.homotopyQuotientBounded C).map c = cH ∧
        boundedExactWeakEquivalence C c ∧
        (T₁.mor₂ ≫ c = b ≫ T₂.mor₂) ∧
        (T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃)

/--
A strict homotopy lift/reflection theorem is exactly strong enough to supply the w69
`lift_completion` input.
-/
theorem boundedExactWeakEquivalence_liftCompletion_of_homotopyLiftReflection
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [Preadditive (BoundedComplexCategory C)]
    [HasShift (BoundedComplexCategory C) ℤ]
    [∀ (n : ℤ), (shiftFunctor (BoundedComplexCategory C) n).Additive]
    [Pretriangulated (BoundedComplexCategory C)]
    [HasShift (BoundedHomotopyCategory C) ℤ]
    [(BoundedComplexCategory.homotopyQuotientBounded C).CommShift ℤ]
    (reflect : boundedExactWeakEquivalenceHomotopyLiftReflection C) :
    boundedExactWeakEquivalenceLiftCompletionInput C := by
  intro T₁ T₂ hT₁ hT₂ a b ha hb hcomm cH hcH₂ hcH₃
  rcases reflect T₁ T₂ hT₁ hT₂ a b ha hb hcomm cH hcH₂ hcH₃ with
    ⟨c, _hc_map, hcW, hc₂, hc₃⟩
  exact ⟨c, hcW, hc₂, hc₃⟩

/--
Reflection from the bounded homotopy Verdier weak equivalences back to direct bounded
exact weak equivalences is already available once the inverse-image equality hypotheses in
`Bounded.lean` are in force.
-/
theorem boundedExactWeakEquivalence_of_homotopyQuotientBounded_trW
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms]
    {K L : BoundedComplexCategory C} {f : K ⟶ L} :
    letI : Pretriangulated (BoundedHomotopyCategory C) :=
      boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
    (boundedExactAcyclicHomotopyObject C).trW
        ((BoundedComplexCategory.homotopyQuotientBounded C).map f) →
      boundedExactWeakEquivalence C f := by
  letI : Pretriangulated (BoundedHomotopyCategory C) :=
    boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
  intro hf
  have hEq :=
    boundedExactWeakEquivalence_eq_boundedExactAcyclicHomotopy_trW_inverseImage_of_isoClosed C
  rw [hEq]
  exact hf

/--
The w69 homotopy-transport theorem specialized to the route-1 frontier. Target-side
triangle compatibility plus a strict homotopy lift/reflection input gives source-side
`boundedExactWeakEquivalence` triangle compatibility.
-/
theorem boundedExactWeakEquivalence_isCompatibleWithTriangulation_of_homotopyLiftReflection
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
    (reflect : boundedExactWeakEquivalenceHomotopyLiftReflection C) :
    (boundedExactWeakEquivalence C).IsCompatibleWithTriangulation := by
  let H : BoundedComplexCategory C ⥤ BoundedHomotopyCategory C :=
    BoundedComplexCategory.homotopyQuotientBounded C
  let lift_completion : boundedExactWeakEquivalenceLiftCompletionInput C :=
    boundedExactWeakEquivalence_liftCompletion_of_homotopyLiftReflection C reflect
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
  [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms]

#check boundedExactWeakEquivalenceLiftCompletionInput
#check boundedExactWeakEquivalenceHomotopyLiftReflection
#check boundedExactWeakEquivalence_liftCompletion_of_homotopyLiftReflection
#check boundedExactWeakEquivalence_of_homotopyQuotientBounded_trW
#check boundedExactWeakEquivalence_isCompatibleWithTriangulation_of_homotopyLiftReflection
#check boundedExactWeakEquivalence_eq_boundedExactAcyclicHomotopy_trW_inverseImage_of_isoClosed
#check boundedExactWeakEquivalenceToBoundedExactAcyclicHomotopy_trW C
#check BoundedComplexCategory.homotopyQuotientBounded C
#check MorphismProperty.compatible_with_triangulation

end Checks

end LeanLCAExactChallenge
