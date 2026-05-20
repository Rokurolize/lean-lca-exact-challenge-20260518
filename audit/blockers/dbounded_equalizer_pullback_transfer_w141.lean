import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Localization.FiniteProducts
import Mathlib.CategoryTheory.MorphismProperty.Limits
import LeanLCAExactChallenge.Derived.Bounded

/-!
W141 audit: equalizer transfer frontier for `Dbounded`.

The finite-limit route after W139 needs `HasEqualizers (Dbounded C)` or, dually,
`HasPullbacks (Dbounded C)`.  This file focuses on the equalizer route selected by the
support worker.  It records the exact bounded weak-equivalence stability input and the missing
localization theorem shape that would turn bounded-complex equalizers into equalizers in
`Dbounded C`.

This is intentionally not a product-success proof and does not claim an unconditional
`HasFiniteLimits (Dbounded C)`.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace DboundedEqualizerPullbackTransferW141

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
  [HasBinaryBiproducts C]

/-- Bounded complexes inherit equalizers from the existing finite-limit source API. -/
noncomputable abbrev boundedComplexHasEqualizersOfBaseFiniteLimits
    [HasFiniteLimits C] :
    HasEqualizers (BoundedComplexCategory C) := by
  infer_instance

/--
The exact equalizer-shaped mapping-cone input for `boundedExactWeakEquivalence`.

This is stated using mathlib's general finite-limit stability API.  For
`WalkingParallelPair`, the cone point is an equalizer.  A future proof should discharge this
by comparing the mapping cone of the equalizer-induced morphism with the equalizer of the
component mapping cones, then transporting exact acyclicity.
-/
abbrev EqualizerConeInput : Prop :=
  ∀ (X₁ X₂ : WalkingParallelPair ⥤ BoundedComplexCategory C)
    (c₁ : Cone X₁) (c₂ : Cone X₂)
    (_h₁ : IsLimit c₁) (_h₂ : IsLimit c₂)
    (f : X₁ ⟶ X₂),
    (∀ j, boundedExactWeakEquivalence C (f.app j)) →
      ∀ (φ : c₁.pt ⟶ c₂.pt),
        (∀ j, φ ≫ c₂.π.app j = c₁.π.app j ≫ f.app j) →
          boundedExactWeakEquivalence C φ

/-- The equalizer cone input is exactly the `WalkingParallelPair` stability class. -/
theorem isStableUnderEqualizers_of_equalizerConeInput
    (h : EqualizerConeInput C) :
    (boundedExactWeakEquivalence C).IsStableUnderLimitsOfShape WalkingParallelPair where
  condition X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ := h X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ

/--
The missing localization theorem for the equalizer route.

Mathlib currently supplies `Localization.hasFiniteProducts` for finite products, but no
corresponding generic `Localization.hasEqualizers` theorem was found in this dependency
snapshot.  This is the theorem shape needed above W141's mapping-cone input.
-/
abbrev EqualizerLocalizationTransferTheorem : Prop :=
  ∀ [HasFiniteLimits C]
    [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions]
    [(boundedExactWeakEquivalence C).IsStableUnderLimitsOfShape WalkingParallelPair],
      HasEqualizers (Dbounded C)

/-- If the missing localization theorem is supplied, the selected route gives equalizers. -/
noncomputable abbrev dboundedHasEqualizersOfTransferTheorem
    [HasFiniteLimits C]
    [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions]
    [(boundedExactWeakEquivalence C).IsStableUnderLimitsOfShape WalkingParallelPair]
    (h : EqualizerLocalizationTransferTheorem C) :
    HasEqualizers (Dbounded C) :=
  h

/--
Combining the equalizer transfer theorem with the existing finite-product localization route
closes the W139 finite-limit gap.
-/
noncomputable abbrev dboundedHasFiniteLimitsOfEqualizerTransfer
    [HasFiniteLimits C]
    [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions]
    [(boundedExactWeakEquivalence C).IsStableUnderFiniteProducts]
    [(boundedExactWeakEquivalence C).IsStableUnderLimitsOfShape WalkingParallelPair]
    (h : EqualizerLocalizationTransferTheorem C) :
    HasFiniteLimits (Dbounded C) := by
  letI : HasFiniteProducts (Dbounded C) := Dbounded.hasFiniteProductsOfStableFiniteProducts C
  letI : HasEqualizers (Dbounded C) := dboundedHasEqualizersOfTransferTheorem C h
  exact hasFiniteLimits_of_hasEqualizers_and_finite_products

/-- Current equalizer-transfer state at the W141 boundary. -/
structure EqualizerTransferState : Type where
  sourceEqualizersConstructor : String
  weakEquivalenceEqualizerStabilityConstructor : Option String
  localizationEqualizersConstructor : Option String
  targetEqualizersConstructor : Option String
  finiteLimitConsumer : String

/-- Reproducible state: source equalizers exist, but stability and localization transfer do not. -/
def currentEqualizerTransferState : EqualizerTransferState where
  sourceEqualizersConstructor := "boundedComplexHasEqualizersOfBaseFiniteLimits"
  weakEquivalenceEqualizerStabilityConstructor := none
  localizationEqualizersConstructor := none
  targetEqualizersConstructor := none
  finiteLimitConsumer := "dboundedHasFiniteLimitsOfEqualizerTransfer"

theorem currentEqualizerTransferState_stability_missing :
    currentEqualizerTransferState.weakEquivalenceEqualizerStabilityConstructor = none := rfl

theorem currentEqualizerTransferState_localization_missing :
    currentEqualizerTransferState.localizationEqualizersConstructor = none := rfl

theorem currentEqualizerTransferState_target_equalizers_missing :
    currentEqualizerTransferState.targetEqualizersConstructor = none := rfl

/-- Named next assumptions for the equalizer route. -/
def equalizerTransferHypothesisNames : List String :=
  ["HasFiniteLimits C",
    "(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions",
    "(boundedExactWeakEquivalence C).IsStableUnderFiniteProducts",
    "(boundedExactWeakEquivalence C).IsStableUnderLimitsOfShape WalkingParallelPair",
    "EqualizerLocalizationTransferTheorem C"]

theorem equalizerTransferHypothesisNames_count :
    equalizerTransferHypothesisNames.length = 5 := rfl

section Checks

#check boundedComplexHasEqualizersOfBaseFiniteLimits
#check EqualizerConeInput
#check isStableUnderEqualizers_of_equalizerConeInput
#check EqualizerLocalizationTransferTheorem
#check dboundedHasEqualizersOfTransferTheorem
#check dboundedHasFiniteLimitsOfEqualizerTransfer
#check EqualizerTransferState
#check currentEqualizerTransferState
#check currentEqualizerTransferState_stability_missing
#check currentEqualizerTransferState_localization_missing
#check currentEqualizerTransferState_target_equalizers_missing
#check equalizerTransferHypothesisNames
#check equalizerTransferHypothesisNames_count
#check CategoryTheory.MorphismProperty.IsStableUnderLimitsOfShape
#check CategoryTheory.Localization.hasFiniteProducts
#check Dbounded.hasFiniteProductsOfStableFiniteProducts
#check HasEqualizers
#check WalkingParallelPair

end Checks

end DboundedEqualizerPullbackTransferW141

end LeanLCAExactChallenge
