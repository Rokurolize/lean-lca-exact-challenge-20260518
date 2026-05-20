import Mathlib.CategoryTheory.Localization.FiniteProducts
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import LeanLCAExactChallenge.Derived.Bounded

/-!
W143 audit: pullback transfer frontier for `Dbounded`.

The SSoT-selected route is the pullback analogue of W141's equalizer frontier.  W139 already
showed that `HasPullbacks (Dbounded C)`, together with the existing finite-product
localization route, is enough to construct `HasFiniteLimits (Dbounded C)`.  This file makes
the pullback-specific missing hypotheses explicit:

* source bounded-complex pullbacks are available from `HasFiniteLimits C`;
* the weak-equivalence stability input is
  `(boundedExactWeakEquivalence C).IsStableUnderLimitsOfShape WalkingCospan`;
* the absent localization theorem is a pullback-transfer theorem for `Dbounded.localization`.

This is a compiling frontier audit, not product success.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace DboundedPullbackLocalizationTransferW143

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
  [HasBinaryBiproducts C]

/-- Bounded complexes inherit pullbacks from the existing finite-limit source API. -/
noncomputable abbrev boundedComplexHasPullbacksOfBaseFiniteLimits
    [HasFiniteLimits C] :
    HasPullbacks (BoundedComplexCategory C) := by
  infer_instance

/--
The pullback-shaped mapping-cone input for `boundedExactWeakEquivalence`.

For `WalkingCospan`, the cone point is a pullback object.  A future proof should compare the
mapping cone of the induced morphism between pullback objects with the pullback-shaped limit
of the component mapping cones, then transport exact acyclicity.
-/
abbrev PullbackConeInput : Prop :=
  ∀ (X₁ X₂ : WalkingCospan ⥤ BoundedComplexCategory C)
    (c₁ : Cone X₁) (c₂ : Cone X₂)
    (_h₁ : IsLimit c₁) (_h₂ : IsLimit c₂)
    (f : X₁ ⟶ X₂),
    (∀ j, boundedExactWeakEquivalence C (f.app j)) →
      ∀ (φ : c₁.pt ⟶ c₂.pt),
        (∀ j, φ ≫ c₂.π.app j = c₁.π.app j ≫ f.app j) →
          boundedExactWeakEquivalence C φ

/-- The pullback cone input is exactly `WalkingCospan` stability. -/
theorem isStableUnderPullbacks_of_pullbackConeInput
    (h : PullbackConeInput C) :
    (boundedExactWeakEquivalence C).IsStableUnderLimitsOfShape WalkingCospan where
  condition X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ := h X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ

/--
The missing localization theorem for the pullback route.

The dependency snapshot exposes `Localization.hasFiniteProducts`, but source scans did not
find a generic `Localization.hasPullbacks` theorem.  This is the exact theorem shape needed
to transfer source pullbacks across `Dbounded.localization`.
-/
abbrev PullbackLocalizationTransferTheorem : Prop :=
  ∀ [HasFiniteLimits C]
    [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions]
    [(boundedExactWeakEquivalence C).IsStableUnderLimitsOfShape WalkingCospan],
      HasPullbacks (Dbounded C)

/-- If the missing localization theorem is supplied, the selected route gives pullbacks. -/
noncomputable abbrev dboundedHasPullbacksOfTransferTheorem
    [HasFiniteLimits C]
    [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions]
    [(boundedExactWeakEquivalence C).IsStableUnderLimitsOfShape WalkingCospan]
    (h : PullbackLocalizationTransferTheorem C) :
    HasPullbacks (Dbounded C) :=
  h

/--
Combining pullback transfer with the existing finite-product localization route closes the
ordinary finite-limit gap identified by W139.
-/
noncomputable abbrev dboundedHasFiniteLimitsOfPullbackTransfer
    [HasFiniteLimits C]
    [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions]
    [(boundedExactWeakEquivalence C).IsStableUnderFiniteProducts]
    [(boundedExactWeakEquivalence C).IsStableUnderLimitsOfShape WalkingCospan]
    (h : PullbackLocalizationTransferTheorem C) :
    HasFiniteLimits (Dbounded C) := by
  letI : HasFiniteProducts (Dbounded C) := Dbounded.hasFiniteProductsOfStableFiniteProducts C
  letI : HasTerminal (Dbounded C) := inferInstance
  letI : HasPullbacks (Dbounded C) := dboundedHasPullbacksOfTransferTheorem C h
  exact hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- Pullback-transfer state at the W143 boundary. -/
structure PullbackTransferState : Type where
  sourcePullbacksConstructor : String
  weakEquivalencePullbackStabilityConstructor : Option String
  localizationPullbacksConstructor : Option String
  targetPullbacksConstructor : Option String
  finiteLimitConsumer : String
  equalizerRouteDependency : Bool

/--
Reproducible state: source pullbacks exist, but the weak-equivalence stability proof and
localization transfer theorem are still absent.  This route does not depend on an equalizer
transfer theorem.
-/
def currentPullbackTransferState : PullbackTransferState where
  sourcePullbacksConstructor := "boundedComplexHasPullbacksOfBaseFiniteLimits"
  weakEquivalencePullbackStabilityConstructor := none
  localizationPullbacksConstructor := none
  targetPullbacksConstructor := none
  finiteLimitConsumer := "dboundedHasFiniteLimitsOfPullbackTransfer"
  equalizerRouteDependency := false

theorem currentPullbackTransferState_stability_missing :
    currentPullbackTransferState.weakEquivalencePullbackStabilityConstructor = none := rfl

theorem currentPullbackTransferState_localization_missing :
    currentPullbackTransferState.localizationPullbacksConstructor = none := rfl

theorem currentPullbackTransferState_target_pullbacks_missing :
    currentPullbackTransferState.targetPullbacksConstructor = none := rfl

theorem currentPullbackTransferState_not_equalizer_dependent :
    currentPullbackTransferState.equalizerRouteDependency = false := rfl

/-- Named next assumptions for the pullback route. -/
def pullbackTransferHypothesisNames : List String :=
  ["HasFiniteLimits C",
    "(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions",
    "(boundedExactWeakEquivalence C).IsStableUnderFiniteProducts",
    "(boundedExactWeakEquivalence C).IsStableUnderLimitsOfShape WalkingCospan",
    "PullbackLocalizationTransferTheorem C"]

theorem pullbackTransferHypothesisNames_count :
    pullbackTransferHypothesisNames.length = 5 := rfl

section Checks

#check boundedComplexHasPullbacksOfBaseFiniteLimits
#check PullbackConeInput
#check isStableUnderPullbacks_of_pullbackConeInput
#check PullbackLocalizationTransferTheorem
#check dboundedHasPullbacksOfTransferTheorem
#check dboundedHasFiniteLimitsOfPullbackTransfer
#check PullbackTransferState
#check currentPullbackTransferState
#check currentPullbackTransferState_stability_missing
#check currentPullbackTransferState_localization_missing
#check currentPullbackTransferState_target_pullbacks_missing
#check currentPullbackTransferState_not_equalizer_dependent
#check pullbackTransferHypothesisNames
#check pullbackTransferHypothesisNames_count
#check CategoryTheory.MorphismProperty.IsStableUnderLimitsOfShape
#check CategoryTheory.Localization.hasFiniteProducts
#check Dbounded.hasFiniteProductsOfStableFiniteProducts
#check HasPullbacks
#check WalkingCospan

end Checks

end DboundedPullbackLocalizationTransferW143

end LeanLCAExactChallenge
