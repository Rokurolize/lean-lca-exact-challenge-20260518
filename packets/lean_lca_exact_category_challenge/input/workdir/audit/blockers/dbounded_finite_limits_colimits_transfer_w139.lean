import Mathlib.CategoryTheory.Localization.FiniteProducts
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import LeanLCAExactChallenge.Derived.Bounded

/-!
W139 audit: finite-limit transfer frontier for `Dbounded`.

The target already has finite limits in the source category of bounded complexes and a
conditional finite-products localization constructor for `Dbounded C`.  This file packages the
remaining finite-limit gap as the missing equalizer/pullback transfer across the bounded exact
weak-equivalence localization.

It is intentionally not a product-success proof: no unconditional constructor for
`HasFiniteLimits (Dbounded C)` is claimed.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace DboundedFiniteLimitsColimitsTransferW139

/-- Bounded complexes inherit finite products from the existing finite-limit source API. -/
noncomputable abbrev boundedComplexHasFiniteProductsOfBaseFiniteLimits
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasFiniteLimits C] :
    HasFiniteProducts (BoundedComplexCategory C) := by
  infer_instance

/-- Bounded complexes inherit equalizers from the existing finite-limit source API. -/
noncomputable abbrev boundedComplexHasEqualizersOfBaseFiniteLimits
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasFiniteLimits C] :
    HasEqualizers (BoundedComplexCategory C) := by
  infer_instance

/--
Finite-limit transfer inputs after the current `Dbounded` finite-products boundary.

The first three fields are the current strict-localization finite-products route.  The last
field is the genuinely missing finite-limit component: equalizers in the localized category,
which should come from a future equalizer/pullback stability theorem for
`boundedExactWeakEquivalence C`.
-/
structure DboundedFiniteLimitsTransferInputs
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type (max u v) where
  sourceFiniteLimits : HasFiniteLimits C
  leftCalculus : (boundedExactWeakEquivalence C).HasLeftCalculusOfFractions
  finiteProductStability : (boundedExactWeakEquivalence C).IsStableUnderFiniteProducts
  dboundedEqualizers : HasEqualizers (Dbounded C)

/--
Conditional finite-limit constructor.

This proves the ordinary category-theory reduction useful for the target: once the existing
finite-products localization path is available and equalizers have been transferred to
`Dbounded C`, Lean can synthesize finite limits for `Dbounded C`.
-/
noncomputable abbrev hasFiniteLimitsOfFiniteProductsAndEqualizers
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (inputs : DboundedFiniteLimitsTransferInputs C) :
    HasFiniteLimits (Dbounded C) := by
  letI : HasFiniteLimits C := inputs.sourceFiniteLimits
  letI : (boundedExactWeakEquivalence C).HasLeftCalculusOfFractions := inputs.leftCalculus
  letI : (boundedExactWeakEquivalence C).IsStableUnderFiniteProducts :=
    inputs.finiteProductStability
  letI : HasFiniteProducts (Dbounded C) := Dbounded.hasFiniteProductsOfStableFiniteProducts C
  letI : HasEqualizers (Dbounded C) := inputs.dboundedEqualizers
  exact hasFiniteLimits_of_hasEqualizers_and_finite_products

/-- Equivalent pullback-shaped finite-limit inputs for implementors who prefer pullbacks. -/
structure DboundedFiniteLimitsPullbackInputs
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type (max u v) where
  sourceFiniteLimits : HasFiniteLimits C
  leftCalculus : (boundedExactWeakEquivalence C).HasLeftCalculusOfFractions
  finiteProductStability : (boundedExactWeakEquivalence C).IsStableUnderFiniteProducts
  dboundedPullbacks : HasPullbacks (Dbounded C)

/-- Pullback-shaped conditional constructor for the same finite-limit frontier. -/
noncomputable abbrev hasFiniteLimitsOfFiniteProductsAndPullbacks
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (inputs : DboundedFiniteLimitsPullbackInputs C) :
    HasFiniteLimits (Dbounded C) := by
  letI : HasFiniteLimits C := inputs.sourceFiniteLimits
  letI : (boundedExactWeakEquivalence C).HasLeftCalculusOfFractions := inputs.leftCalculus
  letI : (boundedExactWeakEquivalence C).IsStableUnderFiniteProducts :=
    inputs.finiteProductStability
  letI : HasFiniteProducts (Dbounded C) := Dbounded.hasFiniteProductsOfStableFiniteProducts C
  letI : HasTerminal (Dbounded C) := inferInstance
  letI : HasPullbacks (Dbounded C) := inputs.dboundedPullbacks
  exact hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- Named assumptions for the equalizer-based route to `HasFiniteLimits (Dbounded C)`. -/
def finiteLimitsTransferHypothesisNames : List String :=
  ["HasFiniteLimits C",
    "(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions",
    "(boundedExactWeakEquivalence C).IsStableUnderFiniteProducts",
    "HasEqualizers (Dbounded C)",
    "equalizer transfer from BoundedComplexCategory C across Dbounded.localization"]

theorem finiteLimitsTransferHypothesisNames_count :
    finiteLimitsTransferHypothesisNames.length = 5 := rfl

/-- Named assumptions for the pullback-based route to `HasFiniteLimits (Dbounded C)`. -/
def finiteLimitsPullbackHypothesisNames : List String :=
  ["HasFiniteLimits C",
    "(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions",
    "(boundedExactWeakEquivalence C).IsStableUnderFiniteProducts",
    "HasPullbacks (Dbounded C)",
    "pullback transfer from BoundedComplexCategory C across Dbounded.localization"]

theorem finiteLimitsPullbackHypothesisNames_count :
    finiteLimitsPullbackHypothesisNames.length = 5 := rfl

/--
Current finite-limit transfer state.

`targetFiniteProductsConstructor` is present, but no equalizer/pullback finite-limit
localization constructor is currently named in the target.
-/
structure FiniteLimitsTransferState : Type where
  sourceFiniteLimitsConstructor : String
  targetFiniteProductsConstructor : String
  targetEqualizersConstructor : Option String
  targetPullbacksConstructor : Option String
  targetFiniteLimitsConstructor : Option String
  missingLocalizationApi : String

/-- Reproducible state at target v182/w139 integration. -/
def currentFiniteLimitsTransferState : FiniteLimitsTransferState where
  sourceFiniteLimitsConstructor := "BoundedComplexCategory.hasFiniteLimits"
  targetFiniteProductsConstructor := "Dbounded.hasFiniteProductsOfStableFiniteProducts"
  targetEqualizersConstructor := none
  targetPullbacksConstructor := none
  targetFiniteLimitsConstructor := none
  missingLocalizationApi :=
    "equalizer or pullback stability/creation for boundedExactWeakEquivalence C"

theorem currentFiniteLimitsTransferState_equalizers_missing :
    currentFiniteLimitsTransferState.targetEqualizersConstructor = none := rfl

theorem currentFiniteLimitsTransferState_pullbacks_missing :
    currentFiniteLimitsTransferState.targetPullbacksConstructor = none := rfl

theorem currentFiniteLimitsTransferState_finiteLimits_missing :
    currentFiniteLimitsTransferState.targetFiniteLimitsConstructor = none := rfl

/-- This route does not address the dual finite-colimit field. -/
def finiteColimitsStillSeparate : String :=
  "HasFiniteColimits (Dbounded C) needs the dual finite-coproduct/coequalizer transfer route."

section Checks

#check boundedComplexHasFiniteProductsOfBaseFiniteLimits
#check boundedComplexHasEqualizersOfBaseFiniteLimits
#check DboundedFiniteLimitsTransferInputs
#check hasFiniteLimitsOfFiniteProductsAndEqualizers
#check DboundedFiniteLimitsPullbackInputs
#check hasFiniteLimitsOfFiniteProductsAndPullbacks
#check finiteLimitsTransferHypothesisNames
#check finiteLimitsTransferHypothesisNames_count
#check finiteLimitsPullbackHypothesisNames
#check finiteLimitsPullbackHypothesisNames_count
#check FiniteLimitsTransferState
#check currentFiniteLimitsTransferState
#check currentFiniteLimitsTransferState_equalizers_missing
#check currentFiniteLimitsTransferState_pullbacks_missing
#check currentFiniteLimitsTransferState_finiteLimits_missing
#check finiteColimitsStillSeparate
#check CategoryTheory.Localization.hasFiniteProducts
#check CategoryTheory.MorphismProperty.IsStableUnderFiniteProducts
#check BoundedComplexCategory.hasFiniteLimits
#check Dbounded.hasFiniteProductsOfStableFiniteProducts
#check HasEqualizers
#check HasPullbacks
#check HasFiniteLimits
#check HasFiniteColimits

end Checks

end DboundedFiniteLimitsColimitsTransferW139

end LeanLCAExactChallenge
