# Source Patch Needed: Nullary Stable Package

Generated UTC: 2026-06-09T12:48:00Z

## Outcome

- `terminal_outcome`: `source_patch_needed_handoff`
- `product_success`: false
- `product_complete`: false
- `update_goal_allowed`: false
- Source base head inspected: `19f35cffc332893d59399c3140fa251f4d6fa67f`

This Tier A proof search made no product-facing Lean source change. It stops adding W-route wrappers and records the precise source theorem/API needed for the original positive witness.

## Files Searched

- `LeanLCAExactChallenge/ExactCategory/Basic.lean`
- `LeanLCAExactChallenge/LCA/ExactCategory.lean`
- `LeanLCAExactChallenge/Ext/Yoneda.lean`
- `LeanLCAExactChallenge/BoundedDerived/Basic.lean`
- `LeanLCAExactChallenge/BoundedDerived/MetrizableStableBridge.lean`
- `LeanLCAExactChallenge/OriginalFourTask/ProductData.lean`
- `LeanLCAExactChallenge/Derived/Bounded.lean`
- `LeanLCAExactChallenge/Derived/MetrizableStableInstanceBoundary.lean`
- `LeanLCAExactChallenge/Derived/MetrizableStableInstanceBoundaryDirectLocalization.lean`
- `LeanLCAExactChallenge/Derived/DirectLeftCalculusRoute.lean`
- `LeanLCAExactChallenge/Derived/ComparisonBijectivityLeftCalculusRoute.lean`
- `LeanLCAExactChallenge/Derived/DirectWppLimitFiniteShapeTransfer.lean`
- `LeanLCAExactChallenge/Derived/WppOpExactAcyclicProjectionFields.lean`

## Current Direct Coverage

Task 1 and Task 2 have direct canonical declarations in current source: `MetrizableLCA.quillenExactCategory`, `MetrizableLCA.quillenConflation_iff_closed_inclusion_open_surjection_algebraic_exact`, and `MetrizableLCA.quillenConflation_iff_closed_inclusion_open_surjection_forget_kernel_cokernel`.

Task 3 has direct canonical declarations through `YonedaExt`, and `OriginalFourTaskProductData` records `yonedaExt`, `yonedaExtAddCommGroup`, and `yonedaExtZeroEquivHom`.

Task 4 is still not nullary. `OriginalFourTaskProductData` intentionally requires a caller-supplied `BoundedDerived.Metrizable.StablePackage`, and the file explicitly says it does not define `OriginalFourTaskProductSuccess`.

## Lean Attempt

Scratch file:

```text
run/tier_a_nullary_stable_package_attempt_20260609.lean
```

Saved output log:

```text
run/verify_tier_a_nullary_stable_package_attempt_20260609.log
```

Key attempted statements:

```lean
#check BoundedDerived.Metrizable.StablePackage
#check OriginalFourTaskProductData
#check originalFourTaskProductDataOfStablePackage
#check Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs
#check (inferInstance :
  (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions)

noncomputable def attemptedNullaryStablePackage :
    BoundedDerived.Metrizable.StablePackage := by
  exact
    Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization
      ?boundaryInputs
```

Command:

```bash
lake env lean run/tier_a_nullary_stable_package_attempt_20260609.lean
```

Result: expected nonzero proof-search failure.

Important output:

```text
LeanLCAExactChallenge.BoundedDerived.Metrizable.StablePackage : Type 2
LeanLCAExactChallenge.OriginalFourTaskProductData : Type 2
LeanLCAExactChallenge.originalFourTaskProductDataOfStablePackage (P : BoundedDerived.Metrizable.StablePackage) :
  OriginalFourTaskProductData
LeanLCAExactChallenge.Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs : Type 1
LeanLCAExactChallenge.Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputNames_count :
  Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputNames.length = 3
LeanLCAExactChallenge.Dbounded.directBoundedLeftCalculusOfKernelCokernelComparisonW830
  (data : Dbounded.MetrizableDirectBoundedLeftCalculusDataW830) :
  (boundedExactWeakEquivalence MetrizableLCA).HasLeftCalculusOfFractions
```

Error signatures:

```text
failed to synthesize instance of type class
  (boundedExactWeakEquivalence MetrizableLCA).HasLeftCalculusOfFractions

don't know how to synthesize placeholder for argument `inputs`
⊢ Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs

unsolved goals
⊢ BoundedDerived.Metrizable.StablePackage
```

## Exact Missing Source API

The smallest useful source patch is one of the following, proved without assumptions, adapters, arbitrary `Prop` fields, or caller-supplied records:

```lean
noncomputable def BoundedDerived.Metrizable.stablePackage :
    BoundedDerived.Metrizable.StablePackage
```

or equivalently:

```lean
noncomputable def Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs :
    Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs
```

The second statement must honestly provide these three fields:

```lean
transferInputs :
  Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputs

directLeftCalculus :
  (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions

directLocalization :
  Dbounded.MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657
```

Those fields expand to the following mathematical obligations:

```lean
-- transferInputs
limitStability :
  (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
    WalkingParallelPair
colimitStability :
  (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderColimitsOfShape
    WalkingParallelPair
functorCategoryLocalization :
  Dbounded.MetrizableWalkingParallelPairFunctorCategoryLocalizationInput

-- directLocalization
sourcePretriangulated :
  Pretriangulated (BoundedComplexCategory MetrizableLCA.{0})
sourceTriangulated :
  IsTriangulated (BoundedComplexCategory MetrizableLCA.{0})
triangleCompletion :
  Dbounded.MetrizableBoundedExactWeakEquivalenceTriangleCompletionInputW654
```

`directLeftCalculus` is not currently inferable as an instance. The nearest declarations are still parameterized, for example:

```lean
Dbounded.directBoundedLeftCalculusOfKernelCokernelComparisonW830
  (data : Dbounded.MetrizableDirectBoundedLeftCalculusDataW830) :
  (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions

Dbounded.directBoundedLeftCalculusOfComparisonBijectivityW831
  (data : Dbounded.MetrizableDirectBoundedLeftCalculusDataWithoutComparisonW831) :
  (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions
```

## Why This Blocks Product Success

The final witness would be easy only after the stable package is nullary:

```lean
noncomputable def originalFourTaskProductSuccess :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStablePackage BoundedDerived.Metrizable.stablePackage
```

At current head this would be a false positive because `BoundedDerived.Metrizable.stablePackage` is not constructible from current source without providing the missing stable-boundary inputs above.

## Next Safe Action

Work on a canonical source patch proving the nullary stable package, starting from the three direct-localization boundary fields. Do not add another W-number product bridge unless it actually constructs one of these missing fields or proves that a smaller canonical theorem eliminates it.
