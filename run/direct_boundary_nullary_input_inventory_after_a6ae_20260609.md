# Direct-Boundary Nullary Input Inventory After W852

Generated: 2026-06-09T13:43:00Z

Base checkpoint: `a6ae7282d5458c2d6f423c4a0d060664422e8dc4` (`Add W852 route-data direct boundary checkpoint`)

Outcome: Tier A proof-search/read-only investigation. No Lean source was changed, and no product-success claim is made.

## Scope

This inventory resumes after W852 routed one `MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732` through the selected-cochain branch into the canonical direct-localization stable-instance boundary.

The remaining question was whether the current source already supplies a nullary direct-boundary input, especially one of:

- `Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs`;
- `(boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions`;
- `Dbounded.MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657`;
- `Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputs`;
- a concrete W732 route-data provider.

## Files Searched

- `LeanLCAExactChallenge/Derived/MetrizableStableInstanceBoundaryDirectLocalization.lean`
- `LeanLCAExactChallenge/Derived/WppOpExactAcyclicProjectionFields.lean`
- `LeanLCAExactChallenge/Derived/DirectWppLimitFiniteShapeTransfer.lean`
- `LeanLCAExactChallenge/Derived/DirectWppOpColimitFiniteShapeTransfer.lean`
- `LeanLCAExactChallenge/Derived/BoundedFiniteProducts.lean`
- `LeanLCAExactChallenge/Derived/TargetExactAtLeftCalculusRoute.lean`
- `LeanLCAExactChallenge/Derived/TargetIsoLeftCalculusRoute.lean`
- `LeanLCAExactChallenge/Derived/IsoClosureLeftCalculusRoute.lean`
- `LeanLCAExactChallenge/Derived/BranchLocalizedExactInputsLeftCalculusRoute.lean`

## Direct Boundary Shape

`LeanLCAExactChallenge/Derived/MetrizableStableInstanceBoundaryDirectLocalization.lean` defines:

```lean
structure Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs : Type 1 where
  transferInputs :
    Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputs
  directLeftCalculus :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions
  directLocalization :
    MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657
```

The module consumes these three fields and derives the accepted stable bounded-derived package, but it does not supply a nullary inhabitant of the structure.

`LeanLCAExactChallenge/Derived/WppOpExactAcyclicProjectionFields.lean` defines the W657 direct localization core as:

```lean
structure MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657 :
    Type 1 where
  sourcePretriangulated :
    Pretriangulated (BoundedComplexCategory MetrizableLCA.{0})
  sourceTriangulated :
    IsTriangulated (BoundedComplexCategory MetrizableLCA.{0})
  triangleCompletion :
    MetrizableBoundedExactWeakEquivalenceTriangleCompletionInputW654
```

This is a data structure, not a typeclass. It requires explicit source pretriangulation, source triangulation, and triangle-completion input.

## Lean Statements Attempted

Passing shape checks:

```text
lake env lean <probe>
```

with:

```lean
import LeanLCAExactChallenge.Derived.MetrizableStableInstanceBoundaryDirectLocalization
set_option autoImplicit false
namespace LeanLCAExactChallenge
#check Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs
#check Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputs
#check Dbounded.MetrizableWalkingParallelPairFunctorCategoryLocalizationInput
#check Dbounded.MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657
#check Dbounded.MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657.sourcePretriangulated
#check Dbounded.MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657.sourceTriangulated
#check Dbounded.MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657.triangleCompletion
#check (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions
end LeanLCAExactChallenge
```

Key output:

```text
LeanLCAExactChallenge.Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs : Type 1
LeanLCAExactChallenge.Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputs : Type 1
LeanLCAExactChallenge.Dbounded.MetrizableWalkingParallelPairFunctorCategoryLocalizationInput : Prop
LeanLCAExactChallenge.Dbounded.MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657 : Type 1
(boundedExactWeakEquivalence MetrizableLCA).HasLeftCalculusOfFractions : Prop
```

Failed typeclass probes:

```lean
#synth (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions
```

failed with:

```text
failed to synthesize
  (boundedExactWeakEquivalence MetrizableLCA).HasLeftCalculusOfFractions
```

```lean
#synth Dbounded.MetrizableWalkingParallelPairFunctorCategoryLocalizationInput
```

failed with:

```text
failed to synthesize
  Dbounded.MetrizableWalkingParallelPairFunctorCategoryLocalizationInput
```

```lean
noncomputable def probeDirectLocalization :
    Dbounded.MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657 :=
  inferInstance
```

failed with:

```text
type class instance expected
  MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657
```

## Search Results

Command:

```text
rg -n "RightOpenLcaInput_direct|RightSurjectiveLcaInput_direct|OpExactAcyclicClosureInput_direct|FunctorCategoryLocalizationInput_direct|WalkingParallelPairFiniteShapeTransferInputs_direct|StableInstanceBoundaryDirectLocalizationInputs_direct" LeanLCAExactChallenge/Derived -g '*.lean'
```

Result: no matches.

Command:

```text
rg -n "MetrizableWppLimitRightOpenLcaInput :=|MetrizableWppLimitRightOpenLcaInput$|MetrizableWppLimitRightSurjectiveLcaInput :=|MetrizableWppLimitRightSurjectiveLcaInput$|MetrizableWppOpExactAcyclicClosureInput :=|MetrizableWppOpExactAcyclicClosureInput$" LeanLCAExactChallenge/Derived -g '*.lean'
```

Result summary:

- route/product files carry `rightOpenLca`, `rightSurjectiveLca`, and `opExactAcyclicClosure` as fields;
- `ClosedQuotientEpiDirectComparison*` can derive right-open/right-surjective LCA inputs only from closed-quotient/equivalence data;
- `BoundarySourcePiZero*` and related product routes can derive op-exact-acyclic closure only from boundary/source/pi-zero or exact-input data;
- no searched declaration supplied the needed right-open/right-surjective/op-closure inputs as nullary data.

Command:

```text
rg -n "leftCalculus_of_|direct.*LeftCalculus|HasLeftCalculusOfFractions" LeanLCAExactChallenge/Derived/TargetExactAtLeftCalculusRoute.lean LeanLCAExactChallenge/Derived/TargetIsoLeftCalculusRoute.lean LeanLCAExactChallenge/Derived/IsoClosureLeftCalculusRoute.lean LeanLCAExactChallenge/Derived/BranchLocalizedExactInputsLeftCalculusRoute.lean LeanLCAExactChallenge/Derived/WppOpExactAcyclicProjectionFields.lean -g '*.lean'
```

Result summary:

- `directBoundedLeftCalculusOfTargetExactAtW832` requires `MetrizableTargetExactAtLeftCalculusDataW832`;
- `directBoundedLeftCalculusOfTargetIsoW833` requires `MetrizableTargetIsoLeftCalculusDataW833`;
- `directBoundedLeftCalculusOfIsoClosureRealizationW834` requires W834 route data;
- `directBoundedLeftCalculusOfClosedMapBranchLocalizedW836` and `directBoundedLeftCalculusOfClosedEmbeddingBranchLocalizedW836` require W836 route data;
- W604/W657 left-calculus routes require `hasHomology`, topology input, and localized-right-adjoint input.

Thus the current source has several parameterized left-calculus constructors, but no nullary `directLeftCalculus` for `boundedExactWeakEquivalence MetrizableLCA`.

Available direct pieces confirmed by Lean:

```lean
#check Dbounded.metrizableWppLimitComparisonInput_direct
#check Dbounded.metrizableWppLimitLeftClosedLcaInput_direct
#check Dbounded.metrizableWppLimitAlgebraicExactInput_direct
#check Dbounded.metrizableWalkingParallelPairLimitStability_of_directLeftAlgebraicRightLca
#check Dbounded.metrizableWalkingParallelPairFiniteShapeTransferInputs_of_directRightLcaOpClosure
```

Key output:

```text
Dbounded.metrizableWppLimitComparisonInput_direct : Dbounded.MetrizableWppLimitComparisonInput
Dbounded.metrizableWppLimitLeftClosedLcaInput_direct : Dbounded.MetrizableWppLimitLeftClosedLcaInput
Dbounded.metrizableWppLimitAlgebraicExactInput_direct : Dbounded.MetrizableWppLimitAlgebraicExactInput
Dbounded.metrizableWalkingParallelPairLimitStability_of_directLeftAlgebraicRightLca
  (inputs : Dbounded.MetrizableWalkingParallelPairLimitClosureFieldInputsFromDirectLeftAlgebraicRightLca) :
  (boundedExactWeakEquivalence MetrizableLCA).IsStableUnderLimitsOfShape WalkingParallelPair
Dbounded.metrizableWalkingParallelPairFiniteShapeTransferInputs_of_directRightLcaOpClosure
  (inputs : Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputsFromDirectRightLcaOpClosure) :
  Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputs
```

The direct comparison, left-closed, and algebraic-exact pieces are available. The helper still requires `rightOpenLca`, `rightSurjectiveLca`, `opExactAcyclicClosure`, and `functorCategoryLocalization`.

## Next Theorem/API Needed

The smallest honest source API after W852 is one of the following:

```lean
noncomputable def Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs :
    Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs
```

or the explicit three-field expansion:

```lean
noncomputable def Dbounded.metrizableDirectLeftCalculus :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions

noncomputable def Dbounded.metrizableDirectLocalizationTriangulatedSourceNoCommShiftCore :
    Dbounded.MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657

noncomputable def Dbounded.metrizableWalkingParallelPairFiniteShapeTransferInputs :
    Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputs
```

For the transfer input, the current best smaller route is:

```lean
noncomputable def Dbounded.metrizableWalkingParallelPairFiniteShapeTransferInputsFromDirectRightLcaOpClosure :
    Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputsFromDirectRightLcaOpClosure
```

which still needs:

- `Dbounded.MetrizableWppLimitRightOpenLcaInput`;
- `Dbounded.MetrizableWppLimitRightSurjectiveLcaInput`;
- `Dbounded.MetrizableWppOpExactAcyclicClosureInput`;
- `Dbounded.MetrizableWalkingParallelPairFunctorCategoryLocalizationInput`.

Equivalently, a concrete nullary route-data provider would bypass this branch:

```lean
noncomputable def Dbounded.metrizableW732RouteDataProvider :
    Dbounded.MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732
```

## Product Status

`product_success` remains false. This checkpoint records the direct-boundary input frontier after W852; it does not construct the original four-task positive witness and does not permit `update_goal(status="complete")`.
