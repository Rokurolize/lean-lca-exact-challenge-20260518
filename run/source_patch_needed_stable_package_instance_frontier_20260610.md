# Source Patch Needed: Stable Package Instance Frontier

Generated UTC: 2026-06-10T10:11:25Z

## Outcome

- `terminal_outcome`: `source_patch_needed_handoff`
- `product_success`: false
- `product_complete`: false
- `update_goal_allowed`: false
- Source head inspected: `07164eeeed0628be816d9b5a27a434c01583eba6`
- Latest source checkpoint: `run/stable_package_gate_bridge_checkpoint_20260610.md`

This checkpoint is post-bridge evidence. Commit `07164eee` makes an already supplied `BoundedDerived.Metrizable.StablePackage` consumable by the ordinary stable semantic input and the accepted four-projection stable gate, but it does not construct the package itself. Current source still has no nullary inhabitant for the stable bounded-derived package or for the W1450 field-data route.

## Files Inspected

- `LeanLCAExactChallenge/BoundedDerived/Basic.lean`
- `LeanLCAExactChallenge/Derived/Bounded.lean`
- `LeanLCAExactChallenge/Derived/BoundedFiniteProducts.lean`
- `LeanLCAExactChallenge/Derived/MetrizableStableInstanceBoundary.lean`
- `LeanLCAExactChallenge/Derived/MetrizableStableInstanceBoundaryDirectLocalization.lean`
- `LeanLCAExactChallenge/Derived/DirectLeftCalculusRoute.lean`
- `LeanLCAExactChallenge/LCA/ExactCategory.lean`
- `LeanLCAExactChallenge/Ext/Yoneda.lean`
- `run/source_patch_needed_w1450_nullary_frontier_20260610.md`
- `run/source_patch_needed_w1450_provider_leaf_reassessment_20260610.md`
- `run/stable_package_gate_bridge_checkpoint_20260610.md`

## What Current Source Proves

- `BoundedDerived.Metrizable.stablePackage_ordinaryStableSemanticInput` extracts the ordinary stable semantic fields from a caller-supplied `BoundedDerived.Metrizable.StablePackage`.
- `BoundedDerived.Metrizable.stablePackage_acceptedStable` turns that supplied package into `Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA`.
- `Dbounded.MetrizableStableInstanceBoundaryInputs` packages the existing canonical stable boundary as two source-facing inputs: direct bounded left calculus and WPP transfer-stable inputs.
- `Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs` refines that boundary to three source-facing inputs: WPP finite-shape transfer inputs, direct bounded left calculus, and the W657 direct-localization triangulated source core.
- `Dbounded.MetrizableDirectBoundedLeftCalculusDataW830` is the current concrete route to direct bounded left calculus.

## Stable Package Nullary Frontier

The product-facing stable package is not blocked by a missing adapter anymore. It is blocked by missing source inhabitants for the mathematical structures that populate `BoundedDerivedInfinityCategory MetrizableLCA (Dbounded.infinityCategory MetrizableLCA)`.

The smallest current stable-instance frontier is:

```lean
noncomputable def Dbounded.nullaryMetrizableStableInstanceBoundaryDirectLocalizationInputs :
    Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs
```

Equivalently, prove all three fields of `MetrizableStableInstanceBoundaryDirectLocalizationInputs` without caller-supplied records:

```lean
noncomputable def Dbounded.nullaryMetrizableWalkingParallelPairFiniteShapeTransferInputs :
    Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputs

theorem Dbounded.nullaryMetrizableBoundedExactWeakEquivalenceLeftCalculus :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions

noncomputable def Dbounded.nullaryMetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657 :
    MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657
```

`Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputs` itself still needs:

```lean
(boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape WalkingParallelPair
(boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderColimitsOfShape WalkingParallelPair
Dbounded.MetrizableWalkingParallelPairFunctorCategoryLocalizationInput
```

The direct-left-calculus route can also be attacked through W830:

```lean
noncomputable def Dbounded.nullaryMetrizableDirectBoundedLeftCalculusDataW830 :
    Dbounded.MetrizableDirectBoundedLeftCalculusDataW830
```

which expands to:

```lean
∀ S : ShortComplex MetrizableLCA.{0},
  IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
(exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂
MetrizableExactAtKernelCokernelConditionedTopologyInputs
BoundedHomotopyLocalizedRightAdjointInput MetrizableLCA.{0}
```

## Relationship To The W1450 Frontier

The W1450 route remains a separate, already recorded product-data frontier. Its four provider packages still expand to the eight leaf obligations listed in `run/source_patch_needed_w1450_provider_leaf_reassessment_20260610.md`.

This stable-package frontier is not a replacement wrapper around W1450. It is the other honest way to finish the bounded-derived task: construct the stable instance/package nullarily and feed it through the bridge added at `07164eee`.

## Rejected Next Steps

- Do not add another declaration that merely converts `StablePackage` to a route ledger, certificate, accepted gate, or product-data wrapper. Commit `07164eee` already supplies that adapter layer.
- Do not split `MetrizableStableInstanceBoundaryDirectLocalizationInputs` into larger caller-supplied route records unless the split simultaneously proves one of the three listed fields.
- Do not claim the original four-task witness from `BoundedDerived.Metrizable.StablePackage` until a nullary package or equivalent nullary stable-boundary inputs exist.

## Product Status

No declaration in current source honestly proves a nullary `OriginalFourTaskProductSuccess`. The bridge checkpoint only improves consumption of an already supplied stable package. Product success remains blocked on a genuine mathematical source patch: either the stable-package frontier above or one of the W1450 leaf APIs from the prior handoff.

## Next Safe Action

Implement one of the exact missing APIs above, preferably starting with the smallest independently checkable source theorem among WPP finite-shape transfer, direct bounded left calculus, or W657 direct localization. If no such theorem can be proved locally, stop with this handoff instead of adding another wrapper.
