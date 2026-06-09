# W947 Product Bridge And Nullary Stable Frontier

- generated_utc: 2026-06-09T06:05:27Z
- thread_id: 019ea5a4-a615-78b2-8944-d6f4ed0b24bb
- branch: goal-clean-positive-witness-20260609-019ea5a4
- product_success: false
- product_success_claimed: false

## Source Reduction

This checkpoint exposes the existing W947 closedness branch at the product-facing bridge. W947 projects definitionally to the W946 route while replacing two separate leaves, W944 target no-univ data and W725 diagram/mapped-cokernel closedness data, with one `TargetNoUnivMembershipClosednessDataProviderW947`.

The new product-facing surface is the six-field W947 input:

- W730 boundary/relation data.
- W947 target-no-univ/closedness data.
- W719 normalized fixed-target data.
- W722 source-triangulation data.
- endpoint strict short-exact witnesses.
- W945 localized-unit data.

This is still not a positive original-four-task witness. No `OriginalFourTaskProductSuccess` declaration is introduced, and the final product data remains conditional on a bounded-derived stable package.

## Nullary Stable Frontier

The final non-caller-supplied product data would need a nullary value of `BoundedDerived.Metrizable.StablePackage`. The current source has a typeclass route:

```lean
Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstances
```

The route becomes nullary only when the concrete `Dbounded MetrizableLCA` stable instance families are available. A local Lean probe importing `LeanLCAExactChallenge.OriginalFourTask.ProductData` confirmed they are not currently synthesized.

Probe target:

```lean
noncomputable def nullaryStablePackageProbe : BoundedDerived.Metrizable.StablePackage :=
  Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstances
```

Observed failure frontier:

```text
failed to synthesize Preadditive (Dbounded MetrizableLCA)
failed to synthesize Limits.HasFiniteLimits (Dbounded MetrizableLCA)
failed to synthesize Limits.HasFiniteColimits (Dbounded MetrizableLCA)
failed to synthesize Limits.HasZeroObject (Dbounded MetrizableLCA)
failed to synthesize shift additivity for shiftFunctor (Dbounded MetrizableLCA)
failed to synthesize Pretriangulated (Dbounded MetrizableLCA)
failed to synthesize IsTriangulated (Dbounded MetrizableLCA)
```

The next real proof step is not another product wrapper. It is source-level construction, or canonical instance registration, for these stable `Dbounded MetrizableLCA` fields without carrying them as an explicit route input.

## Changed Paths

- `LeanLCAExactChallenge/BoundedDerived/MetrizableStableBridge.lean`
- `LeanLCAExactChallenge/OriginalFourTask/ProductData.lean`
- `audit/ProductSuccessDeclarations.lean`
- `run/w947_product_bridge_nullary_stable_frontier_20260609.md`

## Lean Declarations Added

- `BoundedDerived.Metrizable.ClosednessEndpointLocalizedUnitBoundaryRelationTargetNoUnivClosednessInput`
- `BoundedDerived.Metrizable.closednessEndpointLocalizedUnitBoundaryRelationInputOfTargetNoUnivClosednessInput`
- `BoundedDerived.Metrizable.stablePackageOfClosednessEndpointLocalizedUnitBoundaryRelationTargetNoUnivClosednessInput`
- `BoundedDerived.Metrizable.stablePackageOfClosednessEndpointLocalizedUnitBoundaryRelationTargetNoUnivClosednessInput_eq_w947`
- `BoundedDerived.Metrizable.stablePackageOfClosednessEndpointLocalizedUnitBoundaryRelationTargetNoUnivClosednessInput_eq_localizedUnitBoundaryRelationInput`
- `originalFourTaskProductDataOfClosednessEndpointLocalizedUnitBoundaryRelationTargetNoUnivClosednessInput`
- `originalFourTaskProductDataOfW947_eq_localizedUnitBoundaryRelationInput`
- `originalFourTaskProductDataOfW947_boundedDerivedInfinityCategory`
- `originalFourTaskProductDataOfW947_metrizableLCAExactCategory`
- `originalFourTaskProductDataOfW947_yonedaExt`

## Verification

Tier B checks run:

- `lake env lean LeanLCAExactChallenge/BoundedDerived/MetrizableStableBridge.lean`
- `lake build LeanLCAExactChallenge.BoundedDerived.MetrizableStableBridge`
- `lake env lean LeanLCAExactChallenge/OriginalFourTask/ProductData.lean`
- `lake build LeanLCAExactChallenge.OriginalFourTask.ProductData`
- `lake env lean audit/ProductSuccessDeclarations.lean > /dev/null`
- `lake env lean audit/OriginalFourTaskCompletionDeclarations.lean > /dev/null`
- `scripts/audit_no_forbidden_lean_tokens.sh LeanLCAExactChallenge/BoundedDerived/MetrizableStableBridge.lean LeanLCAExactChallenge/OriginalFourTask/ProductData.lean audit/ProductSuccessDeclarations.lean`
- `git diff --check`

Known warnings remain style/reducibility warnings in imported modules and `ProductData.lean`; they do not introduce Lean errors.

## Next Safe Action

Work on a direct source-level constructor for `Preadditive`, finite limits, finite colimits, zero object, shift additivity, `Pretriangulated`, and `IsTriangulated` on `Dbounded MetrizableLCA`, preferably through the existing finite-products and walking-parallel-pair transfer routes, without packaging those facts as a new caller-supplied product input.
