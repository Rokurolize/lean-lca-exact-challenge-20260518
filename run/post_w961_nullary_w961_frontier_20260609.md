# Post-W961 Nullary Frontier Probe

Generated UTC: 2026-06-09T14:17:41Z

Base checkpoint: `d69d0a5070793627b56ac5232177e987ffb97538` (`Expose W961 closedness product surface`)

Outcome: Tier A proof-search/read-only investigation. No Lean source was changed, and no product-success claim is made.

## Scope

The W961 checkpoint exposed an already checked route from
`ClosedEmbeddingClosednessFieldsInputW961` to the bounded-derived stable package
and to `OriginalFourTaskProductData`. This probe checks whether that new surface
is now nullary or whether it still requires explicit source data.

## Probe

Lean probe:

```text
run/post_w961_nullary_w961_frontier_probe_20260609.lean
```

Verification log:

```text
run/verify_post_w961_nullary_w961_frontier_probe_20260609.log
```

Command:

```text
lake env lean run/post_w961_nullary_w961_frontier_probe_20260609.lean
```

The command is expected to fail, because the probe deliberately asks Lean to
synthesize or construct the currently missing nullary data.

## Positive Shape Checks

The W961 product surface is present:

```text
ClosedEmbeddingClosednessFieldsInputW961 : Type 2
stablePackageOfClosedEmbeddingClosednessFieldsW961
  (input : ClosedEmbeddingClosednessFieldsInputW961) : StablePackage
originalFourTaskProductDataOfClosedEmbeddingClosednessFieldsW961
  (input : ClosedEmbeddingClosednessFieldsInputW961) : OriginalFourTaskProductData
```

W961 also exposes the route-data and direct-left-calculus projections, but only
from caller-supplied W961 leaves:

```text
routeDataProviderOfClosedEmbeddingClosednessFieldsW961
  (leaves : ...FieldLeavesW961) : MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732

directBoundedLeftCalculusOfClosedEmbeddingClosednessFieldsW961
  (leaves : ...FieldLeavesW961) :
  (boundedExactWeakEquivalence MetrizableLCA).HasLeftCalculusOfFractions
```

## W961 Input Surface

Lean printed the W961 structure and confirmed the existing count theorem:

```text
Dbounded.closedEmbeddingClosednessFieldsInputNamesW961.length = 18
```

The structure still contains explicit source-side fields, including:

- `sourcePretriangulated : Pretriangulated (BoundedComplexCategory MetrizableLCA)`
- `sourceTriangulated : IsTriangulated (BoundedComplexCategory MetrizableLCA)`
- `triangleCompletion : MetrizableBoundedExactWeakEquivalenceTriangleCompletionInputW654`
- `boundedHomotopyLocalizedRightAdjoint`
- `boundedHomotopyLocalizedAdjunction`
- `boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents`

It also keeps the WPP boundary, relation, closed-embedding, normalized-lift, and
fixed-target uniqueness leaves explicit.

## Failed Nullary Probes

The following syntheses failed on the current source:

```text
failed to synthesize
  Pretriangulated (BoundedComplexCategory MetrizableLCA)

failed to synthesize
  (boundedExactWeakEquivalence MetrizableLCA).HasLeftCalculusOfFractions

failed to synthesize
  Dbounded.MetrizableWalkingParallelPairFunctorCategoryLocalizationInput
```

The W961 input itself is also not constructible without an external witness:

```text
case leaves
|- ClosedEmbeddingClosednessFieldsInputW961
```

## Next Source API Needed

The smallest honest source patch remains one of:

```lean
noncomputable def BoundedDerived.Metrizable.stablePackage :
    BoundedDerived.Metrizable.StablePackage
```

or:

```lean
noncomputable def Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs :
    Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs
```

or:

```lean
noncomputable def Dbounded.metrizableW732RouteDataProvider :
    Dbounded.MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732
```

For the W961 branch specifically, a source patch would need to construct:

```lean
noncomputable def BoundedDerived.Metrizable.closedEmbeddingClosednessFieldsInputW961 :
    BoundedDerived.Metrizable.ClosedEmbeddingClosednessFieldsInputW961
```

This is not currently available from typeclass synthesis or existing nullary
source declarations.

## Product Status

`product_success` remains false. This checkpoint does not define
`OriginalFourTaskProductSuccess`, does not define `originalFourTaskProductSuccess`,
and does not permit `update_goal(status="complete")`.
