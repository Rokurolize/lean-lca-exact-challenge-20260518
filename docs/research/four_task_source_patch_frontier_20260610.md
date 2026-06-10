# Four-Task Source Patch Frontier, 2026-06-10

This note is a durable source-patch handoff for the original four-task product witness. It is an evidence note, not a success marker.

## Product Status

The repository does not define `LeanLCAExactChallenge.OriginalFourTaskProductSuccess`. The checked product-data surface remains parameterized by source inputs for the bounded-derived stable package.

Durable anchors:

- `LeanLCAExactChallenge/OriginalFourTask/ProductData.lean` defines `OriginalFourTaskProductData` and intentionally does not define `OriginalFourTaskProductSuccess`.
- `originalFourTaskProductDataOfMetrizableStableInstances` needs the seven instance families listed by `Dbounded.metrizableStableInstanceFieldNames`.
- `originalFourTaskProductDataOfW1496RawFieldInputViaFullDataDirectLocalizationBoundary` consumes `BoundedDerived.Metrizable.W1496RawFieldInput` and routes through the W1625 full-data direct-localization boundary.
- `BoundedDerived.Metrizable.W1496RawFieldInput` is an abbreviation for `Dbounded.W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceHomologicalTriangulationDataConstructionInputW1496`.
- `w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceHomologicalTriangulationDataConstructionInputNamesW1496_count` proves that the W1496 source-homological-triangulation construction surface has 74 named inputs.
- `currentW1496W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceHomologicalTriangulationDataConstruction_productSuccess` proves its route state still has `productSuccessClaimed = false`.

## Narrow Source Patch Target

The shortest product-facing source patch is a nullary construction of `BoundedDerived.Metrizable.W1496RawFieldInput`, followed by the existing product route:

```lean
noncomputable def concreteW1496RawFieldInput :
    BoundedDerived.Metrizable.W1496RawFieldInput := by
  -- construct the W1496/W1495 source fields from real source theorems

noncomputable def OriginalFourTaskProductSuccess :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfW1496RawFieldInputViaFullDataDirectLocalizationBoundary
    concreteW1496RawFieldInput
```

An equivalent patch may bypass W1496, but it must still construct the same mathematical content: the exact-category data, metrizable LCA exact-category data, Yoneda Ext data, and a stable bounded-derived infinity-category package with no caller-supplied stable-package argument.

## W1496 Input Boundary

`W1496RawFieldInput` reuses W1495's source-triangulation field-data input and adds no new homology-provider input. The W1496 file records two relevant facts:

- `w1496SourceHomologicalTriangulationDataUsesComparisonBijectivityHomology` shows W855/W821 supplies the `CategoryWithHomology MetrizableLCA` provider.
- `w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceHomologicalTriangulationDataConstructionRemovedHomologyInputNamesW1496_count` shows the caller-supplied homology-provider input has been removed.

Therefore the source patch should focus on the W1495/W1496 remaining field list, not on adding another product-data adapter. Use `w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceHomologicalTriangulationDataConstructionInputNamesW1496` as the input checklist.

## Intermediate Routes To Avoid Rewrapping

The following routes are already wired into product-facing paths and should not be reintroduced as completion evidence:

- W841 derives finite limits, finite colimits, pretriangulated structure, and triangulated structure from W839 plus W653/W657 source data.
- W842 and W1533 derive W653 finite-shape data and W657 direct-localization data from later W987-style inputs.
- W1609, W1623, W1624, W1625, and the `BoundedDerived.MetrizableStableBridge` declarations already expose product data from W839, W1519, W1007, W1450, W1479, W1490, and W1496 surfaces.

Adding an equality theorem, route state, input-count theorem, or product-data wrapper around these declarations is not a source patch. A useful source patch must discharge, derive, or eliminate one of the named W1496/W1495 source fields.

## Verification For A Future Patch

A terminal patch should pass at least:

```bash
lake build LeanLCAExactChallenge
lake env lean audit/RequiredDeclarations.lean
lake env lean audit/ProductSuccessDeclarations.lean
lake env lean audit/OriginalFourTaskCompletionDeclarations.lean
scripts/audit_no_generated_files.sh
scripts/audit_no_forbidden_lean_tokens.sh LeanLCAExactChallenge audit
PYTHONDONTWRITEBYTECODE=1 python3 audit/external_audit.py --root .
git diff --check
```

The positive success claim must be backed by a Lean declaration, not by `productSuccessClaimed`, terminal JSON, route names, or generated audit text.
