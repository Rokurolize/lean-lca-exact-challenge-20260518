# ProductData Task 2/3 Projection Checkpoint

- generated_utc: 2026-06-10T02:26:00Z
- base_head: 7f271aae29295e3ea3a909f92aaa645c9e018e9f
- product_success: false
- product_complete: false
- update_goal_allowed: false
- commit_made: yes, in the checkpoint commit containing this note

This checkpoint does not complete the original four-task positive witness. It records a small canonical ProductData improvement after inspecting the W601/W713/W944 target frontier and confirming that a nullary arbitrary-target target-difference or compactness provider would be mathematically dishonest.

## Source Changes

`LeanLCAExactChallenge/OriginalFourTask/ProductData.lean` now names three stable-package projections that were already present as fields of `OriginalFourTaskProductData`:

```lean
theorem originalFourTaskProductDataOfStablePackage_quillenExactCategory
theorem originalFourTaskProductDataOfStablePackage_metrizableLCAConflationIff
theorem originalFourTaskProductDataOfStablePackage_yonedaExtZeroEquivHom
```

These expose the canonical Task 1/2 exact-category surface and the Task 3 degree-zero Ext-to-Hom comparison without adding a new caller-supplied mathematical assumption. The existing `originalFourTaskProductDataOfStablePackage_yonedaExtAddCommGroup` extraction is now marked `@[reducible]`, removing the Lean warning about defining a class-valued declaration without reducibility.

`audit/RequiredDeclarations.lean` now checks the new field projections and the corresponding `OriginalFourTaskProductData` fields:

```lean
#check LeanLCAExactChallenge.OriginalFourTaskProductData.quillenExactCategory
#check LeanLCAExactChallenge.OriginalFourTaskProductData.metrizableLCAConflationIff
#check LeanLCAExactChallenge.OriginalFourTaskProductData.yonedaExtZeroEquivHom
#check LeanLCAExactChallenge.originalFourTaskProductDataOfStablePackage_quillenExactCategory
#check LeanLCAExactChallenge.originalFourTaskProductDataOfStablePackage_metrizableLCAConflationIff
#check LeanLCAExactChallenge.originalFourTaskProductDataOfStablePackage_yonedaExtZeroEquivHom
```

## Verification

- `lake env lean LeanLCAExactChallenge/OriginalFourTask/ProductData.lean`: passed.
- `lake build LeanLCAExactChallenge.OriginalFourTask.ProductData`: passed. Existing unrelated lint warnings remain in older imported modules; the prior ProductData class-valued-definition warning is absent.
- `lake env lean audit/RequiredDeclarations.lean`: passed after rebuilding `LeanLCAExactChallenge.OriginalFourTask.ProductData` so the audit saw the updated `.olean`.
- `git diff --check -- LeanLCAExactChallenge/OriginalFourTask/ProductData.lean audit/RequiredDeclarations.lean`: passed.
- `scripts/audit_no_forbidden_lean_tokens.sh LeanLCAExactChallenge/OriginalFourTask/ProductData.lean`: passed.

## Remaining Frontier

The final product witness remains nonterminal. `OriginalFourTaskProductData` still requires a caller-supplied `BoundedDerived.Metrizable.StablePackage`, and no nullary `OriginalFourTaskProductSuccess` declaration is introduced.

The W601/W713/W944 target route inspection found that the arbitrary-target statements still carried by those routes are not true in full generality: arbitrary WPP-op targets do not supply universal surjectivity of `left - right`, and arbitrary codomains are not compact spaces. Further progress should either construct the remaining bounded-derived stable package from a true restricted target API, continue reducing the direct-localization boundary inputs, or write a precise source-patch-needed handoff for the missing nullary stable package.
