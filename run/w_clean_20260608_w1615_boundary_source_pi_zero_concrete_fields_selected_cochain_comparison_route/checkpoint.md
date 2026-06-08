# W1615 Boundary Source-Pi-Zero Concrete-Fields Selected-Cochain Comparison Checkpoint

This is a nonterminal source-progress checkpoint for the original four-task contract. Product success is not claimed.

## Source Change

- Added `LeanLCAExactChallenge/Derived/BoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonProductRoute.lean`.
- Added the root import in `LeanLCAExactChallenge.lean`.
- W1615 feeds W1614 after assembling the W735 exact-input branch from its concrete field surface.
- The route exposes nine top-level branch fields:
  - bundled WPP right-open quotient-cover and source-pi-zero boundary data
  - bundled closed natural transformation ordinary relation data
  - target-only target-difference surjectivity plus target-codomain compactness provider
  - closed-map or closed-embedding selected-difference component provider
  - matching W519 mapped-explicit-cokernel closedness provider
  - normalized fixed-target data provider
  - source triangulation and triangle-completion data provider
  - endpoint strict-topology data provider
  - bounded homotopy localized-right-adjoint data provider

## Route Effect

W1614 required one W735 exact-input branch record. W1615 removes that wrapper from the top-level route surface by constructing the W735 record from concrete fields:

```lean
closedMapExactInputsOfConcreteFieldsSelectedCochainComparisonW1615 data
```

The closed-embedding branch uses the corresponding constructor. The checked W1615 input list has length nine:

```lean
boundarySourcePiZeroConcreteFieldsSelectedCochainComparisonInputNamesW1615_count :
  boundarySourcePiZeroConcreteFieldsSelectedCochainComparisonInputNamesW1615.length = 9
```

W1615 re-exposes W1614 product and stable-boundary outputs at the concrete-field selected-cochain comparison surface, including:

```lean
boundedDerivedOfClosedMapConcreteFieldsSelectedCochainComparisonW1615 :
  MetrizableClosedMapBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615 ->
    BoundedDerivedInfinityCategory MetrizableLCA
      (Dbounded.infinityCategory MetrizableLCA)

boundedDerivedOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615 :
  MetrizableClosedEmbeddingBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615 ->
    BoundedDerivedInfinityCategory MetrizableLCA
      (Dbounded.infinityCategory MetrizableLCA)
```

## Verification

- `lake env lean LeanLCAExactChallenge/Derived/BoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonProductRoute.lean` passed; see `w1615_module_lean.log`.
- `lake build LeanLCAExactChallenge.Derived.BoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonProductRoute` passed; see `w1615_lake_build.summary`.
- `lake env lean LeanLCAExactChallenge.lean` passed; see `root_lean.log`.
- `lake env lean run/w_clean_20260608_w1615_boundary_source_pi_zero_concrete_fields_selected_cochain_comparison_route/w1615_boundary_source_pi_zero_concrete_fields_selected_cochain_comparison_probe.lean` passed; see `probe.log`.
- `lake env lean audit/ProductSuccessDeclarations.lean` passed; see `product_success_declarations_summary.txt`.
- `lake env lean audit/OriginalFourTaskCompletionDeclarations.lean` passed; see `original_four_task_completion_declarations_summary.txt`.
- `jq empty terminal_outcome/terminal_outcome.json run/goal_identity_20260602_human_centered_positive_witness.json` passed; see `json_valid.log`.
- `python3 audit/original_four_task_contract_audit.py --root . --contract /home/roku/codex-consultant-20260517/outputs/proposed_goals/lean_lca_original_four_task_completion_contract_20260526.md --positive-witness-contract /home/roku/codex-consultant-20260517/outputs/proposed_goals/lean_lca_false_positive_recovery_20260530/lean_lca_positive_witness_completion_contract_20260530.md --terminal-outcome terminal_outcome/terminal_outcome.json` passed; see `original_four_task_contract_audit.json`.
- `scripts/audit_no_forbidden_lean_tokens.sh LeanLCAExactChallenge/Derived/BoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonProductRoute.lean LeanLCAExactChallenge.lean` passed; see `forbidden_tokens.log`.
- `git diff --check` passed; see `diff_check.log`.

## Contract Status

`terminal_outcome/terminal_outcome.json` remains nonterminal:

- `product_success = false`
- `product_success_claimed = false`
- `product_complete = false`
- `update_goal_allowed = false`

W1615 removes the W735 wrapper from the top-level selected-cochain comparison route, but it still depends on concrete branch-field values and does not construct the nullary original four-task witness. The goal must not be marked complete from this checkpoint.
