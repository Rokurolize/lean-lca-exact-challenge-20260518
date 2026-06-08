# W1614 Boundary Source-Pi-Zero Exact-Inputs Selected-Cochain Comparison Checkpoint

This is a nonterminal source-progress checkpoint for the original four-task contract. Product success is not claimed.

## Source Change

- Added `LeanLCAExactChallenge/Derived/BoundarySourcePiZeroExactInputsSelectedCochainComparisonProductRoute.lean`.
- Added the root import in `LeanLCAExactChallenge.lean`.
- W1614 feeds W1613 after deriving W847 selected-cochain data from W851 comparison selected-cochain data.
- The route keeps one top-level branch input:
  - W735 closed-map or closed-embedding exact-input branch data

## Route Effect

W1613 required a W847 selected-cochain strictification field. W1614 removes that explicit field by converting one W735 exact-input branch through W851:

```lean
closedMapSelectedCochainDirectSourceDataOfComparisonW851 exactInputs
```

The closed-embedding branch uses the corresponding W851 conversion. The checked W1614 input list has length one:

```lean
boundarySourcePiZeroExactInputsSelectedCochainComparisonInputNamesW1614_count :
  boundarySourcePiZeroExactInputsSelectedCochainComparisonInputNamesW1614.length = 1
```

W1614 re-exposes W1613 product and stable-boundary outputs at the exact-input selected-cochain comparison surface, including:

```lean
boundedDerivedOfClosedMapExactInputsSelectedCochainComparisonW1614 :
  MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735 ->
    BoundedDerivedInfinityCategory MetrizableLCA
      (Dbounded.infinityCategory MetrizableLCA)

boundedDerivedOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614 :
  MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735 ->
    BoundedDerivedInfinityCategory MetrizableLCA
      (Dbounded.infinityCategory MetrizableLCA)
```

## Verification

- `lake env lean LeanLCAExactChallenge/Derived/BoundarySourcePiZeroExactInputsSelectedCochainComparisonProductRoute.lean` passed; see `w1614_module_lean.log`.
- `lake build LeanLCAExactChallenge.Derived.BoundarySourcePiZeroExactInputsSelectedCochainComparisonProductRoute` passed; see `w1614_lake_build.summary`.
- `lake env lean LeanLCAExactChallenge.lean` passed; see `root_lean.log`.
- `lake env lean run/w_clean_20260608_w1614_boundary_source_pi_zero_exact_inputs_selected_cochain_comparison_route/w1614_boundary_source_pi_zero_exact_inputs_selected_cochain_comparison_probe.lean` passed; see `probe.log`.
- `lake env lean audit/ProductSuccessDeclarations.lean` passed; see `product_success_declarations_summary.txt`.
- `lake env lean audit/OriginalFourTaskCompletionDeclarations.lean` passed; see `original_four_task_completion_declarations_summary.txt`.
- `jq empty terminal_outcome/terminal_outcome.json run/goal_identity_20260602_human_centered_positive_witness.json` passed; see `json_valid.log`.
- `python3 audit/original_four_task_contract_audit.py --root . --contract /home/roku/codex-consultant-20260517/outputs/proposed_goals/lean_lca_original_four_task_completion_contract_20260526.md --positive-witness-contract /home/roku/codex-consultant-20260517/outputs/proposed_goals/lean_lca_false_positive_recovery_20260530/lean_lca_positive_witness_completion_contract_20260530.md --terminal-outcome terminal_outcome/terminal_outcome.json` passed; see `original_four_task_contract_audit.json`.
- `scripts/audit_no_forbidden_lean_tokens.sh LeanLCAExactChallenge/Derived/BoundarySourcePiZeroExactInputsSelectedCochainComparisonProductRoute.lean LeanLCAExactChallenge.lean` passed; see `forbidden_tokens.log`.
- `git diff --check` passed; see `diff_check.log`.

## Contract Status

`terminal_outcome/terminal_outcome.json` remains nonterminal:

- `product_success = false`
- `product_success_claimed = false`
- `product_complete = false`
- `update_goal_allowed = false`

W1614 removes the separate W847 selected-cochain strictification surface from W1613, but it still depends on concrete W735 branch data and does not construct the nullary original four-task witness. The goal must not be marked complete from this checkpoint.
