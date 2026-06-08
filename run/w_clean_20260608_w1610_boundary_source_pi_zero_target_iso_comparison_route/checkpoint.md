# W1610 Boundary Source-Pi-Zero Target-Isomorphism Comparison Checkpoint

This is a nonterminal source-progress checkpoint for the original four-task contract. Product success is not claimed.

## Source Change

- Added `LeanLCAExactChallenge/Derived/BoundarySourcePiZeroTargetIsoComparisonProductRoute.lean`.
- Added the root import in `LeanLCAExactChallenge.lean`.
- W1610 feeds W1609 after deriving W839 target-homology-zero branch data from W844 target-isomorphism direct-source route data.
- The route keeps two top-level branch inputs:
  - W784 exact-acyclic homotopy-object target-isomorphism realization data
  - W735 closed-map or closed-embedding exact-input branch data

## Route Effect

W1609 required a target-homology-zero branch surface with a W790 payload provider. W1610 removes that explicit W790 surface by converting W844 target-isomorphism route data to W839 data:

```lean
closedMapTargetHomologyZeroDataOfTargetIsoW844 data
```

The closed-embedding branch uses the corresponding W844 conversion. The checked W1610 input list has length two:

```lean
boundarySourcePiZeroTargetIsoComparisonInputNamesW1610_count :
  boundarySourcePiZeroTargetIsoComparisonInputNamesW1610.length = 2
```

W1610 re-exposes W1609 product and stable-boundary outputs at the target-isomorphism comparison surface, including:

```lean
boundedDerivedOfClosedMapTargetIsoComparisonW1610 :
  MetrizableClosedMapTargetIsoDirectSourceStableRouteDataW844 ->
    BoundedDerivedInfinityCategory MetrizableLCA
      (Dbounded.infinityCategory MetrizableLCA)

boundedDerivedOfClosedEmbeddingTargetIsoComparisonW1610 :
  MetrizableClosedEmbeddingTargetIsoDirectSourceStableRouteDataW844 ->
    BoundedDerivedInfinityCategory MetrizableLCA
      (Dbounded.infinityCategory MetrizableLCA)
```

## Verification

- `lake env lean LeanLCAExactChallenge/Derived/BoundarySourcePiZeroTargetIsoComparisonProductRoute.lean` passed; see `w1610_module_lean.log`.
- `lake build LeanLCAExactChallenge.Derived.BoundarySourcePiZeroTargetIsoComparisonProductRoute` passed; see `w1610_lake_build.summary`.
- `lake env lean LeanLCAExactChallenge.lean` passed; see `root_lean.log`.
- `lake env lean run/w_clean_20260608_w1610_boundary_source_pi_zero_target_iso_comparison_route/w1610_boundary_source_pi_zero_target_iso_comparison_probe.lean` passed; see `probe.log`.
- `lake env lean audit/ProductSuccessDeclarations.lean` passed; see `product_success_declarations_summary.txt`.
- `lake env lean audit/OriginalFourTaskCompletionDeclarations.lean` passed; see `original_four_task_completion_declarations_summary.txt`.
- `jq empty terminal_outcome/terminal_outcome.json run/goal_identity_20260602_human_centered_positive_witness.json` passed; see `json_valid.log`.
- `python3 audit/original_four_task_contract_audit.py --root . --contract /home/roku/codex-consultant-20260517/outputs/proposed_goals/lean_lca_original_four_task_completion_contract_20260526.md --positive-witness-contract /home/roku/codex-consultant-20260517/outputs/proposed_goals/lean_lca_false_positive_recovery_20260530/lean_lca_positive_witness_completion_contract_20260530.md --terminal-outcome terminal_outcome/terminal_outcome.json` passed; see `original_four_task_contract_audit.json`.
- `scripts/audit_no_forbidden_lean_tokens.sh LeanLCAExactChallenge/Derived/BoundarySourcePiZeroTargetIsoComparisonProductRoute.lean LeanLCAExactChallenge.lean` passed; see `forbidden_tokens.log`.
- `git diff --check` passed; see `diff_check.log`.

## Contract Status

`terminal_outcome/terminal_outcome.json` remains nonterminal:

- `product_success = false`
- `product_success_claimed = false`
- `product_complete = false`
- `update_goal_allowed = false`

W1610 removes the separate W790 target-homology-zero payload surface from W1609, but it still depends on W784 target-isomorphism realization data and W735 branch data. It does not construct the nullary original four-task witness. The goal must not be marked complete from this checkpoint.
