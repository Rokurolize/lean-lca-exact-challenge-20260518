# W1607 Boundary Source-Pi-Zero Target-ExactAt Stable-Closure Checkpoint

This is a nonterminal source-progress checkpoint for the original four-task contract. Product success is not claimed.

## Source Change

- Added `LeanLCAExactChallenge/Derived/BoundarySourcePiZeroTargetExactAtStableClosureProductRoute.lean`.
- Added the root import in `LeanLCAExactChallenge.lean`.
- W1607 feeds W1606 after deriving the W1606 closed-two input from W796 target ExactAt closed-range data.
- The route keeps three top-level branch inputs:
  - universal W736 left-right comparison isomorphism
  - exact-acyclic homotopy-object target ExactAt realization data
  - W735 closed-map or closed-embedding exact-input branch data

## Route Effect

W1606 required a separate `exactAcyclicHomotopyIsoClosure MetrizableLCA` closed-two input. W1607 removes that explicit input by constructing W1606 branch data with:

```lean
exactClosed2 :=
  exactClosed2OfTargetExactAtClosedRangeW796
    (closedRangeEndpointTopologyOfClosedMapExactInputsW790 data.exactInputs)
    data.targetExactAtPayload
```

The closed-embedding branch uses the corresponding W790 closed-range endpoint topology projection. The checked W1607 input list has length three:

```lean
boundarySourcePiZeroTargetExactAtStableClosureInputNamesW1607_count :
  boundarySourcePiZeroTargetExactAtStableClosureInputNamesW1607.length = 3
```

W1607 re-exposes W1606 stable-boundary products at this target-ExactAt surface, including:

```lean
boundedDerivedOfClosedMapTargetExactAtW1607 :
  MetrizableClosedMapBoundarySourcePiZeroTargetExactAtBranchDataW1607 ->
    BoundedDerivedInfinityCategory MetrizableLCA
      (Dbounded.infinityCategory MetrizableLCA)

boundedDerivedOfClosedEmbeddingTargetExactAtW1607 :
  MetrizableClosedEmbeddingBoundarySourcePiZeroTargetExactAtBranchDataW1607 ->
    BoundedDerivedInfinityCategory MetrizableLCA
      (Dbounded.infinityCategory MetrizableLCA)
```

## Verification

- `lake env lean LeanLCAExactChallenge/Derived/BoundarySourcePiZeroTargetExactAtStableClosureProductRoute.lean` passed; see `w1607_module_lean.log`.
- `lake build LeanLCAExactChallenge.Derived.BoundarySourcePiZeroTargetExactAtStableClosureProductRoute` passed; see `w1607_lake_build.summary`.
- `lake env lean LeanLCAExactChallenge.lean` passed; see `root_lean.log`.
- `lake env lean run/w_clean_20260608_w1607_boundary_source_pi_zero_target_exact_at_stable_closure/w1607_boundary_source_pi_zero_target_exact_at_stable_closure_probe.lean` passed; see `probe.log`.
- `lake env lean audit/ProductSuccessDeclarations.lean` passed; see `product_success_declarations_summary.txt`.
- `lake env lean audit/OriginalFourTaskCompletionDeclarations.lean` passed; see `original_four_task_completion_declarations_summary.txt`.
- `jq empty terminal_outcome/terminal_outcome.json run/goal_identity_20260602_human_centered_positive_witness.json` passed; see `json_valid.log`.
- `python3 audit/original_four_task_contract_audit.py --root . --contract /home/roku/codex-consultant-20260517/outputs/proposed_goals/lean_lca_original_four_task_completion_contract_20260526.md --positive-witness-contract /home/roku/codex-consultant-20260517/outputs/proposed_goals/lean_lca_false_positive_recovery_20260530/lean_lca_positive_witness_completion_contract_20260530.md --terminal-outcome terminal_outcome/terminal_outcome.json` passed; see `original_four_task_contract_audit.json`.
- `scripts/audit_no_forbidden_lean_tokens.sh LeanLCAExactChallenge/Derived/BoundarySourcePiZeroTargetExactAtStableClosureProductRoute.lean LeanLCAExactChallenge.lean` passed; see `forbidden_tokens.log`.
- `git diff --check` passed; see `diff_check.log`.

## Contract Status

`terminal_outcome/terminal_outcome.json` remains nonterminal:

- `product_success = false`
- `product_success_claimed = false`
- `product_complete = false`
- `update_goal_allowed = false`

The contract audit still reports the expected nonterminal blocker:

```text
final product surface still references AcceptedStableBoundedDerivedInfinityCategory
```

W1607 replaces one high-level closed-two input with target ExactAt realization data, but it still depends on branch data and does not construct the nullary original four-task witness. The goal must not be marked complete from this checkpoint.
