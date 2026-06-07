# Checkpoint: Yoneda Ext Baer-Sum Group API

Generated UTC: 2026-06-07T13:52:49Z

Base HEAD: 6aec74bf713d8d79169460860a573c3b81999717

Product success: false

## Change

This checkpoint exposes the public group-law API for `YonedaExt.baer_sum`, making explicit that Baer addition is the local Ext additive group operation.

New declarations:

- `LeanLCAExactChallenge.YonedaExt.baer_sum_eq_add`
- `LeanLCAExactChallenge.YonedaExt.baer_sum_zero_left`
- `LeanLCAExactChallenge.YonedaExt.baer_sum_zero_right`
- `LeanLCAExactChallenge.YonedaExt.baer_sum_comm`
- `LeanLCAExactChallenge.YonedaExt.baer_sum_assoc`
- `LeanLCAExactChallenge.YonedaExt.baer_sum_neg_left`
- `LeanLCAExactChallenge.YonedaExt.baer_sum_neg_right`

The declarations are now checked by both `audit/RequiredDeclarations.lean` and `audit/OriginalFourTaskCompletionDeclarations.lean`.

## Verification

Commands run for this checkpoint:

```bash
lake env lean LeanLCAExactChallenge/Ext/Yoneda.lean
lake build LeanLCAExactChallenge.Ext.Yoneda
lake env lean audit/RequiredDeclarations.lean
lake env lean audit/OriginalFourTaskCompletionDeclarations.lean
```

The first full audit attempt failed because the audits were reading the previous built `.olean`; rebuilding `LeanLCAExactChallenge.Ext.Yoneda` fixed the unknown-constant errors, and both audits then passed.

Remaining verification before commit:

```bash
scripts/audit_no_forbidden_lean_tokens.sh LeanLCAExactChallenge/Ext/Yoneda.lean audit/RequiredDeclarations.lean audit/OriginalFourTaskCompletionDeclarations.lean
jq empty run/goal_identity_20260602_human_centered_positive_witness.json terminal_outcome/terminal_outcome.json
git diff --check -- LeanLCAExactChallenge/Ext/Yoneda.lean audit/RequiredDeclarations.lean audit/OriginalFourTaskCompletionDeclarations.lean terminal_outcome/terminal_outcome.json run/goal_identity_20260602_human_centered_positive_witness.json run/resumption_gate_20260607_yoneda_ext_baer_sum_group_api run/w_clean_20260607_yoneda_ext_baer_sum_group_api/checkpoint.md
```

## Status

This is a nonterminal checkpoint. It strengthens the Yoneda Ext group API but does not satisfy the final original four-task product witness. The goal remains active, and `update_goal` remains disallowed.
