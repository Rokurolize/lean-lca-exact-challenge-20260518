# Yoneda Baer Sum Subtraction API Checkpoint

Generated UTC: 2026-06-07T18:13:03Z

Base HEAD: b4cdb58d2f30b9cae722a7a10d70019262c8e8de

## Scope

This checkpoint extends the public `YonedaExt.baer_sum` group API with direct subtraction forms. It is intentionally nonterminal: `product_success`, `product_success_claimed`, `product_complete`, and `update_goal_allowed` remain false.

## New Declarations

- `LeanLCAExactChallenge.YonedaExt.baer_sum_neg_right_eq_sub`
- `LeanLCAExactChallenge.YonedaExt.baer_sum_neg_left_eq_sub`
- `LeanLCAExactChallenge.YonedaExt.baer_sum_sub_left`
- `LeanLCAExactChallenge.YonedaExt.baer_sum_sub_right`

These make the basic Baer operation reusable in downstream product and Ext-group obligations without re-expanding `baer_sum` at each call site.

## Verification

- `lake env lean LeanLCAExactChallenge/Ext/Yoneda.lean`
- `lake build LeanLCAExactChallenge.Ext.Yoneda`
- `lake env lean audit/RequiredDeclarations.lean > /tmp/lean-lca-required-declarations-20260608.log`
- `lake env lean audit/OriginalFourTaskCompletionDeclarations.lean > /tmp/lean-lca-original-four-completion-declarations-20260608.log`
- `scripts/audit_no_forbidden_lean_tokens.sh LeanLCAExactChallenge/Ext/Yoneda.lean audit/RequiredDeclarations.lean audit/OriginalFourTaskCompletionDeclarations.lean`
- `git diff --check -- LeanLCAExactChallenge/Ext/Yoneda.lean audit/RequiredDeclarations.lean audit/OriginalFourTaskCompletionDeclarations.lean`

The first audit attempt failed because the audit imports still saw stale `.olean` artifacts after a direct source-file Lean check. `lake build LeanLCAExactChallenge.Ext.Yoneda` regenerated the module artifact, and both audit files then resolved the new names. Observed warnings were pre-existing header/linter warnings and the existing `Yoneda.lean` unnecessary `simpa` warnings at lines 6734 and 6747 after this edit.

## Commit Status

This checkpoint note is part of the source/audit update to be committed and pushed after Tier B verification. The final response and parent progress TSV record the pushed commit hash.

## Remaining Gap

The full original four-task positive witness surface is still absent, and the bounded derived infinity-category obligation remains incomplete. This checkpoint only strengthens the public Yoneda Ext Baer-sum group API with honest Lean declarations.
