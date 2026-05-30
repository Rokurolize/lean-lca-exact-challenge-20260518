# Lean LCA Local Issues

This directory is the local support-issue handoff surface for the Lean LCA exact challenge.

It is operational state, not proof evidence. A support issue, worker result, accepted row, clean build, audit pass, or HTML report is never a substitute for a positive `OriginalFourTaskProductSuccess` Lean witness.

## Ownership

- The implementation role remains the only live proof writer for the target repository.
- The support/governor role owns `Issues/support_issues.tsv`, support worker inboxes, stale-row decisions, and `accepted_for_impl` promotion.
- Support workers must not mutate the live target repository.
- A support result becomes implementation-readable only after the parent/governor verifies the result and promotes a short row or note to `accepted_for_impl`.

## Required Flow

```text
open -> assigned -> result_submitted -> parent_verified -> accepted_for_impl
open -> assigned -> result_submitted -> parent_verified -> rejected
open -> assigned -> result_submitted -> stale_rebase_needed
open -> needs_split -> open
accepted_for_impl -> consumed_by_impl -> closed
```

Before launching any worker, refresh the live `base_head` and `dirty_context`. If the implementation role has advanced the target, mark stale rows `stale_rebase_needed` and rewrite the active rows before launch.

## Current Seed

`support_issues.tsv` is seeded from the consultant proposal at:

```text
/home/roku/codex-consultant-20260517/outputs/proposed_goals/lean_lca_support_issue_system_20260530/support_issues_seed.tsv
```

The first row, `LCA-SUP-001`, is the closeout monitor. It must be parent-verified before any proof-frontier, route-critic, API-scout, or audit worker launches.

Current refreshed baseline:

```text
base_head=f08e8d914b47ade3e95745850251c82ef255796f
dirty_context=clean_w1449_issue_ledger_installed_quiescent_impl_session
```

This `base_head` is the Lean proof/source baseline before the issue-only operational commit that installed this directory. It is not intended to equal the commit hash of the ledger-install commit itself. The latest safety check found the implementation rollout quiescent after W1449 `task_complete`, the target worktree clean, and target `Issues/` absent before installation.

## Result Contract

Every support worker result must include at least:

```json
{
  "schema": "lean_lca_support_issue_result.v1",
  "issue_id": "LCA-SUP-001",
  "base_head": "",
  "dirty_context": "",
  "role": "",
  "status": "accepted_candidate|rejected_candidate|stale|blocked",
  "audited_paths": [],
  "commands_run": [],
  "candidate_next_action": "",
  "lean_command_to_rerun": "",
  "rejected_routes": [],
  "product_success_claimed": false,
  "implementation_note": ""
}
```

`product_success_claimed` must be `false` for ordinary support rows.
