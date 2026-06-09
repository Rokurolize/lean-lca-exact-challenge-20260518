# Quillen Map Property Projection Checkpoint

Generated: 2026-06-09T07:28:00Z

Checkpoint name: `quillen-map-property-projections`

Outcome: nonterminal mathematical-frontier checkpoint; `product_success = false`, `product_complete = false`, and `update_goal complete` remains disallowed.

## Source Changes

- `LeanLCAExactChallenge/LCA/ExactCategory.lean`: exposes map-level consequences of canonical exact-category predicates via `MetrizableLCA.closed_inclusion_of_quillenInflation`, `MetrizableLCA.open_map_of_quillenDeflation`, `MetrizableLCA.surjective_of_quillenDeflation`, and `MetrizableLCA.open_surjection_of_quillenDeflation`.
- `audit/RequiredDeclarations.lean`: records the new declaration names in the required public surface.
- `audit/OriginalFourTaskCompletionDeclarations.lean`: records the new declaration names in the original-four-task audit surface.
- `audit/ProductSuccessDeclarations.lean`: records the new declaration names in the product-success audit surface without claiming product success.
- `run/goal_identity_20260602_human_centered_positive_witness.json`: preserves the post-W1618 resumption identity refresh.

## Obligation Status

The checkpoint strengthens the Task 2 exact-category surface by extracting the expected topological map properties directly from the canonical `QuillenExactCategory.inflation` and `QuillenExactCategory.deflation` predicates, rather than only from complete conflations.

The positive-witness obligation remains open. This checkpoint does not add a positive witness, does not claim terminal completion, and does not set any product-success flag to true.

The expected `docs/research/positive_witness_obligation_ledger.md` file was absent during resumption; the current ledger evidence remains the existing current-state reports, W1618 report, resumption gate logs, and this checkpoint report.

## Resumption And Stable Gate Evidence

- Resumption gate logs were generated after W1618: `run/resumption_gate_git_status_20260609_after_w1618.log`, `run/resumption_gate_head_20260609_after_w1618.log`, `run/resumption_gate_origin_main_local_20260609_after_w1618.log`, `run/resumption_gate_origin_main_remote_20260609_after_w1618.log`, `run/resumption_gate_terminal_outcome_20260609_after_w1618.json`, `run/resumption_gate_product_success_true_search_20260609_after_w1618.log`, and `run/resumption_gate_product_success_false_search_20260609_after_w1618.log`.
- Stable migration gate source state was confirmed as Lean `v4.30.0`, mathlib rev `v4.30.0`, and manifest mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
- Stable survey build evidence: `run/stable_v4300_mathlib_survey_build_after_w1618_20260609.log`.

## Verification

Tier B checkpoint verification succeeded with these commands:

- `lake env lean LeanLCAExactChallenge/LCA/ExactCategory.lean > run/verify_exactcategory_after_quillen_map_projections_20260609.log 2>&1`
- `lake build LeanLCAExactChallenge.LCA.ExactCategory > run/verify_exactcategory_build_after_quillen_map_projections_20260609.log 2>&1`
- `lake env lean audit/RequiredDeclarations.lean > run/verify_required_after_quillen_map_projections_20260609.log 2>&1`
- `lake env lean audit/ProductSuccessDeclarations.lean > run/verify_productsuccess_after_quillen_map_projections_20260609.log 2>&1`
- `lake env lean audit/OriginalFourTaskCompletionDeclarations.lean > run/verify_originalfour_after_quillen_map_projections_20260609.log 2>&1`
- `scripts/audit_no_forbidden_lean_tokens.sh LeanLCAExactChallenge/LCA/ExactCategory.lean`
- `scripts/audit_no_forbidden_lean_tokens.sh audit/RequiredDeclarations.lean`
- `scripts/audit_no_forbidden_lean_tokens.sh audit/ProductSuccessDeclarations.lean`
- `scripts/audit_no_forbidden_lean_tokens.sh audit/OriginalFourTaskCompletionDeclarations.lean`
- `git diff --check -- LeanLCAExactChallenge/LCA/ExactCategory.lean audit/RequiredDeclarations.lean audit/ProductSuccessDeclarations.lean audit/OriginalFourTaskCompletionDeclarations.lean run/goal_identity_20260602_human_centered_positive_witness.json`

The `lake build` log reports pre-existing style warnings and ends with `Build completed successfully (1754 jobs).`

Raw audit logs were kept outside the repository because they are multi-megabyte `#check` outputs:

- `/home/roku/codex-thread-workspaces/019ea5a4-a615-78b2-8944-d6f4ed0b24bb/logs/verify_required_after_quillen_map_projections_20260609.log`, size `4142643`, SHA256 `7b77fdd3c4ff124bfca0e1b8c0de3154744d8bde5ac724bd9ee98ebe4fd5cb29`.
- `/home/roku/codex-thread-workspaces/019ea5a4-a615-78b2-8944-d6f4ed0b24bb/logs/verify_productsuccess_after_quillen_map_projections_20260609.log`, size `6964224`, SHA256 `f9ac1a14c9b272f083edc05b16766a01cb63303f5591e81bcbe44b6f2ae9172f`.
- `/home/roku/codex-thread-workspaces/019ea5a4-a615-78b2-8944-d6f4ed0b24bb/logs/verify_originalfour_after_quillen_map_projections_20260609.log`, size `5383341`, SHA256 `58b4260d2a9b9a603d272ad4e2fcd9d2a3c5f203561273ec673c223ebafc72da`.
