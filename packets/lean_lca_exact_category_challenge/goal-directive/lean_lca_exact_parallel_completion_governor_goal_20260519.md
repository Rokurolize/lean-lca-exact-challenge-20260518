# Goal: Parallel Completion Governor For Lean LCA Exact Challenge

Goal contract version: `2026-05-19-lean-lca-exact-parallel-completion-governor-v1`

Target workdir: `/home/roku/src/Rokurolize/lean-lca-exact-challenge-20260518`

Use this goal only after the currently running thread `019e3c1e-ce8e-7190-9df0-18452cc5e187` has either completed, stopped, been intentionally cancelled by the human operator, or reached a repeated plateau on the same product gap. Do not run this concurrently against the same dirty target worktree while that thread is actively editing.

## Objective

Complete the four-part Lean/mathlib formalization challenge for Quillen exact categories, metrizable locally compact abelian groups with strict exact sequences, Yoneda-Ext groups, and bounded derived infinity-category structure. Use parent-supervised parallel workers where they reduce proof-frontier latency, but preserve a strict product-success oracle. The final claim must be machine-checked and must not rely on `sorry`, `admit`, `axiom`, `unsafe`, source-patch assumption wrappers, blocker classes, or placeholder product interfaces.

## Completion Type

Product success only.

The only terminal outcome that may call `update_goal(status="complete")` is:

```text
product_success
```

`product_success` requires `terminal_outcome/terminal_outcome.json.product_complete=true`, empty `known_gaps`, passing verification oracle, passing review packet audit, and fresh claim-review-loop acceptance.

Any non-success state is progress evidence only. It must not call `update_goal(status="complete")`.

## Required First Barrier

Before launching any worker:

1. Inspect current target state read-only.
2. If another Codex process is actively working in `/home/roku/src/Rokurolize/lean-lca-exact-challenge-20260518`, do not launch workers. Create a coordination note and wait or ask the human operator whether to cancel the other run.
3. If the target worktree has uncommitted changes, identify whether they belong to the just-finished active run. Do not overwrite, reset, clean, stash, or duplicate them.
4. Run or inspect a fresh baseline:

```bash
git status --short --branch
git log --oneline -5
lake build
scripts/audit_no_forbidden_lean_tokens.sh LeanLCAExactChallenge
lake env lean audit/RequiredDeclarations.lean
lake env lean audit/ProductSuccessDeclarations.lean
python3 audit/external_audit.py --root "$PWD" --terminal-outcome terminal_outcome/terminal_outcome.json
git diff --check
```

If `lake build` or required Lean checks already fail, fix or isolate the failure before spawning broad parallel work.

## Required Artifacts

Maintain:

```text
GOAL_IDENTITY.json
implementation-notes.html
progress.tsv
proof_frontier/FRONTIER_MATRIX.json
proof_frontier/FRONTIER_MATRIX.md
workers/
reviews/
merge_queue/
run/verification.json
audit/RequiredDeclarations.lean
audit/ProductSuccessDeclarations.lean
audit/external_audit.py
docs/research/sources.md
docs/research/reference_route_log.md
docs/research/mathlib_gap_analysis.md
terminal_outcome/terminal_outcome.json
packets/lean_lca_exact_category_challenge/
packets/lean_lca_exact_category_challenge.zip
packets/lean_lca_exact_category_challenge.zip.sha256
```

The progress TSV header must be:

```text
ts_utc	actor	status	artifact	evidence	next
```

## Implementation Notes Contract

Maintain `implementation-notes.html` in the target workdir. It must record:

- design decisions where the mathematical spec or mathlib API is ambiguous;
- deviations from the source mathematics or prior goal text;
- tradeoffs between a minimal compiling interface and a faithful product formalization;
- open mathematical questions and whether they block product success;
- worker assignments and merge decisions;
- why any candidate worker was rejected or delayed.

Open questions do not block local work unless they affect product-success truth.

## Proof Frontier Matrix

Before launching workers, write `proof_frontier/FRONTIER_MATRIX.json` and `.md`. Each row must include:

- `frontier_id`;
- target declarations;
- target files or proposed new module;
- dependencies;
- allowed writes;
- forbidden writes;
- worker count allowed;
- verification command;
- merge blocker;
- product-success contribution;
- whether another active process already owns it.

Initial frontier candidates from the 2026-05-18 inspection:

1. `frontier-left-yoneda-descent`: left-variable quotient descent and bilinear Yoneda product compatibility. Do not duplicate if the active thread is already working here.
2. `frontier-degree0-hom-tail`: degree 0 and arbitrary hom-tail compatibility for YonedaExt.
3. `frontier-dbounded-infinity`: bounded derived infinity-category enhancement or product-contract tightening that rejects ordinary localization as insufficient.
4. `frontier-audit-hardening`: strengthen `audit/external_audit.py` and `audit/ProductSuccessDeclarations.lean` so product success cannot be claimed by placeholders.
5. `frontier-route-log`: Japanese source-route documentation and packet consistency.

## Worker Launch Contract

The parent owns all fan-out. A worker must not launch `codex`, `codex-patched`, `codex-exec`, subagents, or another worker.

Each worker must have:

- unique worktree or owned directory;
- unique branch name;
- unique `CODEX_PROGRESS_TSV`;
- unique `CODEX_SQLITE_HOME`;
- unique `CODEX_ROLLOUT_DIR`;
- unique `log_dir`;
- stdout and stderr logs;
- `--output-last-message`;
- concise `goal.txt` naming the absolute `instructions.md` path and mandatory absolute `result.json` path;
- detailed `instructions.md`;
- machine-readable `result.json`.

The parent progress TSV must record `child_tsv=<absolute-worker-tsv>` before launch.

Prefer worker-owned new modules imported by the parent over multiple workers editing the same large file. In particular, avoid parallel edits to `LeanLCAExactChallenge/Ext/Yoneda.lean` unless the workers are explicitly partitioned by imported helper modules and the parent owns the final integration.

## Merge Contract

Worker output is not accepted merely because the worker says it compiled. The parent must:

1. inspect the diff;
2. run the worker's focused Lean command;
3. run the relevant audit file;
4. update `FRONTIER_MATRIX`;
5. update `implementation-notes.html`;
6. run a fresh claim-review-loop for any merge that changes product-success semantics;
7. merge or reimplement the change in the parent-owned target.

The parent owns `audit/RequiredDeclarations.lean`, `audit/ProductSuccessDeclarations.lean`, `terminal_outcome/terminal_outcome.json`, packet generation, and final response.

## Verification Oracle

Product success requires all commands to pass from a clean extraction or clean target checkout:

```bash
lake build
scripts/audit_no_forbidden_lean_tokens.sh LeanLCAExactChallenge
lake env lean audit/RequiredDeclarations.lean
lake env lean audit/ProductSuccessDeclarations.lean
python3 audit/external_audit.py --root "$PWD" --terminal-outcome terminal_outcome/terminal_outcome.json
git diff --check
```

`audit/external_audit.py` must fail on:

- missing required files;
- stale verification evidence;
- `sorry`, `admit`, `axiom`, `unsafe`;
- product declarations that depend on assumption wrappers, source-patch classes, blocker classes, frontier classes, or placeholder interfaces;
- ordinary localization being claimed as bounded derived infinity-category without a product-approved interpretation;
- `terminal_outcome.json.outcome` other than `product_success`;
- `product_complete` other than `true`;
- nonempty `known_gaps`;
- packet-internal authoritative final zip SHA256;
- stale or non-success terminal state.

## Review Packet

Create a review packet:

```text
packets/lean_lca_exact_category_challenge.zip
packets/lean_lca_exact_category_challenge.zip.sha256
```

Preferred packet structure:

```text
README_FOR_REVIEW.md
manifest.json
external_audit.py
goal-directive/
initial/
input/
run/
audit/
terminal_outcome/
```

The final zip SHA256 must be authoritative only in the external `.sha256` sidecar or an external build-provenance file. Packet-internal files may contain per-file hashes but must not treat the final zip SHA256 as authoritative.

Required negative fixture:

```text
audit/negative_fixtures/self_referential_zip_sha_authoritative/
```

## Forbidden Operations

- Do not run concurrently against a dirty target worktree owned by another active Codex process.
- Do not launch recursive Codex workers from inside workers.
- Do not push to GitHub.
- Do not change global Lean/elan defaults.
- Do not reset, clean, stash, restore, or overwrite existing work.
- Do not mutate `/home/roku/codex-consultant-20260517` except reading this goal if it remains there.
- Do not claim product success for a bounded handoff.
- Do not hide missing mathematics behind an assumption wrapper or placeholder product interface.
- Do not read browser cookies, auth JSON, private keys, or unrelated secrets.

## Final Response Format

Respond in Japanese:

```text
outcome:
product_complete:
update_goal_called:
workdir:
final_commit:
verified_commands:
packet_zip:
packet_sha256_sidecar:
terminal_outcome_json:
reference_route_log:
worker_frontier_summary:
claim_review_result:
remaining_gaps:
next_recommended_goal:
```

For a completed run, `remaining_gaps` must be `[]` or a Japanese statement that there are no remaining product gaps.

## Startup Command

Use only after the current active target run is no longer editing the same target worktree:

```text
/goal follow the instructions in /home/roku/codex-consultant-20260517/outputs/proposed_goals/lean_lca_exact_parallel_completion_governor_goal_20260519.md
```
