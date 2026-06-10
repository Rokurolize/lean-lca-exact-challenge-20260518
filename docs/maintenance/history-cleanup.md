# History Cleanup Runbook

Current cleanup is clean-forward: remove generated artifacts from the tracked index, add gates that prevent recurrence, and preserve the pre-cleanup tip as a local archive ref.

The pre-cleanup `origin/main` tip audited on 2026-06-10 was `a0776d88e195b0aeb03549753da9a44613c76dca`, and the local preservation ref is `archive/pre-hygiene-a0776d88`.

Shared-history rewriting is a protected operation because it mutates remote state for every clone; do not run it without an explicit approval step that names the remote, target branch, backup ref, and expected post-rewrite commit.

Before any rewrite, fetch the remote, verify that every collaborator-facing branch has either been archived or intentionally excluded, and create a mirror clone outside the working checkout.

Use `git filter-repo` from the mirror clone only, with path rules that remove root `/run/`, root `/terminal_outcome/`, root `/packets/`, root `/manifest.json`, and generated suffixes such as `.log`, `.exit`, `.err`, `.status`, `.tsv`, `.olean`, `.ilean`, `.c`, and `.o`.

After filtering, run `git fsck`, `scripts/audit_no_generated_files.sh`, `lake build`, `scripts/audit_no_forbidden_lean_tokens.sh LeanLCAExactChallenge audit`, the three Lean audit files, `PYTHONDONTWRITEBYTECODE=1 python3 audit/external_audit.py --root .`, and `git diff --check` in a fresh clone of the rewritten branch.

Only after the fresh-clone checks pass should a force push be considered, and the command should use `--force-with-lease` against the reviewed remote ref.

If any check fails after filtering, discard the mirror clone, keep the clean-forward branch, and fix the source-level cause before attempting another rewrite.
