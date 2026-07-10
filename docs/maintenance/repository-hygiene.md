# Repository Hygiene

This repository is a Lean/mathlib source workspace, so tracked history should contain source files, concise review documentation, scripts, and CI configuration.

Root run logs, terminal outcomes, progress TSVs, packet manifests, generated C/object files, Lean build products, worker transcripts, and external review packets are transient evidence and must stay outside git history.

Use `/run/`, `/terminal_outcome/`, `/packets/`, root `manifest.json`, `*.log`, `*.exit`, `*.err`, `*.status`, `*.tsv`, `*.olean`, `*.ilean`, `*.c`, and `*.o` as generated paths unless a future repository contract names a narrower tracked fixture path.

The local gate is `scripts/audit_no_generated_files.sh`, and CI runs the same gate before Lean checks so a branch cannot merge while generated artifacts remain tracked.

Do not use root `terminal_outcome/terminal_outcome.json` or `run/verification.json` as completion evidence for this challenge; completion claims must be backed by Lean declarations that compile in `lake build`, and objective 4's status is tracked in `docs/STATUS.md`.

When long-running workers, terminal captures, or packet audits are needed, write them under the active Codex thread workspace or publish them as CI artifacts instead of committing them to this repository.
