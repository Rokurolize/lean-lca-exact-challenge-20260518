# LeanLCAExactChallenge

This repository is a Lean/mathlib workspace for the exact-category and bounded-derived challenge around metrizable locally compact abelian groups.

Current status, including the honest per-objective breakdown and the mandatory caveat on
objective 4 (the stable bounded-derived infinity-category), lives in `docs/STATUS.md`.

## What Is In Scope

- A local `QuillenExactCategory` interface and a strict exact-category instance for `MetrizableLCA`.
- Pullback, pushout, cokernel, finite-colimit, and strict short exact sequence support for metrizable LCA groups.
- A local Yoneda Ext construction over the exact-category interface, including Baer-sum and product-facing APIs.
- A bounded cochain-complex localization surface, plus the ordinary triangulated bounded-derived structure and an in-progress stable infinity-category enhancement.

## Current Gap

The remaining product gap is the genuine stable infinity-category enhancement of the bounded
derived category (objective 4). See `docs/STATUS.md` for the detailed breakdown of what is
proved and what remains.

## Useful Checks

```bash
lake build LeanLCAExactChallenge
scripts/audit_no_generated_files.sh
scripts/audit_no_forbidden_lean_tokens.sh LeanLCAExactChallenge
git diff --check
```

Use the Lean sources and the concise research notes under `docs/research/` as the review
surface. Raw run logs, worker transcripts, packet manifests, terminal outcomes, and progress
TSVs belong in a thread workspace or CI artifacts, not in the repository history.

Maintenance policy and cleanup runbooks live under `docs/maintenance/`.
