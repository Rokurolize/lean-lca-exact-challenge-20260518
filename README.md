# LeanLCAExactChallenge

This repository is a Lean/mathlib workspace for the exact-category and bounded-derived challenge around metrizable locally compact abelian groups.

The repository is not claiming product success. The current terminal outcome remains nonterminal until Lean contains a genuine positive witness for the original four-task contract, in the shape checked by `audit/ProductSuccessDeclarations.lean` and `audit/OriginalFourTaskCompletionDeclarations.lean`.

## What Is In Scope

- A local `QuillenExactCategory` interface and a strict exact-category instance for `MetrizableLCA`.
- Pullback, pushout, cokernel, finite-colimit, and strict short exact sequence support for metrizable LCA groups.
- A local Yoneda Ext construction over the exact-category interface, including Baer-sum and product-facing APIs.
- A bounded cochain-complex localization surface, plus conditional routes toward ordinary triangulated and stable bounded-derived structures.
- Audit declarations and negative fixtures that prevent metadata-only, ordinary-nerve-only, symbol-only, comment-only, and final-false-witness product-success claims.

## Current Gap

The remaining product gap is the positive Lean construction of the original four-task witness, especially the stable bounded-derived infinity-category part. Existing route modules expose many structural fields and comparison boundaries, but they still carry assumptions rather than a completed `OriginalFourTaskProductSuccess` witness.

Future proof work should replace carried provider assumptions with source-level constructions or a precise missing-theorem handoff. Route ledgers, worker progress files, run logs, review packets, and root manifests are not completion evidence.

## Useful Checks

```bash
lake build
scripts/audit_no_generated_files.sh
scripts/audit_no_forbidden_lean_tokens.sh LeanLCAExactChallenge audit
scripts/build_lean_audit_dependencies.sh
lake env lean audit/RequiredDeclarations.lean
lake env lean audit/ProductSuccessDeclarations.lean
lake env lean audit/OriginalFourTaskCompletionDeclarations.lean
PYTHONDONTWRITEBYTECODE=1 python3 audit/external_audit.py --root .
git diff --check
```

Use the Lean sources, the audit declarations, and the concise research notes under `docs/research/` as the review surface. Raw run logs, worker transcripts, packet manifests, terminal outcomes, and progress TSVs belong in a thread workspace or CI artifacts, not in the repository history.

Maintenance policy and cleanup runbooks live under `docs/maintenance/`.
