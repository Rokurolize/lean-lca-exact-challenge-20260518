# Agent Workflows

## Development loop

1. Edit Lean sources under `LeanLCAExactChallenge/`.
2. Verify:
   - Fast single-file check while iterating: `lake env lean -j1 <touched-file>`.
   - Full check before finishing: `lake build LeanLCAExactChallenge`.
3. Commit with a descriptive message.

There are no per-commit status or report updates. `docs/STATUS.md` is updated at milestones
only, not after every commit.

## Quality gates

Run before pushing:

```bash
scripts/audit_no_forbidden_lean_tokens.sh LeanLCAExactChallenge
scripts/audit_no_generated_files.sh
```

The first rejects `sorry`, `admit`, `axiom`, and unsafe declarations. The second rejects
tracked generated artifacts (run logs, build products, terminal outcomes, etc.).

## Honesty rule

Objective 4 (the stable bounded-derived ∞-category) must not be claimed complete until the
genuine stable quasicategory construction is inhabited and verified — inhabitation of the
∞-localization universal property, comparison with the dg carrier, the stability proof, and
equivalence of the ordinary comparison functor. See `docs/STATUS.md` for the current status
and remaining tasks.

## Lean 4 workflows

Use the installed `lean4` skill for theorem-proving work in this repository.
