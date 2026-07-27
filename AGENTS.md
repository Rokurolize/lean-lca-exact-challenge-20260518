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

## Objective 4 shorthand

When the user says only `目的4を完了してください`, this repository and Objective 4 are already identified. Read `docs/OBJECTIVE4_EVERGREEN.md`, inspect the current source and Git state, and resume end-to-end implementation without asking the user to repeat the repository or objective.

`docs/OBJECTIVE4_EVERGREEN.md` is the progress-independent contract. `docs/STATUS.md`, the source tree, compiler output, and `git log` determine current progress. Do not copy transient blocker details into the evergreen contract.

## Honesty rule

Objective 4 (the stable bounded-derived ∞-category) must not be claimed complete until the genuine stable quasicategory construction is inhabited and verified: inhabitation of the ∞-localization universal property, comparison with the dg carrier, the stability proof, and equivalence of the ordinary comparison functor. See `docs/OBJECTIVE4_EVERGREEN.md` for the permanent completion contract and `docs/STATUS.md` for current status.

## Lean 4 workflows

Use the installed `lean4` skill for theorem-proving work in this repository.
