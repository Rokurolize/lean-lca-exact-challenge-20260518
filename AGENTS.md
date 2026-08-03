## Lean 4 workflows

For Lean 4 proving workflows, use the `lean4` skill ($lean4).

## Objective 4 shorthand

When the user says only `目的4を完了してください`, this repository and Objective 4 are already identified. Read `docs/OBJECTIVE4_EVERGREEN.md`, inspect the current source and Git state, and resume end-to-end implementation without asking the user to repeat the repository or objective.

`docs/OBJECTIVE4_EVERGREEN.md` is the progress-independent contract. `docs/STATUS.md`, the source tree, compiler output, and `git log` determine current progress. Do not copy transient blocker details into the evergreen contract.
