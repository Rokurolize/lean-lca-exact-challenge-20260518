# Lean LCA Exact Category Challenge Handoff

Workdir: `/home/roku/src/Rokurolize/lean-lca-exact-challenge-20260518`

This project was initialized with:

```bash
lake +leanprover/lean4:v4.30.0-rc2 init LeanLCAExactChallenge math
```

Mathlib cache was downloaded during initialization. The pinned toolchain is
`leanprover/lean4:v4.30.0-rc2`, and `lakefile.toml` depends on mathlib
`v4.30.0-rc2`.

Useful first checks:

```bash
lake build
scripts/check_mathlib_survey.sh
scripts/audit_no_forbidden_lean_tokens.sh LeanLCAExactChallenge
```

The file `LeanLCAExactChallenge/MathlibSurvey.lean` is not a solution. It only
records checked imports and names that are relevant to the challenge:
`TopCat`, `AddCommGrpCat`, `ShortComplex.Exact`, `DerivedCategory`, and
`Abelian.Ext`.

Start the TUI goal with:

```text
/goal follow the instructions in /home/roku/codex-consultant-20260517/outputs/proposed_goals/lean_lca_exact_category_challenge_goal_20260518.md
```
