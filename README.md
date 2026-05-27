# LeanLCAExactChallenge

Prepared Lean/mathlib workspace for the Quillen exact category / metrizable LCA
challenge.

Start from the consultant Goal:

```text
/goal follow the instructions in /home/roku/codex-consultant-20260517/outputs/proposed_goals/lean_lca_exact_category_challenge_goal_20260518.md
```

Baseline checks:

```bash
lake build
scripts/check_mathlib_survey.sh
scripts/audit_no_forbidden_lean_tokens.sh LeanLCAExactChallenge
```

`LeanLCAExactChallenge/MathlibSurvey.lean` records checked mathlib anchors. It
is a starting point, not a solution.

## Current Frontier

W1005 is the latest checked nonterminal increment. It packages W1004's separate W944 target no-univ data and W973 closed-embedding closedness data into the existing W984 target/closed-embedding closedness provider, reducing the explicit frontier from four W1004 items to three provider items: W730 boundary/relation data, W984 target no-univ plus closed-embedding closedness data, and W950 normalized-source/endpoint-localized-unit data. Product success remains false.
