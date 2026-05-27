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

W1006 is the latest checked nonterminal increment. It packages W1005's separate W984 target no-univ plus closed-embedding closedness data and W950 normalized-source/endpoint-localized-unit data into the existing W986 target/closedness/normalized-source/endpoint-localized provider, reducing the explicit frontier from three W1005 items to two provider items: W730 boundary/relation data and W986 target/closed-embedding-closedness/normalized-source/endpoint-localized data. Product success remains false.
