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

W1009 is the latest checked nonterminal increment. It constructs W1008's W977 current full-data provider from the W971 component-field surface through W978, then feeds W1008/W1007/W1006/W1005/W1004/W1003/W1002/W998. The explicit frontier is the 18 W971 component fields. Product success remains false.
