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

W1003 is the latest checked nonterminal increment. It packages W1002's separate endpoint strict short-exact family and W945 localized-unit data into the existing W949 endpoint-localized-unit provider, reducing the explicit frontier from six W982 items to five provider items: W730 boundary/relation data, W944 target no-univ data, W973 closed-embedding closedness data, W949 endpoint-localized-unit data, and W948 normalized-source-triangulation data. Product success remains false.
