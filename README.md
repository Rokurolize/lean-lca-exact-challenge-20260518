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

W1256 is the latest checked nonterminal increment. It constructs W1255's W1012/W1003 endpoint-localized-unit provider surface from the W1013/W1004 normalized-source/endpoint-localized-unit route, then delegates through W1255 and the previously checked route chain. The explicit input surface is the 4 W1013/W1004 normalized-source/endpoint-localized-unit provider inputs. Product success remains false.
