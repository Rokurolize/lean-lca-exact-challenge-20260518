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

W1253 is the latest checked nonterminal increment. It constructs W1252's W1018/W971 component-field provider surface from the W1010/W981 unit-strict-exact-iso route, then delegates through W1252 and the previously checked route chain. The explicit input surface is the 7 W1010/W981 unit-strict-exact-iso provider inputs. Product success remains false.
