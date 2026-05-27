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

W1015 is the latest checked nonterminal increment. It constructs W1014's W1005 target/closed-embedding-closedness surface from the W1006 target/closed-embedding-closedness/normalized-source/endpoint-localized surface, then feeds W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/W1004/W1003/W1002/W998. The explicit frontier is the 2 W1006 target/closed-embedding-closedness/normalized-source/endpoint-localized provider inputs. Product success remains false.
