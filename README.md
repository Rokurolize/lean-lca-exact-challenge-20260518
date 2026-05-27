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

W1047 is the latest checked nonterminal increment. It constructs W1046's W1010 endpoint/unit-strict-exact provider surface from the W1011 localized-unit-choice provider surface, then feeds W1046/W1045/W1044/W1043/W1042/W1041/W1040/W1039/W1038/W1037/W1036/W1035/W1034/W1033/W1032/W1031/W1030/W1029/W1028/W1027/W1026/W1025/W1024/W1023/W1022/W1021/W1020/W1019/W1018/W1017/W1016/W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/W1004/W1003/W1002/W998. The explicit frontier is the 6 W1011 localized-unit-choice inputs. Product success remains false.
