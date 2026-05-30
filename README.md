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

## Current Status

The W1426 product-success metadata was reopened as a false positive under the positive-witness recovery contract. Current terminal metadata is `nonterminal_recovery_baseline`: product success is false, the W1425/W1426 `originalFourTaskContractCompletion` surface still proves `productSuccessClaimed = false`, and the repository now requires a positive Lean-native `OriginalFourTaskProductSuccess`-style witness before product success may be claimed.

W1424 adds a checked nonterminal bridge from the W982 localized-unit-choice provider through the existing W1164/W1163 unit-strict-exact route into the closed-map stable package, and wires that bridge into the original-four audit surface without changing the final false product-success flag.

The next implementation work is mathematical, not metadata promotion: build the missing positive Lean surface for the original four tasks, or continue the smallest checked route increment that moves one of those four tasks closer to such a witness.
