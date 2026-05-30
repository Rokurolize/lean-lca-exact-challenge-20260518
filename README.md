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

W1425 extends that checked W982 surface to the component-field, current-full-data, branch-full-data, and target surjective-compact projections exposed by W1164/W1163. This is still route evidence only; no positive product-success witness is claimed.

W1430 records the nested W982 target/closedness/normalized-source/endpoint and rebuilt W982/W981/W971 projections exposed by W1164/W1163. It deliberately skips the historical W1426 number because W1426 was the reopened false-positive product-success promotion.

W1431 extends the same route to deeper rebuilt current-full-data, branch-full-data, target, endpoint, localized-choice, unit-strict-exact, and component-field projections through W1164/W1163. This continues the checked route surface without changing the nonterminal product status.

W1432 moves the checked bridge one step upstream: W1003 endpoint-localized-unit data constructs the W982 localized-choice surface through W1165, then delegates direct calculus and the stable package through W1164. The route now records five remaining endpoint-localized-unit inputs, but it is still not a positive product witness.

W1433 moves the checked bridge another step upstream: W1004 normalized-source/endpoint-localized-unit data constructs W1003 through W1166, then delegates direct calculus and the stable package through W1165. The route now records four remaining normalized-source/endpoint-localized-unit inputs, while product success remains false.

W1434 moves the checked bridge another step upstream: W1005 target/closed-embedding-closedness data constructs W1004 through W1167, then delegates direct calculus and the stable package through W1166. The route now records three remaining target/closed-embedding-closedness inputs, while product success remains false.

W1435 moves the checked bridge another step upstream: W1006 target/closedness/normalized-source/endpoint data constructs W1005 through W1168, then delegates direct calculus and the stable package through W1167. The route now records two remaining target/closedness/normalized-source/endpoint inputs, while product success remains false.

W1436 moves the checked bridge another step upstream: W1007 branch-full-data constructs W1006 through W1169, then delegates direct calculus and the stable package through W1168. The route now records one remaining branch-full-data input, while product success remains false.

W1437 pins that last branch-full-data input to the W987 surface: W1169's one-input surface is the W1007 surface, W1007's wrapped input is the W987 branch-specific full-data provider, and its count matches the W1270/W1271 current-full-data cycle. This is nonterminal boundary evidence, not a positive completion witness.

W1438 connects that W1007/W987 input to the canonical W1298 unpack: the wrapped W987 provider projects to W730 boundary/relation data and W986 target/closedness/normalized-source/endpoint data, and unpacking the one-input package exposes a two-input W730/W986 surface. Product success remains false.

The next implementation work is mathematical, not metadata promotion: build the missing positive Lean surface for the original four tasks, or continue the smallest checked route increment that moves one of those four tasks closer to such a witness.
