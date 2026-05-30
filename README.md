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

W1439 connects the W986 component from W1438 to W1299: W986 repacks judgmentally, feeds W985 with W730 plus its W984 target/closedness and W950 normalized-source/endpoint projections, and exposes the three-input W730/W984/W950 surface. Product success remains false.

W1440 connects the W984 target/closedness component from W1439 to W1300: W984 repacks judgmentally, feeds the W984 full-data route with W944 target no-univ data and W973 closed-embedding closedness data, and exposes the four-input W730/W944/W973/W950 surface. Product success remains false.

W1441 connects the W950 normalized-source/endpoint component from W1440 to W1302: W950 repacks judgmentally, feeds W985 with W948 normalized-source-triangulation data and W949 endpoint-localized-unit data, and exposes the five-input W730/W944/W973/W948/W949 surface. Product success remains false.

W1442 connects the W948 normalized-source-triangulation component from W1441 to W1303: W948 repacks judgmentally, exposes W719 normalized fixed-target data and W722 source-triangulation data, and exposes the six-input W730/W944/W973/W719/W722/W949 surface. Product success remains false.

W1443 connects the W949 endpoint-localized-unit component from W1442 to W1301: W949 repacks judgmentally, exposes endpoint strict-exact witnesses and W945 localized-unit data, and exposes the seven-input W730/W944/W973/W719/W722/endpoint/W945 surface. Product success remains false.

W1444 connects the W945 localized-unit component from W1443 to W1306: W945 repacks judgmentally, exposes the localized right adjoint, localized adjunction, and W939 unit-component witness, and exposes the nine-input W730/W944/W973/W719/W722/endpoint/right-adjoint/adjunction/W939 surface. Product success remains false.

W1445 aligns the W1444 unpacked surface with the W990 primitive unit-components route: W1007's W730/W944/W973/endpoint/right-adjoint/adjunction/W939 data plus the W1303 W948 repack form the W990 provider, W990 preserves the localized adjunction fields, and the route delegates through W989. This is checked route alignment, not a positive product witness.

W1446 records the next W990 packaging step: the W1445 W990 provider forms W981 unit strict-exact/isomorphism full data, chooses the W939 unit mapping-cone model, and lets W989 rebuild localized-unit data while preserving the localized right adjoint and adjunction. Product success remains false.

W1447 records the W989-to-W988 packaging step: the W1446 W981 package forms W982 localized-unit-choice data, keeps boundary/relation, localized-unit, and W948 data, and lets W988 rebuild W987 full data while preserving the W984 target/closedness and W950 normalized-endpoint components. Product success remains false.

W1448 rewraps the W1447-built W987 full data as a W1007 branch-full-data provider: W1007 projections recover the W730 boundary/relation data and W986 target/normalized-endpoint data built by W988, and W1438's W987 repack remains identity on the rewrapped provider. This records a nonterminal route cycle, not product success.

W1449 exposes the W1448 rewrapped provider through W1007's stable-route outputs: the rewrapped provider supplies component fields, endpoint strict exactness, unit mapping-cone exactness and isomorphism data, the direct bounded left-calculus proof, and the bounded-derived infinity-category object while preserving the one-input W987 surface. Product success remains false.

W1450 replaces that one W987 provider argument with a direct field-data construction surface: W716 boundary data and W717 relation data build W730, W984 target/closedness data and W950 normalized-source/endpoint data build W986, and those two constructed providers assemble W987 with projection theorems back to the four named inputs. Product success remains false because these four inputs are still assumed data, not a positive `OriginalFourTaskProductSuccess` witness.

W1451 refines the W1450 construction by replacing the bundled W716 boundary-data input with the two raw boundary fields used by W907. It constructs W716 from the right-open boundary field and source-pi-zero boundary field, feeds the resulting W1450 input, and proves the constructed W716/W730/W987 projections return to those fields and the carried W717/W984/W950 data. Product success remains false because W717/W984/W950 and the two raw boundary fields are still assumed data, not a positive `OriginalFourTaskProductSuccess` witness.

W1452 refines the W1451 construction by replacing the bundled W717 relation-data input with the two raw relation fields used by W908. It constructs W717 from the relation-pullback provider and target-relation-lifts provider, feeds the resulting W1451 input, and proves the constructed W717/W730/W987 projections return to those relation fields, the raw boundary fields, and the carried W984/W950 data. Product success remains false because these six inputs are still assumed data, not a positive `OriginalFourTaskProductSuccess` witness.

W1453 refines the W1452 construction by replacing the bundled W984 target/closedness input with the W944 target no-univ provider and W973 closed-embedding closedness provider. It constructs W984 from those two providers, feeds the resulting W1452 input, and proves the constructed W984/W730/W986/W987 projections return to those target fields, relation fields, boundary fields, and the carried W950 data. Product success remains false because these seven inputs are still assumed data, not a positive `OriginalFourTaskProductSuccess` witness.

The next implementation work is mathematical, not metadata promotion: build the missing positive Lean surface for the original four tasks, or continue the smallest checked route increment that moves one of those four tasks closer to such a witness.
