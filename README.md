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

W1454 refines the W1453 construction by replacing the bundled W950 normalized-source/endpoint-localized-unit input with the W948 normalized-source-triangulation provider and W949 endpoint-localized-unit provider. It constructs W950 from those two providers, feeds the resulting W1453 input, and proves the constructed W950/W730/W986/W987 projections return to those normalized-endpoint fields, target fields, relation fields, and boundary fields. Product success remains false because these eight inputs are still assumed data, not a positive `OriginalFourTaskProductSuccess` witness.

W1455 refines the W1454 construction by replacing the bundled W949 endpoint-localized-unit input with endpoint strict-exact witnesses and the W945 localized-unit provider. It constructs W949 from those two fields, feeds the resulting W1454 input, and proves the constructed W949/W950/W730/W986/W987 projections return to those endpoint fields, normalized-source field, target fields, relation fields, and boundary fields. Product success remains false because these nine inputs are still assumed data, not a positive `OriginalFourTaskProductSuccess` witness.

W1456 refines the W1455 construction by replacing the bundled W948 normalized-source-triangulation input with the W719 normalized fixed-target provider and W722 source-triangulation provider. It constructs W948 from those two fields, feeds the resulting W1455 input, and proves the constructed W948/W949/W950/W730/W986/W987 projections return to those normalized-source fields, endpoint fields, target fields, relation fields, and boundary fields. Product success remains false because these ten inputs are still assumed data, not a positive `OriginalFourTaskProductSuccess` witness.

W1457 refines the W1456 construction by replacing the bundled W719 normalized fixed-target input with a normalized lift blueprint, target fixed-target uniqueness, and localization-model fixed-target uniqueness. It constructs W719 from those three fields, feeds the resulting W1456 input, and proves the constructed W719/W948/W950/W730/W986/W987 projections return to those fixed-target fields, source field, endpoint fields, target fields, relation fields, and boundary fields. Product success remains false because these twelve inputs are still assumed data, not a positive `OriginalFourTaskProductSuccess` witness.

W1458 refines the W1457 construction by replacing the bundled W722 source-triangulation input with a source pretriangulated structure, source triangulated structure, and source triangle-completion input. It constructs W722 from those three fields, feeds the resulting W1457 input, and proves the constructed W722/W948/W950/W730/W986/W987 projections return to those source-triangulation fields, fixed-target fields, endpoint fields, target fields, relation fields, and boundary fields. Product success remains false because these fourteen inputs are still assumed data, not a positive `OriginalFourTaskProductSuccess` witness.

W1459 refines the W1458 construction by replacing the bundled W945 localized-unit input with a bounded homotopy localized right adjoint, localized adjunction, and W939 unit-component witness. It constructs W945 from those three fields, feeds the resulting W1458 input, and proves the constructed W945/W949/W950/W730/W986/W987 projections return to those localized-unit fields, endpoint fields, source-triangulation fields, fixed-target fields, target fields, relation fields, and boundary fields. Product success remains false because these sixteen inputs are still assumed data, not a positive `OriginalFourTaskProductSuccess` witness.

W1460 refines the W1459 construction by replacing the bundled W939 unit-component witness with a unit mapping-cone model, unit mapping-cone strict short-exact family, and chosen mapping-cone isomorphism. It constructs W981-style unit strict-exact/isomorphism data and the W939 witness from those three fields, feeds the resulting W1459 input, and proves the constructed W945/W949/W730/W986/W987 projections return to the localized-unit, boundary, and target/endpoint data. Product success remains false because these eighteen inputs are still assumed data, not a positive `OriginalFourTaskProductSuccess` witness.

W1461 refines the W1460 construction by replacing the bundled localized adjunction with the unit natural transformation, counit natural transformation, left triangle identity, and right triangle identity used by `Adjunction.mkOfUnitCounit`. It constructs the localized adjunction from those core fields, feeds the resulting W1460 input, and proves the constructed localized-unit/W730/W986/W987 projections return to the core-built adjunction, unit mapping-cone data, boundary data, and target/endpoint data. Product success remains false because these twenty-one inputs are still assumed data, not a positive `OriginalFourTaskProductSuccess` witness.

W1462 refines the W1461 construction by replacing the unit mapping-cone strict short-exact family with closed-embedding, open-map, cokernel-top, and kernel-equality families. It constructs the strict short-exact family with `MetrizableLCA.strictShortExact_of_kernel_open_closed_cokernelSubgroup_eq_top`, feeds the resulting W1461 input, and proves the constructed localized-unit/W730/W986/W987 projections return to the strict-exact construction, unit mapping-cone data, boundary data, and target/endpoint data. Product success remains false because these twenty-four inputs are still assumed data, not a positive `OriginalFourTaskProductSuccess` witness.

W1463 refines the W1462 construction by replacing the endpoint strict short-exact family with closed-embedding, open-map, cokernel-top, and kernel-equality families. It constructs the endpoint strict-exact family with `MetrizableLCA.strictShortExact_of_kernel_open_closed_cokernelSubgroup_eq_top`, feeds the resulting W1462 input, and proves the constructed W987 projection returns to the endpoint strict-exact construction while keeping the unit mapping-cone and localized-unit data. Product success remains false because these twenty-seven inputs are still assumed data, not a positive `OriginalFourTaskProductSuccess` witness.

W1464 refines the W1463 construction by replacing the chosen unit mapping-cone isomorphism with explicit hom, inv, hom-inv, and inv-hom fields. It constructs the `Iso` from those four fields, feeds the resulting W1463 input, and proves the constructed W987 projection keeps the unit mapping-cone model, localized-unit data, boundary data, and target/endpoint data. Product success remains false because these thirty inputs are still assumed data, not a positive `OriginalFourTaskProductSuccess` witness.

W1465 refines the W1464 construction by replacing the localized-adjunction unit and counit natural transformations with component maps and naturality proofs. It constructs those two natural transformations, feeds the resulting W1464 input, and proves the constructed W987 projection keeps the localized right adjoint, unit mapping-cone model, boundary data, and target/endpoint data. Product success remains false because these thirty-two inputs are still assumed data, not a positive `OriginalFourTaskProductSuccess` witness.

W1466 refines the W1465 construction by replacing the localized-adjunction left and right triangle natural-transformation identities with objectwise component identity families. It reconstructs both triangle identities from those component identities, feeds the resulting W1465 input, and proves the constructed W987 projection keeps the localized right adjoint, unit mapping-cone model, boundary data, and target/endpoint data. Product success remains false because these thirty-two inputs are still assumed data, not a positive `OriginalFourTaskProductSuccess` witness.

W1467 refines the W1466 construction by replacing the localized right-adjoint functor input with explicit object map, morphism map, identity law, and composition law fields. It reconstructs the functor from those fields, feeds the resulting W1466 input, and proves the constructed W987 projection keeps the reconstructed right adjoint, unit mapping-cone model, boundary data, and target/endpoint data. Product success remains false because these thirty-five inputs are still assumed data, not a positive `OriginalFourTaskProductSuccess` witness.

W1468 refines the W1467 construction by replacing the W944 target no-univ provider with target-difference surjectivity and target-codomain compact no-univ membership primitive families. It reconstructs W944 from those two primitive families, feeds the resulting W1467 input, and proves the constructed W944 provider, localized-unit data, and W987 projections keep the primitive target fields, reconstructed right adjoint, boundary data, and target/endpoint data. Product success remains false because these thirty-six inputs are still assumed data, not a positive `OriginalFourTaskProductSuccess` witness.

W1469 refines the W1468 construction by replacing the W973 closed-embedding closedness provider with the W718 selected-difference closed-embedding diagram component provider and W519 mapped explicit cokernel closed-embedding provider. It reconstructs W973 from those two fields, feeds the resulting W1468 input, and proves the constructed W973 provider, localized-unit data, and W987 projections keep the closedness fields, primitive target fields, reconstructed right adjoint, boundary data, and target/endpoint data. Product success remains false because these thirty-seven inputs are still assumed data, not a positive `OriginalFourTaskProductSuccess` witness.

W1470 refines the W1469 construction by replacing the W718 selected-difference closed-embedding diagram component provider with its three W714 selected-difference closed-embedding diagram fields. It reconstructs W718 from those three fields, feeds the resulting W1469 input, and proves the constructed W718/W973 providers, localized-unit data, and W987 projections keep the component fields, W519 mapped-cokernel data, primitive target fields, reconstructed right adjoint, boundary data, and target/endpoint data. Product success remains false because these thirty-nine inputs are still assumed data, not a positive `OriginalFourTaskProductSuccess` witness.

W1471 refines the W1470 construction by replacing the W519 mapped explicit cokernel closed-embedding provider with its raw closed-embedding field. It reconstructs W519 from that field, feeds the resulting W1470 input, and proves the constructed W519/W973 providers, localized-unit data, and W987 projections keep the raw mapped-cokernel closed-embedding field, W714 component fields, primitive target fields, reconstructed right adjoint, boundary data, and target/endpoint data. Product success remains false because these thirty-nine inputs are still assumed data, not a positive `OriginalFourTaskProductSuccess` witness.

W1472 refines the W1471 construction by replacing the normalized strict-representative lift blueprint with its raw lift blueprint, object-image normalization field, and map-image normalization field. It reconstructs the normalized lift blueprint from those three fields, feeds the resulting W1471 input, and proves the reconstructed normalized lift blueprint and W987 projections keep the raw lift data, W714 component fields, mapped-cokernel closed-embedding field, primitive target fields, reconstructed right adjoint, boundary data, and target/endpoint data. Product success remains false because these forty-one inputs are still assumed data, not a positive `OriginalFourTaskProductSuccess` witness.

W1473 refines the W1472 construction by replacing the raw strict-representative lift blueprint with its object strict-preimage data family, map strict-preimage data family, map identity law, and map composition law. It reconstructs the raw lift blueprint from those four fields, feeds the resulting W1472 input, and lets W1472 reconstruct the normalized lift blueprint while preserving the W987 projections. Product success remains false because these forty-four inputs are still assumed data, not a positive `OriginalFourTaskProductSuccess` witness.

W1474 refines the W1473 construction by replacing the object strict-preimage data family with eight object-level fields: zero and one source objects, zero and one comparison isomorphisms, left and right source maps, and left and right factorization laws. It reconstructs the object strict-preimage data family, feeds the resulting W1473 input, and preserves the W987 projections through the W1473 route. Product success remains false because these fifty-one inputs are still assumed data, not a positive `OriginalFourTaskProductSuccess` witness.

W1475 refines the W1474 construction by replacing the map strict-preimage data family with six map-level fields: zero and one source-map families, zero and one localization factorization laws, and left and right naturality laws. It reconstructs the map strict-preimage data family, feeds the resulting W1474 input, and preserves the W987 projections through the W1474 route. Product success remains false because these fifty-six inputs are still assumed data, not a positive `OriginalFourTaskProductSuccess` witness.

W1476 refines the W1475 construction by replacing the raw lift map identity and composition laws with four componentwise functoriality laws: zero and one source-map identity laws, and zero and one source-map composition laws. It reconstructs the raw lift map identity and composition laws, feeds the resulting W1475 input, and preserves the W987 projections through the W1475 route. Product success remains false because these fifty-eight inputs are still assumed data, not a positive `OriginalFourTaskProductSuccess` witness.

W1477 refines the W1476 construction by replacing the normalized lift map-image normalization law with two componentwise map-image laws: zero and one component map-image normalization. It reconstructs the bundled map-image law, feeds the resulting W1476 input, and preserves the W987 projections through the W1476 route. Product success remains false because these fifty-nine inputs are still assumed data, not a positive `OriginalFourTaskProductSuccess` witness.

W1478 refines the W1477 construction by replacing the normalized lift object-image normalization law with four componentwise image laws: zero and one object-image equalities, and left and right arrow-image equalities. It reconstructs the bundled object-image law, feeds the resulting W1477 input, and preserves the W987 projections through the W1477 route. Product success remains false because these sixty-two inputs are still assumed data, not a positive `OriginalFourTaskProductSuccess` witness.

The next implementation work is mathematical, not metadata promotion: build the missing positive Lean surface for the original four tasks, or continue the smallest checked route increment that moves one of those four tasks closer to such a witness.
