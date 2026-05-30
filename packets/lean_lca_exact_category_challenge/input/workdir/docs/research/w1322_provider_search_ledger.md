# W1322 provider search ledger

Baseline: W1321 checked the W990 primitive unit-components route and showed it expands the current one-input W1270/W987 obligation to eight inputs.

Decision: W1322 checks W998, the branch-full-data route that recovers W715 target surjective-compact data from the existing W987 provider. W998 projects W987 through W977 to W944 target no-univ data, rebuilds compactness, constructs the W997 branch-full-data provider, and delegates through W997.

Rejected alternatives:

| Candidate | Intended effect | Reason rejected |
| --- | --- | --- |
| Treat W998 as product completion | Use W987 to recover W715 and feed the route | Rejected because W998 still assumes the W987 branch-full-data provider; its input surface has one item, the same size as the current W1270 obligation. |
| Open W987 through W988-W992 | Replace the W987 provider with component/localized-unit surfaces | Rejected for this guard because those expansions are already recorded by W1316-W1321. |
| Use W997 directly | Package W715 and W987 behind one provider | Rejected because W998 is strictly more informative: it eliminates the separate W715 sub-assumption while preserving the W987 blocker. |

Result: selected for W1322. The guard proves W998 builds W997's branch provider from W987, keeps the branch full-data field unchanged, and recovers target no-univ data from W987 leaves. Product success remains false because the current W1270/W987 provider obligation is not discharged.
