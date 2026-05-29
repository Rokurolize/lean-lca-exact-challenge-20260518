# W1324 provider search ledger

Baseline: W1323 checked W997 and showed that its one-input wrapper still contains the unclosed W987 branch full-data provider internally.

Decision: W1324 checks W996, the target-surjective compact full-data route. W996 projects W730 boundary/relation data and W986 target/closedness/normalized-source/endpoint data from W987 full data, combines them with W715 target-surjective compact data, and delegates through W995.

Rejected alternatives:

| Candidate | Intended effect | Reason rejected |
| --- | --- | --- |
| Treat W996 as product completion | Use W715 plus W987 to feed W995 | Rejected because W996 still assumes both W715 and W987; its surface has two inputs. |
| Prefer W997 | Bundle W715 and W987 behind one provider | Already recorded by W1323; W996 exposes the two actual assumptions behind that wrapper. |
| Open W987 through W988-W992 | Replace W987 with lower surfaces | Rejected for this guard because those expansions are already recorded by W1316-W1322. |

Result: selected for W1324. The guard proves W996 projects W715, W730, and W986 from the W715/W987 surface and delegates full data through W995. Product success remains false because the current W1270/W987 provider obligation is not discharged.
