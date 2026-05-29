# W1323 provider search ledger

Baseline: W1322 checked W998 and showed that W715 target-surjective compact data can be recovered from W987, but the route still keeps the current one-input W1270/W987 obligation.

Decision: W1323 checks W997, the one-provider wrapper that packages W715 target-surjective compact data and W987 branch full data. This guard records why that one-input surface is not terminal: the wrapper contains the same unconstructed W987 branch full-data provider.

Rejected alternatives:

| Candidate | Intended effect | Reason rejected |
| --- | --- | --- |
| Treat W997 as product completion | Use the one-provider surface as terminal | Rejected because the provider contains W715 and W987 fields; it is a wrapper, not a construction of either field. |
| Prefer W998 over W997 | Recover W715 from W987 | Already recorded by W1322; W1323 captures the adjacent wrapper that W998 feeds. |
| Open W997 to W996 only | Return to the two-input W715/W987 surface | Deferred to a separate guard because W997 itself is the immediate one-input wrapper boundary. |

Result: selected for W1323. The guard proves W997 projects W715 and W987 from the wrapper, builds the W996 surface, and delegates full data through W996. Product success remains false because the current W1270/W987 provider obligation is not discharged.
