# W1325 provider search ledger

Baseline: W1324 checked W996 and showed that the W715/W987 route expands the current one-input W1270/W987 obligation to two inputs.

Decision: W1325 checks W995, the target-surjective compact target-provider route. W995 projects W986 to W984/W973 target closed-embedding closedness data and to W950 normalized-source/endpoint-localized data, then delegates through W994.

Rejected alternatives:

| Candidate | Intended effect | Reason rejected |
| --- | --- | --- |
| Treat W995 as product completion | Feed W994 from W730, W715, and W986 | Rejected because W995 still exposes three explicit assumptions. |
| Use W996 instead | Bundle W730 and W986 into W987 | Already recorded by W1324; W1325 records the direct W995 surface behind that bundling. |
| Open W986 internals here | Push below the target/closedness/normalized-source/endpoint provider | Deferred because this guard records the W995 consumer boundary. |

Result: selected for W1325. The guard proves W995 obtains W973 and W950 from W986 and routes full data through W994. Product success remains false because the current W1270/W987 provider obligation is not discharged.
