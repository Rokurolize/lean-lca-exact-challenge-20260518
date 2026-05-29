# W1326 provider search ledger

Baseline: W1325 checked W995 and showed that the W730/W715/W986 target-provider route expands the current one-input W1270/W987 obligation to three inputs.

Decision: W1326 checks W994, the target-surjective compact normalized-source/endpoint route. W994 projects W950 to W949 endpoint-localized-unit data, extracts endpoint strict exactness and localized-unit data, keeps W950's normalized-source triangulation data, and delegates through W993.

Rejected alternatives:

| Candidate | Intended effect | Reason rejected |
| --- | --- | --- |
| Treat W994 as product completion | Feed W993 from W730, W715, W973, and W950 | Rejected because W994 still exposes four explicit assumptions. |
| Use W995 instead | Bundle W973 and W950 behind W986 | Already recorded by W1325; W1326 records the direct W994 surface behind that bundling. |
| Open W950 internals here | Push below the normalized-source/endpoint-localized provider | Deferred because this guard records the W994 consumer boundary. |

Result: selected for W1326. The guard proves W994 obtains endpoint strict exactness, localized-unit data, and normalized-source triangulation from W950 and routes full data through W993. Product success remains false because the current W1270/W987 provider obligation is not discharged.
