# W1327 provider search ledger

Baseline: W1326 checked W994 and showed that the W730/W715/W973/W950 normalized-source/endpoint route expands the current one-input W1270/W987 obligation to four inputs. The older W1317 guard already recorded the main W988 localized-unit-choice to full-data route.

Decision: W1327 supplements W1317 by checking the remaining W988 field splits. W988 preserves W982 closedness, endpoint strict exactness, normalized-source triangulation, endpoint-localized-unit data, target/closedness data, and normalized-endpoint data while constructing W986 and then W987.

Rejected alternatives:

| Candidate | Intended effect | Reason rejected |
| --- | --- | --- |
| Treat W988 as product completion | Build W987 full data from W982 localized-unit-choice data | Rejected because W988 still exposes W982's six explicit inputs. |
| Reuse W1317 without a new guard | Rely on the earlier W988 summary | Rejected because W1317 did not record the normalized-endpoint and inner-provider field equalities now needed for route accounting. |
| Open W982 internals here | Push below the localized-unit-choice provider | Deferred because this guard records the W988 consumer boundary. |

Result: selected for W1327. The guard proves the W988 field-split equalities into W984, W949, W950, and W986. Product success remains false because the current W1270/W987 provider obligation is not discharged.
