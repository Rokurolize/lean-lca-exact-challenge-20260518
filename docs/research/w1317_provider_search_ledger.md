# W1317 provider search ledger

Baseline: W1316 checked W989 and showed that constructing W987 through W981 and W988 expands the current one-input W1270/W987 obligation to a seven-input route surface.

Decision: W1317 checks W988 directly. W988 constructs W984 target/closed-embedding closedness data, W949 endpoint-localized-unit data, W950 normalized-source/endpoint-localized data, W986 inner full-data data, and finally W987 full data from W982 localized-unit-choice fields.

Rejected alternatives:

| Candidate | Intended effect | Reason rejected |
| --- | --- | --- |
| Treat W988 as a closing route | Discharge W987 directly | Rejected because `localizedUnitChoiceInputNamesW988.length = 6`, so W988 expands the one-input W987 obligation. |
| Route through W989 first | Use the adjacent unit strict-exact/isomorphism constructor | Rejected for this guard because W1316 already proves that path has seven inputs. |
| Reopen W982 fields further | Search below localized-unit-choice data | Deferred because W1300-W1306 and W1312 already record the adjacent target, endpoint, normalized-source, localized-unit, and endpoint strict-exact boundaries. |

Result: selected for W1317. The guard proves the definitional W982-to-W987 packaging steps and records the six-input W988 route surface. Product success remains false because the current W1270/W987 provider obligation is not discharged.
