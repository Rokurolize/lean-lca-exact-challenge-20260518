# W1138 Provider Search Ledger

Timestamp: 2026-05-29T00:46:31+09:00.

W1138 follows the existing W1129 endpoint-localized-unit to localized-unit-choice bridge pattern, but retargets it to the current W1137 frontier instead of W1128.

Decision: use `localizedUnitChoiceDataOfEndpointLocalizedUnitW1012` to build the W982 localized-unit-choice provider from W1003 endpoint-localized-unit data, then delegate all component-field, current/full-data, target-surjective-compact, left-calculus, and bounded-derived constructions through W1137.

Rejected route: directly opening W1003 endpoint-localized-unit fields into lower primitive fields in this increment would skip the already checked W1012 contraction and mix frontier reduction with a deeper primitive-field search.

Result: W1138 reduces the explicit surface from 6 W1011 localized-unit-choice inputs to 5 W1012 endpoint-localized-unit inputs. Product success remains false.
