# W1139 Provider Search Ledger

Timestamp: 2026-05-29T00:56:00+09:00.

W1139 follows the existing W1130 normalized-source/endpoint-localized-unit to endpoint-localized-unit bridge pattern, but retargets it to the current W1138 frontier instead of W1129.

Decision: use `endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013` to build the W1003 endpoint-localized-unit provider from W1004 normalized-source/endpoint-localized-unit data, then delegate all localized-unit-choice, component-field, current/full-data, target-surjective-compact, left-calculus, and bounded-derived constructions through W1138.

Rejected route: directly opening W1004 normalized-source/endpoint-localized-unit fields into lower primitive fields in this increment would skip the already checked W1013 contraction and mix frontier reduction with a deeper primitive-field search.

Result: W1139 reduces the explicit surface from 5 W1012 endpoint-localized-unit inputs to 4 W1013 normalized-source/endpoint-localized-unit inputs. Product success remains false.
