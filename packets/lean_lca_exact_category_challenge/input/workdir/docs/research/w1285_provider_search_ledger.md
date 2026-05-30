# W1285 provider search ledger

Baseline: W1284 ruled out the W1053-W1070 repeated direct-route alias bands.

Decision: W1285 records the next repeated bands W1071-W1088. W1071, W1079, W1080, and W1088 are one-input wrappers around the current branch/current full-data surface, while W1072-W1078 and W1081-W1087 expose 18, 7, 6, 5, 4, 3, and 2 inputs in each band.

Checked Lean facts:

- `repeatedDirectRouteWrappersKeepCurrentSurfaceW1285`: the one-input wrappers keep the same input count as W1270.
- `repeatedDirectRouteAliasesDoNotReduceW1285`: the expansion routes are all larger than the current W1270 one-input W987 surface.
- `currentW1285RepeatedDirectRouteAliasGuard_productSuccess`: W1285 remains nonterminal.

Result: selected as a nonterminal provider-search guard. W1285 does not claim product success; the remaining W987 provider is still explicit.
