# W1284 provider search ledger

Baseline: W1283 ruled out the W1035-W1052 repeated direct-route alias bands.

Decision: W1284 records the next repeated bands W1053-W1070. W1053, W1061, W1062, and W1070 are one-input wrappers around the current branch/current full-data surface, while W1054-W1060 and W1063-W1069 expose 18, 7, 6, 5, 4, 3, and 2 inputs in each band.

Checked Lean facts:

- `repeatedDirectRouteWrappersKeepCurrentSurfaceW1284`: the one-input wrappers keep the same input count as W1270.
- `repeatedDirectRouteAliasesDoNotReduceW1284`: the expansion routes are all larger than the current W1270 one-input W987 surface.
- The individual count theorems record W1053/W1061/W1062/W1070 as 1 input, W1054/W1063 as 18, W1055/W1064 as 7, W1056/W1065 as 6, W1057/W1066 as 5, W1058/W1067 as 4, W1059/W1068 as 3, and W1060/W1069 as 2.

Result: selected as a nonterminal provider-search guard. W1284 does not claim product success; the remaining W987 provider is still explicit.
