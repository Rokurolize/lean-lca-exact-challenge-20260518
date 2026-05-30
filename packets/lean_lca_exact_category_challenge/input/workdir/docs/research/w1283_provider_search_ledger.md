# W1283 provider search ledger

Baseline: W1282 ruled out the W1025-W1034 numbered direct-route alias layer as a completion path for the current one-input W987 surface.

Decision: W1283 records the repeated W1035-W1052 direct-route alias bands. W1035, W1043, W1044, and W1052 are one-input wrappers around the current branch/current full-data surface, while W1036-W1042 and W1045-W1051 expose 18, 7, 6, 5, 4, 3, and 2 inputs in each band.

Checked Lean facts:

- `currentFullDataRepeatAInputNamesW1283_count`: W1035 has 1 input.
- `branchFullDataRepeatAInputNamesW1283_count`: W1043 has 1 input.
- `currentFullDataRepeatBInputNamesW1283_count`: W1044 has 1 input.
- `branchFullDataRepeatBInputNamesW1283_count`: W1052 has 1 input.
- `componentFieldsRepeatAInputNamesW1283_count` and `componentFieldsRepeatBInputNamesW1283_count`: W1036/W1045 have 18 inputs.
- `unitStrictExactIsoDataRepeatAInputNamesW1283_count` and `unitStrictExactIsoDataRepeatBInputNamesW1283_count`: W1037/W1046 have 7 inputs.
- `localizedUnitChoiceRepeatAInputNamesW1283_count` and `localizedUnitChoiceRepeatBInputNamesW1283_count`: W1038/W1047 have 6 inputs.
- `endpointLocalizedUnitRepeatAInputNamesW1283_count` and `endpointLocalizedUnitRepeatBInputNamesW1283_count`: W1039/W1048 have 5 inputs.
- `normalizedSourceEndpointLocalizedUnitRepeatAInputNamesW1283_count` and `normalizedSourceEndpointLocalizedUnitRepeatBInputNamesW1283_count`: W1040/W1049 have 4 inputs.
- `targetClosedEmbeddingClosednessRepeatAInputNamesW1283_count` and `targetClosedEmbeddingClosednessRepeatBInputNamesW1283_count`: W1041/W1050 have 3 inputs.
- `targetClosedEmbeddingClosednessNormalizedSourceEndpointRepeatAInputNamesW1283_count` and `targetClosedEmbeddingClosednessNormalizedSourceEndpointRepeatBInputNamesW1283_count`: W1042/W1051 have 2 inputs.
- `repeatedDirectRouteWrappersKeepCurrentSurfaceW1283`: the one-input wrappers keep the same input count as W1270.
- `repeatedDirectRouteAliasesDoNotReduceW1283`: the expansion routes are all larger than the current W1270 one-input W987 surface.

Result: selected as a nonterminal provider-search guard. W1283 does not claim product success; the remaining W987 provider is still explicit.
