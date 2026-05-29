# W1282 provider search ledger

Baseline: W1281 ruled out the unnumbered W1016-W1024 direct-route alias layer as a completion path for the current one-input W987 surface.

Decision: W1282 records the numbered W1025-W1034 direct-route alias layer. W1025, W1026, and W1034 are one-input wrappers around the current branch/current full-data surface, while W1027-W1033 expose 18, 7, 6, 5, 4, 3, and 2 inputs respectively.

Checked Lean facts:

- `branchFullDataNumberedAliasInputNamesW1282_count`: W1025 has 1 input.
- `currentFullDataNumberedAliasInputNamesW1282_count`: W1026 has 1 input.
- `componentFieldsNumberedAliasInputNamesW1282_count`: W1027 has 18 inputs.
- `unitStrictExactIsoDataNumberedAliasInputNamesW1282_count`: W1028 has 7 inputs.
- `localizedUnitChoiceNumberedAliasInputNamesW1282_count`: W1029 has 6 inputs.
- `endpointLocalizedUnitNumberedAliasInputNamesW1282_count`: W1030 has 5 inputs.
- `normalizedSourceEndpointLocalizedUnitNumberedAliasInputNamesW1282_count`: W1031 has 4 inputs.
- `targetClosedEmbeddingClosednessNumberedAliasInputNamesW1282_count`: W1032 has 3 inputs.
- `targetClosedEmbeddingClosednessNormalizedSourceEndpointNumberedAliasInputNamesW1282_count`: W1033 has 2 inputs.
- `branchFullDataReturnAliasInputNamesW1282_count`: W1034 has 1 input.
- `numberedDirectRouteWrappersKeepCurrentSurfaceW1282`: W1025, W1026, and W1034 keep the same one-input surface as W1270.
- `numberedDirectRouteAliasesDoNotReduceW1282`: W1027-W1033 are all larger than the current W1270 one-input W987 surface.

Result: selected as a nonterminal provider-search guard. W1282 does not claim product success; the remaining W987 provider is still explicit.
