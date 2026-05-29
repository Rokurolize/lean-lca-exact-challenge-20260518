# W1281 provider search ledger

Baseline: W1280 ruled out W988/W989 and W1000-W1005 as W987-producing completion routes because they expand beyond the current one-input W987 surface.

Decision: W1281 records the unnumbered W1016-W1024 direct-route alias layer. W1016 and W1017 remain one-input wrappers around the current branch/current full-data surface, while W1018-W1024 expose 18, 7, 6, 5, 4, 3, and 2 inputs respectively.

Checked Lean facts:

- `branchFullDataAliasInputNamesW1281_count`: W1016 has 1 input.
- `currentFullDataAliasInputNamesW1281_count`: W1017 has 1 input.
- `componentFieldsAliasInputNamesW1281_count`: W1018 has 18 inputs.
- `unitStrictExactIsoDataAliasInputNamesW1281_count`: W1019 has 7 inputs.
- `localizedUnitChoiceAliasInputNamesW1281_count`: W1020 has 6 inputs.
- `endpointLocalizedUnitAliasInputNamesW1281_count`: W1021 has 5 inputs.
- `normalizedSourceEndpointLocalizedUnitAliasInputNamesW1281_count`: W1022 has 4 inputs.
- `targetClosedEmbeddingClosednessAliasInputNamesW1281_count`: W1023 has 3 inputs.
- `targetClosedEmbeddingClosednessNormalizedSourceEndpointAliasInputNamesW1281_count`: W1024 has 2 inputs.
- `directRouteWrappersKeepCurrentSurfaceW1281`: W1016 and W1017 keep the same one-input surface as W1270.
- `directRouteAliasesDoNotReduceW1281`: W1018-W1024 are all larger than the current W1270 one-input W987 surface.

Result: selected as a nonterminal provider-search guard. W1281 does not claim product success; the remaining W987 provider is still explicit.
