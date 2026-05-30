# W1280 provider search ledger

Baseline: W1279 ruled out the remaining W99x base W987-producing routes W996/W994/W993/W991/W992 as expansions beyond the current one-input W987 surface.

Decision: W1280 records the older W988/W989 and W1000-W1005 W987-producing chain. These routes are checked constructors, but they expose 6, 7, 18, 7, 6, 5, 4, and 3 inputs respectively, so none closes the current W1270 one-input W987 provider.

Checked Lean facts:

- `noUnivLocalizedUnitChoiceInputNamesW1280_count`: W988 has 6 inputs.
- `noUnivUnitStrictExactIsoInputNamesW1280_count`: W989 has 7 inputs.
- `componentFieldsInputNamesW1280_count`: W1000 has 18 inputs.
- `unitStrictExactIsoDataInputNamesW1280_count`: W1001 has 7 inputs.
- `localizedUnitChoiceInputNamesW1280_count`: W1002 has 6 inputs.
- `endpointLocalizedUnitInputNamesW1280_count`: W1003 has 5 inputs.
- `normalizedSourceEndpointLocalizedUnitInputNamesW1280_count`: W1004 has 4 inputs.
- `targetClosedEmbeddingClosednessInputNamesW1280_count`: W1005 has 3 inputs.
- `olderChainExpansionsDoNotReduceW1280`: all eight routes are larger than the current W1270 one-input W987 surface.

Result: selected as a nonterminal provider-search guard. W1280 does not claim product success; the remaining W987 provider is still explicit.
