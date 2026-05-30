# W1279 provider search ledger

Baseline: W1278 ruled out W998/W997 one-input wrappers and the W990 primitive-unit-components route, which expands to eight inputs.

Decision: W1279 records the remaining W99x base W987-producing routes that had not yet been captured by the recent guards. W996 constructs W987 through a target-surjective-compact full-data surface with 2 inputs. W994 constructs W987 through a target-surjective-compact normalized-source/endpoint surface with 4 inputs. W993 constructs W987 through a target-surjective-compact localized-unit-choice surface with 6 inputs. W991 and W992 construct W987 through kernel/cokernel-top iso component-field surfaces with 13 inputs each.

Checked Lean facts:

- `targetSurjectiveCompactFullDataInputNamesW1279_count`: W996 has 2 inputs.
- `targetSurjectiveCompactNormalizedSourceEndpointInputNamesW1279_count`: W994 has 4 inputs.
- `targetSurjectiveCompactLocalizedUnitChoiceInputNamesW1279_count`: W993 has 6 inputs.
- `kernelCokernelTopIsoComponentFieldsInputNamesW1279_count`: W991 has 13 inputs.
- `targetSurjectiveCompactKernelCokernelTopIsoComponentFieldsInputNamesW1279_count`: W992 has 13 inputs.
- `baseRouteExpansionsDoNotReduceW1279`: all five routes are larger than the current W1270 one-input W987 surface.

Result: selected as a nonterminal provider-search guard. W1279 does not claim product success; the remaining W987 provider is still explicit.
