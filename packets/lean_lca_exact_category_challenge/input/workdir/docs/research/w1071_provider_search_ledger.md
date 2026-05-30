# W1071 Provider Search Ledger

## Scope

W1071 targets W1070's W1016 branch-full-data input surface. The existing W1017 current-full-data route already constructs the W1007 branch-full-data provider accepted by W1070 via `branchFullDataProviderOfCurrentFullDataW1017`, so W1071 repackages one W1008 current-full-data provider and feeds W1070.

## Candidate Providers

- `branchFullDataInputNamesW1070`: rejected as the latest input ledger because it still exposes one W1016 branch-full-data input.
- `branchFullDataProviderOfCurrentFullDataW1017`: chosen because W1017 already constructs the W1007 provider consumed by W1070.
- `currentFullDataInputNamesW1017`: accepted as the next input ledger because it records the one W1017 current-full-data provider input that remains explicit after W1017.

## Remaining W1071 Inputs

- 1 W1017 current-full-data provider input

The count is checked by `currentFullDataInputNamesW1071_count`.

## Checked W1071 Surface

- `branchFullDataProviderOfCurrentFullDataW1071`
- `targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1071`
- `targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1071`
- `normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1071`
- `endpointLocalizedUnitDataProviderOfCurrentFullDataW1071`
- `localizedUnitChoiceDataOfCurrentFullDataW1071`
- `unitStrictExactIsoDataOfCurrentFullDataW1071`
- `componentFieldsOfCurrentFullDataW1071`
- `currentFullDataProviderOfCurrentFullDataW1071`
- `branchFullDataProviderOfBranchFullDataOfCurrentFullDataW1071`
- `targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfCurrentFullDataW1071`
- `targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfCurrentFullDataW1071`
- `normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfCurrentFullDataW1071`
- `endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfCurrentFullDataW1071`
- `localizedUnitChoiceDataOfLocalizedUnitChoiceOfCurrentFullDataW1071`
- `unitStrictExactIsoDataOfUnitStrictExactIsoDataOfCurrentFullDataW1071`
- `componentFieldsOfComponentFieldsOfCurrentFullDataW1071`
- `currentFullDataProviderOfCurrentFullDataOfCurrentFullDataW1071`
- `branchFullDataProviderOfBranchFullDataOfBranchFullDataOfCurrentFullDataW1071`
- `localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfCurrentFullDataW1071`
- `componentFieldsOfComponentFieldsOfComponentFieldsOfCurrentFullDataW1071`
- `currentFullDataOfCurrentFullDataW1071`
- `branchFullDataOfCurrentFullDataW1071`
- `targetSurjectiveCompactDataOfCurrentFullDataW1071`
- `fullDataOfCurrentFullDataW1071`
- `directBoundedLeftCalculusOfCurrentFullDataW1071`
- `boundedDerivedInfinityCategoryOfCurrentFullDataW1071`
- `currentFullDataInputNamesW1071_count`

## Nonterminal Status

Product success remains false. W1071 replaces W1070's one W1016 branch-full-data assumption by the one W1017 current-full-data input, but that input remains an explicit assumption and the original four-task completion witness and review packet are still missing.
