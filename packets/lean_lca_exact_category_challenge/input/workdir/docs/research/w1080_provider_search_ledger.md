# W1080 Provider Search Ledger

## Scope

W1080 targets W1079's W1016 branch-full-data input surface. The existing W1017 current-full-data route already constructs the W1007 branch-full-data provider accepted by W1079 via `branchFullDataProviderOfCurrentFullDataW1017`, so W1080 repackages one W1008 current-full-data provider and feeds W1079.

## Candidate Providers

- `branchFullDataInputNamesW1079`: rejected as the latest input ledger because it still exposes one W1016 branch-full-data input.
- `branchFullDataProviderOfCurrentFullDataW1017`: chosen because W1017 already constructs the W1007 provider consumed by W1079.
- `currentFullDataInputNamesW1017`: accepted as the next input ledger because it records the one W1017 current-full-data provider input that remains explicit after W1017.

## Remaining W1080 Inputs

- 1 W1017 current-full-data provider input

The count is checked by `currentFullDataInputNamesW1080_count`.

## Checked W1080 Surface

- `branchFullDataProviderOfCurrentFullDataW1080`
- `targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1080`
- `targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1080`
- `normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1080`
- `endpointLocalizedUnitDataProviderOfCurrentFullDataW1080`
- `localizedUnitChoiceDataOfCurrentFullDataW1080`
- `unitStrictExactIsoDataOfCurrentFullDataW1080`
- `componentFieldsOfCurrentFullDataW1080`
- `currentFullDataProviderOfCurrentFullDataW1080`
- `branchFullDataProviderOfBranchFullDataOfCurrentFullDataW1080`
- `targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfCurrentFullDataW1080`
- `targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfCurrentFullDataW1080`
- `normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfCurrentFullDataW1080`
- `endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfCurrentFullDataW1080`
- `localizedUnitChoiceDataOfLocalizedUnitChoiceOfCurrentFullDataW1080`
- `unitStrictExactIsoDataOfUnitStrictExactIsoDataOfCurrentFullDataW1080`
- `componentFieldsOfComponentFieldsOfCurrentFullDataW1080`
- `currentFullDataProviderOfCurrentFullDataOfCurrentFullDataW1080`
- `branchFullDataProviderOfBranchFullDataOfBranchFullDataOfCurrentFullDataW1080`
- `localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfCurrentFullDataW1080`
- `componentFieldsOfComponentFieldsOfComponentFieldsOfCurrentFullDataW1080`
- `currentFullDataOfCurrentFullDataW1080`
- `branchFullDataOfCurrentFullDataW1080`
- `targetSurjectiveCompactDataOfCurrentFullDataW1080`
- `fullDataOfCurrentFullDataW1080`
- `directBoundedLeftCalculusOfCurrentFullDataW1080`
- `boundedDerivedInfinityCategoryOfCurrentFullDataW1080`
- `currentFullDataInputNamesW1080_count`

## Nonterminal Status

Product success remains false. W1080 replaces W1079's one W1016 branch-full-data assumption by the one W1017 current-full-data input, but that input remains an explicit assumption and the original four-task completion witness and review packet are still missing.
