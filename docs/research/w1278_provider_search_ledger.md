# W1278 provider search ledger

Baseline: W1277 ruled out the older W952/W947/W725 closedness route as a reduction of the current one-input W987 surface.

Decision: W1278 records two remaining base-route candidates around W987. W998 derives target-surjective-compact data from an existing W987 provider and feeds W997, but its checked ledger is still one W987 input. W997 is also a one-provider wrapper that contains W715 target-surjective-compact data plus W987 branch full data. W990 is a genuine primitive-unit-components constructor for W987, but its checked ledger has eight inputs.

Checked Lean facts:

- `branchWrapperInputNamesW1278_count`: the W998 branch-full-data wrapper surface has 1 input.
- `branchWrapperDoesNotReduceW1278`: W998 has the same input count as the current W1270 one-input W987 surface.
- `targetSurjectiveCompactBranchWrapperInputNamesW1278_count`: the W997 target-surjective-compact branch wrapper surface has 1 input.
- `targetSurjectiveCompactBranchWrapperDoesNotReduceW1278`: W997 has the same input count as the current W1270 one-input W987 surface.
- `primitiveUnitComponentsInputNamesW1278_count`: the W990 primitive-unit-components route has 8 inputs.
- `primitiveUnitComponentsRouteDoesNotReduceW1278`: W990 expands beyond the current W1270 one-input W987 surface.

Result: selected as a nonterminal provider-search guard. W1278 does not claim product success; the remaining W987 provider is still explicit.
