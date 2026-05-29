# W1277 provider search ledger

Baseline: W1276 showed that directly splitting W716/W717/W984/W950 exposes eight inputs, while the current W907/W908 branch field splits have 31/32 inputs. The remaining checked surface is still the W1270 one-input W987 provider.

Decision: W1277 records why the older W952 one-provider route is not a discharge of the current W987 surface. W952 also has one full-provider input, so switching to it does not reduce the one remaining provider. More importantly, W952 routes target closedness through W951/W947, and W947 packages W944 with W725 closed-map-or-closed-embedding closedness data. The current W987 route intentionally keeps the W984/W973 closed-embedding-specific provider surface.

Checked Lean facts:

- `oldClosednessFullProviderInputNamesW1277_count`: the older W952 full-provider surface has 1 input.
- `oldClosednessFullProviderDoesNotReduceW1277`: the W952 full-provider input count equals the current W1270 one-input W987 surface.
- `oldTargetClosednessRouteInputNamesW1277_count`: the W947 older target/closedness route has 6 inputs.
- `branchSpecificTargetClosednessInputNamesW1277_count`: the W984 branch-specific target/closed-embedding closedness surface has 2 inputs.
- `oldTargetClosednessRouteExpandsBranchSpecificSurfaceW1277`: the older W947/W725 route is larger than the W984/W973 branch-specific target-closedness surface.

Result: selected as a nonterminal provider-search guard. W1277 does not claim product success; the remaining W987 provider is still explicit.
