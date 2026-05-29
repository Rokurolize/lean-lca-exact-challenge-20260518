# W1275 provider search ledger

Baseline: W1274 opened the remaining W987 provider through W730 and W986 to W716/W717/W984/W950 atom candidates, but that already expands the one-input W987 surface to four lower-level inputs.

Decision: W1275 records the checked route sizes for those atom candidates. W716 has a 22-input boundary-data route, W717 has a 21-input relation-data route, W984 has a 2-input target/closed-embedding-closedness route, and W950 has a 3-input normalized-source/endpoint-localized-unit route. Each is larger than the W1270 one-input W987 surface.

Checked Lean facts:

- `boundaryDataRouteCandidateInputNamesW1275_count`: W716 route has 22 inputs.
- `relationDataRouteCandidateInputNamesW1275_count`: W717 route has 21 inputs.
- `targetClosednessAtomRouteCandidateInputNamesW1275_count`: W984 route has 2 inputs.
- `normalizedEndpointAtomRouteCandidateInputNamesW1275_count`: W950 route has 3 inputs.
- `atomRouteCandidatesDoNotReduceW1275`: all four route counts are strictly larger than the W1270 one-input W987 surface.

Result: selected as a nonterminal provider-search guard. W1275 does not claim product success; the remaining W987 provider is still explicit.
