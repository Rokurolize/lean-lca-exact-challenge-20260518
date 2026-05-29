# W1272 provider search ledger

Baseline: W1270 reduced the current full-data payload bridge to one explicit W987 branch-specific full-data provider, and W1271 ruled out the W999 W977-to-W987 route as a one-input cycle.

Decision: W1272 inspects the remaining tempting W987-producing routes. `branchFullDataOfBranchFullDataW1205` still takes W1007 branch-full-data data, and W1007 is a wrapper around the same W987 provider. W1205 therefore has one input but does not reduce the W1270 one-input surface. The nearby W1167, W1164, and W1091 routes construct W987 only by expanding to three, six, and seven explicit inputs.

Checked Lean facts:

- `branchFullDataRouteCandidateInputNamesW1272_count`: W1205 candidate input count is 1.
- `branchFullDataRouteCandidateDoesNotReduceW1272`: W1205 candidate input count equals the W1270 remaining W987 input count.
- `targetClosedEmbeddingClosednessCandidateInputNamesW1272_count`: W1167 expands to 3 inputs.
- `localizedUnitChoiceCandidateInputNamesW1272_count`: W1164 expands to 6 inputs.
- `unitStrictExactIsoCandidateInputNamesW1272_count`: W1091 expands to 7 inputs.

Result: selected as a nonterminal provider-search guard. W1272 does not claim product success; it records that the best one-input branch-full-data candidate is another W987 wrapper and that the adjacent W987-producing alternatives expand the assumption surface.
