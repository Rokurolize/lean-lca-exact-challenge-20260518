# W972 provider search ledger

Baseline: W971 is the current clean boundary/relation-data route. It verifies a nonterminal route with 18 explicit inputs, including two split target primitives for target-difference surjectivity and target-codomain compact no-univ membership.

Decision: W972 uses `TargetSurjectiveNoUnivMembershipForTargetProviderW944` to replace the two W971 split target primitive fields with one target no-univ data provider. The route projects W944 back to the target-difference and target-codomain no-univ primitives, then delegates through W971.

Rejected alternatives:

| Candidate | Effect | Reason deferred |
| --- | --- | --- |
| W947 target/closedness data | Bundle target no-univ data with closedness branch data | W972 targets only the split target primitive pair; adding closedness would also need a closed-embedding-specific branch alignment. |
| W725 closedness branch data | Bundle W718 and W519 closedness fields | Useful next step, but independent of target primitive bundling. |
| W945 localized-unit data | Bundle right adjoint, adjunction, and unit strictness | W972 does not yet target the bounded-homotopy/unit mapping-cone surface. |

Result: selected for W972. Explicit input names drop from 18 to 17. Product success remains false because the W972 field surface still consists of explicit assumptions and does not construct the original four-task completion witness.
