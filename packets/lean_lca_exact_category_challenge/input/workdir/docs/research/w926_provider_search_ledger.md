# W926 Provider Search Ledger

W926 extends the W925 closed-map target-compact-filter-primitive-field route by replacing the `ClusterPt x f` portion of the target-codomain compactness provider with the mathlib definition `Filter.NeBot (𝓝 x ⊓ f)`.

The route leaves the outer `Filter.NeBot` and `Filter.principal` quantifier from W925 unchanged, and only removes the `ClusterPt` abbreviation from the selected witness in the compactness input.

This is still nonterminal for the original four-task contract: W926 preserves the stable W925 ExactAt route output, keeps `productSuccessClaimed = false`, and records 39 explicit input names with one input refined from the target-codomain compactness filter-cluster condition to neighborhood-filter meet nontriviality.
